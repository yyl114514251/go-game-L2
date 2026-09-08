/* ============================================================
 * 棋道 · 围棋 AI Worker  v2.0 (L2)
 * MCTS + RAVE + 静态评估 + 启发式模拟 + 树复用
 * 运行在独立 Web Worker 线程
 * ============================================================ */

const EMPTY = 0, BLACK = 1, WHITE = 2;
const UCT_C = 1.414;
const K_RAVE = 2500;       // RAVE 常数（棋盘越大越大）
const MAX_ROLLOUT_DEPTH = 80;  // 模拟最大步数（超过则用评估函数）
const EARLY_EVAL_THRESHOLD = 0.35; // 棋盘占用率超过此值则提前评估

let SIZE = 19;
let NEIGHBORS = [];

// 预计算邻接表
function precomputeNeighbors(size) {
  SIZE = size;
  NEIGHBORS = new Array(size * size);
  for (let i = 0; i < size * size; i++) {
    const r = Math.floor(i / size), c = i % size;
    const n = [];
    if (r > 0) n.push(i - size);
    if (r < size - 1) n.push(i + size);
    if (c > 0) n.push(i - 1);
    if (c < size - 1) n.push(i + 1);
    NEIGHBORS[i] = n;
  }
}

// ---------- 围棋规则 ----------

function getGroup(board, pos) {
  const color = board[pos];
  const visited = new Int8Array(board.length);
  const stones = [];
  let liberties = 0;
  const libSet = new Set();
  const stack = [pos];
  visited[pos] = 1;
  while (stack.length) {
    const p = stack.pop();
    stones.push(p);
    for (const n of NEIGHBORS[p]) {
      if (board[n] === EMPTY) {
        if (!libSet.has(n)) { libSet.add(n); liberties++; }
      } else if (board[n] === color && !visited[n]) {
        visited[n] = 1;
        stack.push(n);
      }
    }
  }
  return { liberties, stones };
}

function checkMove(board, pos, color, koPoint) {
  if (board[pos] !== EMPTY) return { legal: false };
  if (pos === koPoint) return { legal: false };

  const opponent = color === BLACK ? WHITE : BLACK;
  const newBoard = new Int8Array(board);
  newBoard[pos] = color;

  let captured = 0;
  let capturedSingle = -1;
  for (const n of NEIGHBORS[pos]) {
    if (newBoard[n] === opponent) {
      const { liberties, stones } = getGroup(newBoard, n);
      if (liberties === 0) {
        for (const s of stones) newBoard[s] = EMPTY;
        captured += stones.length;
        if (stones.length === 1) capturedSingle = stones[0];
      }
    }
  }

  const { liberties: selfLib } = getGroup(newBoard, pos);
  if (selfLib === 0 && captured === 0) return { legal: false };

  let ko = -1;
  if (captured === 1) {
    const { stones: selfStones } = getGroup(newBoard, pos);
    if (selfStones.length === 1) ko = capturedSingle;
  }

  return { legal: true, board: newBoard, captured, ko };
}

function generateMoves(board, color, koPoint) {
  const moves = [];
  for (let i = 0; i < board.length; i++) {
    if (board[i] !== EMPTY) continue;
    const result = checkMove(board, i, color, koPoint);
    if (result.legal) moves.push(i);
  }
  return moves;
}

function isOwnEye(board, pos, color) {
  for (const n of NEIGHBORS[pos]) {
    if (board[n] !== color) return false;
  }
  const r = Math.floor(pos / SIZE), c = pos % SIZE;
  let friendlyDiag = 0, totalDiag = 0;
  const diags = [[-1,-1],[-1,1],[1,-1],[1,1]];
  for (const [dr, dc] of diags) {
    const nr = r + dr, nc = c + dc;
    if (nr < 0 || nr >= SIZE || nc < 0 || nc >= SIZE) { friendlyDiag++; totalDiag++; continue; }
    totalDiag++;
    if (board[nr * SIZE + nc] === color) friendlyDiag++;
  }
  return friendlyDiag >= totalDiag - 1;
}

// 启发式落子评分
function scoreMove(board, pos, color) {
  let score = 0;
  const opponent = color === BLACK ? WHITE : BLACK;

  for (const n of NEIGHBORS[pos]) {
    if (board[n] === opponent) score += 4;
    else if (board[n] === color) score += 1.5;
  }

  // 提子潜力：检查邻接对方棋块是否只剩1气
  for (const n of NEIGHBORS[pos]) {
    if (board[n] === opponent) {
      const { liberties } = getGroup(board, n);
      if (liberties === 1) score += 8;
    }
  }

  // 自己的棋块只剩1气时，优先连接/长气
  for (const n of NEIGHBORS[pos]) {
    if (board[n] === color) {
      const { liberties } = getGroup(board, n);
      if (liberties === 1) score += 6;
    }
  }

  let nearStone = false;
  for (const n of NEIGHBORS[pos]) {
    if (board[n] !== EMPTY) { nearStone = true; break; }
  }
  if (!nearStone) score -= 3;

  if (isOwnEye(board, pos, color)) score -= 25;

  const r = Math.floor(pos / SIZE), c = pos % SIZE;
  const centerDist = Math.abs(r - SIZE/2) + Math.abs(c - SIZE/2);
  score += Math.max(0, 4 - centerDist * 0.2);

  // 边角价值（开局时边角更重要）
  if (r < 3 || r >= SIZE - 3 || c < 3 || c >= SIZE - 3) score += 1;

  return score;
}

// ---------- 静态评估函数（L2核心改进） ----------
// 快速评估局面，返回从 player 视角的胜率 (0~1)
function evaluateBoard(board, player) {
  let blackStones = 0, whiteStones = 0;
  let blackTerritory = 0, whiteTerritory = 0;
  let blackLiberties = 0, whiteLiberties = 0;
  const visited = new Int8Array(board.length);

  for (let i = 0; i < board.length; i++) {
    if (board[i] === BLACK) {
      blackStones++;
      const { liberties } = getGroup(board, i);
      blackLiberties += liberties;
    } else if (board[i] === WHITE) {
      whiteStones++;
      const { liberties } = getGroup(board, i);
      whiteLiberties += liberties;
    } else if (!visited[i]) {
      // 空点连通块
      const group = [];
      const bordering = new Set();
      const stack = [i];
      visited[i] = 1;
      while (stack.length) {
        const p = stack.pop();
        group.push(p);
        for (const n of NEIGHBORS[p]) {
          if (board[n] === EMPTY && !visited[n]) {
            visited[n] = 1;
            stack.push(n);
          } else if (board[n] !== EMPTY) {
            bordering.add(board[n]);
          }
        }
      }
      if (bordering.size === 1) {
        if (bordering.has(BLACK)) blackTerritory += group.length;
        else whiteTerritory += group.length;
      }
    }
  }

  const komi = 7.5;
  const blackTotal = blackStones + blackTerritory * 0.8 + blackLiberties * 0.05;
  const whiteTotal = whiteStones + whiteTerritory * 0.8 + whiteLiberties * 0.05 + komi;

  const diff = player === BLACK ? (blackTotal - whiteTotal) : (whiteTotal - blackTotal);
  // sigmoid 转换为胜率
  return 1 / (1 + Math.exp(-diff * 0.15));
}

// 数子法终局计分
function scoreGame(board, player) {
  let blackArea = 0, whiteArea = 0;
  const visited = new Int8Array(board.length);

  for (let i = 0; i < board.length; i++) {
    if (board[i] === BLACK) blackArea++;
    else if (board[i] === WHITE) whiteArea++;
    else if (!visited[i]) {
      const group = [];
      const bordering = new Set();
      const stack = [i];
      visited[i] = 1;
      while (stack.length) {
        const p = stack.pop();
        group.push(p);
        for (const n of NEIGHBORS[p]) {
          if (board[n] === EMPTY && !visited[n]) {
            visited[n] = 1;
            stack.push(n);
          } else if (board[n] !== EMPTY) {
            bordering.add(board[n]);
          }
        }
      }
      if (bordering.size === 1) {
        if (bordering.has(BLACK)) blackArea += group.length;
        else whiteArea += group.length;
      }
    }
  }

  const komi = 7.5;
  const blackScore = blackArea;
  const whiteScore = whiteArea + komi;

  if (player === BLACK) {
    if (blackScore > whiteScore) return 1;
    if (blackScore < whiteScore) return 0;
    return 0.5;
  } else {
    if (whiteScore > blackScore) return 1;
    if (whiteScore < blackScore) return 0;
    return 0.5;
  }
}

// ---------- MCTS 节点（含 RAVE） ----------
class Node {
  constructor(board, player, koPoint, parent = null, move = -1) {
    this.board = board;
    this.player = player;
    this.koPoint = koPoint;
    this.parent = parent;
    this.move = move;
    this.children = [];
    this.visits = 0;
    this.wins = 0;
    this.untriedMoves = null;
    // RAVE 统计
    this.amafVisits = new Int32Array(board.length);
    this.amafWins = new Float32Array(board.length);
  }

  getUntriedMoves() {
    if (this.untriedMoves === null) {
      this.untriedMoves = generateMoves(this.board, this.player, this.koPoint);
    }
    return this.untriedMoves;
  }

  isFullyExpanded() {
    return this.getUntriedMoves().length === 0;
  }
}

// UCT-RAVE 选择最优子节点（L2核心改进）
function bestChildRAVE(node) {
  let best = null;
  let bestScore = -Infinity;
  const logN = Math.log(Math.max(1, node.visits));

  for (const child of node.children) {
    if (child.visits === 0) return child;

    // MCTS 价值
    const q = child.wins / child.visits;

    // RAVE 价值
    const move = child.move;
    const amafV = node.amafVisits[move];
    const q_rave = amafV > 0 ? node.amafWins[move] / amafV : 0;

    // beta: RAVE 权重，随访问次数增加而降低
    const beta = amafV > 0 ? Math.sqrt(K_RAVE / (3 * node.visits + K_RAVE)) : 0;
    const combinedQ = (1 - beta) * q + beta * q_rave;

    // UCT 探索项
    const explore = UCT_C * Math.sqrt(logN / child.visits);
    const score = combinedQ + explore;

    if (score > bestScore) {
      bestScore = score;
      best = child;
    }
  }
  return best;
}

// 扩展（启发式选择最优未尝试落子）
function expand(node) {
  const untried = node.getUntriedMoves();
  if (untried.length === 0) return node;

  let bestMove = untried[0];
  let bestScore = -Infinity;
  for (const m of untried) {
    const s = scoreMove(node.board, m, node.player);
    if (s > bestScore) { bestScore = s; bestMove = m; }
  }

  const result = checkMove(node.board, bestMove, node.player, node.koPoint);
  const child = new Node(
    result.board,
    node.player === BLACK ? WHITE : BLACK,
    result.ko,
    node,
    bestMove
  );
  node.children.push(child);
  node.untriedMoves = untried.filter(m => m !== bestMove);
  return child;
}

// 模拟（rollout）—— 启发式落子 + 提前评估（L2核心改进）
function rollout(board, player, koPoint) {
  let currentBoard = new Int8Array(board);
  let currentPlayer = player;
  let currentKo = koPoint;
  let passes = 0;
  const moveSequence = [];  // 记录模拟中的落子，用于 RAVE

  for (let step = 0; step < MAX_ROLLOUT_DEPTH; step++) {
    // 提前评估：棋盘占用率超过阈值时直接用评估函数
    let occupied = 0;
    for (let i = 0; i < currentBoard.length; i++) {
      if (currentBoard[i] !== EMPTY) occupied++;
    }
    if (occupied / currentBoard.length > EARLY_EVAL_THRESHOLD && step > 20) {
      const winRate = evaluateBoard(currentBoard, player);
      return { result: winRate, moves: moveSequence };
    }

    const moves = generateMoves(currentBoard, currentPlayer, currentKo);
    if (moves.length === 0) {
      passes++;
      moveSequence.push({ move: -1, player: currentPlayer });
      if (passes >= 2) break;
      currentPlayer = currentPlayer === BLACK ? WHITE : BLACK;
      currentKo = -1;
      continue;
    }
    passes = 0;

    // 启发式加权随机：80% 选前50%好棋，20% 完全随机
    const scored = moves.map(m => ({
      move: m,
      score: Math.max(1, scoreMove(currentBoard, m, currentPlayer) + 12)
    }));

    let chosen;
    if (Math.random() < 0.8) {
      scored.sort((a, b) => b.score - a.score);
      const topCount = Math.max(1, Math.ceil(scored.length * 0.5));
      const top = scored.slice(0, topCount);
      const totalWeight = top.reduce((s, x) => s + x.score, 0);
      let r = Math.random() * totalWeight;
      chosen = top[0].move;
      for (const item of top) {
        r -= item.score;
        if (r <= 0) { chosen = item.move; break; }
      }
    } else {
      chosen = moves[Math.floor(Math.random() * moves.length)];
    }

    moveSequence.push({ move: chosen, player: currentPlayer });
    const result = checkMove(currentBoard, chosen, currentPlayer, currentKo);
    currentBoard = result.board;
    currentKo = result.ko;
    currentPlayer = currentPlayer === BLACK ? WHITE : BLACK;
  }

  // 终局数子
  const result = scoreGame(currentBoard, player);
  return { result, moves: moveSequence };
}

// 回溯（含 RAVE 更新，L2核心改进）
function backpropagate(node, result, moveSequence, startPlayer) {
  let current = node;
  while (current !== null) {
    current.visits++;
    // 从当前节点玩家视角的胜负
    const resultFromPerspective = (current.player === startPlayer) ? result : (1 - result);
    current.wins += resultFromPerspective;

    // RAVE 更新：统计模拟中当前玩家下的所有落子
    for (const { move, player } of moveSequence) {
      if (move === -1) continue;
      if (player === current.player) {
        current.amafVisits[move]++;
        current.amafWins[move] += resultFromPerspective;
      }
    }

    current = current.parent;
  }
}

// ---------- 树复用（L2核心改进） ----------
let persistentRoot = null;

function boardsEqual(a, b) {
  for (let i = 0; i < a.length; i++) {
    if (a[i] !== b[i]) return false;
  }
  return true;
}

// 尝试复用已有搜索树
function reuseTree(board) {
  if (!persistentRoot) return null;

  // 时序：持久根 = AI上一次思考时的局面（玩家刚下完）
  // 持久根的子节点 = AI的落子
  // AI落子的子节点 = 玩家的应对落子
  // 当前局面应该匹配某个"玩家应对落子"节点
  for (const aiChild of persistentRoot.children) {
    for (const playerChild of aiChild.children) {
      if (boardsEqual(playerChild.board, board)) {
        // 提升为新根
        playerChild.parent = null;
        return playerChild;
      }
    }
  }

  // 如果玩家直接 pass 或下了 AI 没扩展的棋，尝试匹配 AI 子节点本身
  for (const aiChild of persistentRoot.children) {
    if (boardsEqual(aiChild.board, board)) {
      aiChild.parent = null;
      return aiChild;
    }
  }

  return null;
}

// ---------- MCTS 主循环 ----------
function mcts(board, player, koPoint, simulations) {
  // 尝试树复用
  let root = reuseTree(board);
  let reused = false;
  if (!root) {
    root = new Node(new Int8Array(board), player, koPoint);
  } else {
    reused = true;
    // 确保根节点的 player 和 koPoint 正确
    root.player = player;
    root.koPoint = koPoint;
  }

  if (generateMoves(board, player, koPoint).length === 0) {
    persistentRoot = root;
    return -1;
  }

  // 空棋盘第一手下中心
  let hasStone = false;
  for (let i = 0; i < board.length; i++) {
    if (board[i] !== EMPTY) { hasStone = true; break; }
  }
  if (!hasStone) {
    const center = Math.floor(SIZE / 2) * SIZE + Math.floor(SIZE / 2);
    persistentRoot = root;
    return center;
  }

  const progressInterval = Math.max(100, Math.floor(simulations / 20));

  for (let i = 0; i < simulations; i++) {
    // 1. Selection (UCT-RAVE)
    let node = root;
    while (node.isFullyExpanded() && node.children.length > 0) {
      node = bestChildRAVE(node);
    }

    // 2. Expansion
    if (node.getUntriedMoves().length > 0) {
      node = expand(node);
    }

    // 3. Simulation (启发式 + 提前评估)
    const { result, moves } = rollout(node.board, node.player, node.koPoint);

    // 4. Backpropagation (含 RAVE)
    backpropagate(node, result, moves, node.player);

    if ((i + 1) % progressInterval === 0) {
      self.postMessage({ type: "progress", simulations: i + 1, reused });
    }
  }

  // 选择访问次数最多的子节点
  let best = null;
  let bestVisits = -1;
  for (const child of root.children) {
    if (child.visits > bestVisits) {
      bestVisits = child.visits;
      best = child;
    }
  }

  persistentRoot = root;
  return best ? best.move : -1;
}

// ---------- Worker 消息处理 ----------
self.onmessage = (e) => {
  const msg = e.data;
  if (msg.type === "think") {
    precomputeNeighbors(msg.size);
    const board = new Int8Array(msg.board);
    const move = mcts(board, msg.player, msg.koPoint, msg.simulations);
    self.postMessage({ type: "result", move });
  } else if (msg.type === "reset") {
    persistentRoot = null;
  }
};
