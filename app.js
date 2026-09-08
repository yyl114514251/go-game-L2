/* ============================================================
 * 棋道 · 围棋 AI  主逻辑
 * 棋盘渲染 + 围棋规则 + Web Worker通信 + UI交互
 * ============================================================ */

(() => {
  "use strict";

  const $ = (id) => document.getElementById(id);

  // ---------- 游戏状态 ----------
  const state = {
    size: 19,
    board: null,          // Int8Array, 0=空 1=黑 2=白
    currentPlayer: 1,     // 1=黑 2=白
    playerColor: 1,       // 玩家执子
    captures: { 1: 0, 2: 0 },
    history: [],          // 落子历史 [{pos, player, captured, koPoint}]
    koPoint: -1,          // 打劫禁入点
    lastMove: -1,
    consecutivePasses: 0,
    gameOver: false,
    aiThinking: false,
    aiSimulations: 2000,
    worker: null,
    cellSize: 0,
    padding: 0,
  };

  const EMPTY = 0, BLACK = 1, WHITE = 2;
  const KOMI = 7.5;

  // ---------- 邻接表预计算 ----------
  function getNeighbors(pos, size) {
    const r = Math.floor(pos / size), c = pos % size;
    const n = [];
    if (r > 0) n.push(pos - size);
    if (r < size - 1) n.push(pos + size);
    if (c > 0) n.push(pos - 1);
    if (c < size - 1) n.push(pos + 1);
    return n;
  }

  // ---------- 围棋规则 ----------
  // 计算一个连通块的气
  function getGroupLiberties(board, pos, size) {
    const color = board[pos];
    if (color === EMPTY) return { liberties: new Set(), stones: [] };
    const visited = new Set();
    const liberties = new Set();
    const stones = [];
    const stack = [pos];
    while (stack.length) {
      const p = stack.pop();
      if (visited.has(p)) continue;
      visited.add(p);
      stones.push(p);
      for (const n of getNeighbors(p, size)) {
        if (board[n] === EMPTY) liberties.add(n);
        else if (board[n] === color && !visited.has(n)) stack.push(n);
      }
    }
    return { liberties, stones };
  }

  // 尝试落子，返回 {ok, captured, koPoint}
  function tryPlace(board, pos, color, size, koPoint) {
    if (board[pos] !== EMPTY) return { ok: false };
    if (pos === koPoint) return { ok: false, reason: "ko" };

    const opponent = color === BLACK ? WHITE : BLACK;
    const newBoard = new Int8Array(board);
    newBoard[pos] = color;

    // 检查是否提掉对方的子
    let captured = [];
    for (const n of getNeighbors(pos, size)) {
      if (newBoard[n] === opponent) {
        const { liberties, stones } = getGroupLiberties(newBoard, n, size);
        if (liberties.size === 0) {
          for (const s of stones) {
            newBoard[s] = EMPTY;
            captured.push(s);
          }
        }
      }
    }

    // 检查自杀（落子后自己没气且没提子）
    const { liberties: selfLib } = getGroupLiberties(newBoard, pos, size);
    if (selfLib.size === 0 && captured.length === 0) {
      return { ok: false, reason: "suicide" };
    }

    // 打劫判断：只提了一个子且自己也只有一个子（简单劫）
    let newKoPoint = -1;
    if (captured.length === 1) {
      const { stones: selfStones } = getGroupLiberties(newBoard, pos, size);
      if (selfStones.length === 1) {
        newKoPoint = captured[0];
      }
    }

    return { ok: true, board: newBoard, captured, koPoint: newKoPoint };
  }

  // 落子
  function placeStone(pos) {
    if (state.gameOver || state.aiThinking) return false;
    if (state.currentPlayer !== state.playerColor) return false;

    const result = tryPlace(state.board, pos, state.currentPlayer, state.size, state.koPoint);
    if (!result.ok) return false;

    state.history.push({
      pos,
      player: state.currentPlayer,
      board: new Int8Array(state.board),
      captures: { ...state.captures },
      koPoint: state.koPoint,
      lastMove: state.lastMove,
      consecutivePasses: state.consecutivePasses,
    });

    state.board = result.board;
    state.captures[state.currentPlayer] += result.captured.length;
    state.koPoint = result.koPoint;
    state.lastMove = pos;
    state.consecutivePasses = 0;
    state.currentPlayer = state.currentPlayer === BLACK ? WHITE : BLACK;

    render();
    updateInfo();

    // 如果轮到AI，触发AI思考
    if (state.currentPlayer !== state.playerColor && !state.gameOver) {
      setTimeout(aiMove, 300);
    }
    return true;
  }

  // Pass
  function pass() {
    if (state.gameOver || state.aiThinking) return;
    if (state.currentPlayer !== state.playerColor) return;

    state.history.push({
      pos: -1,
      player: state.currentPlayer,
      board: new Int8Array(state.board),
      captures: { ...state.captures },
      koPoint: state.koPoint,
      lastMove: state.lastMove,
      consecutivePasses: state.consecutivePasses,
    });

    state.consecutivePasses++;
    state.koPoint = -1;
    state.lastMove = -1;
    state.currentPlayer = state.currentPlayer === BLACK ? WHITE : BLACK;

    updateInfo();

    if (state.consecutivePasses >= 2) {
      endGame();
      return;
    }

    if (state.currentPlayer !== state.playerColor && !state.gameOver) {
      setTimeout(aiMove, 300);
    }
  }

  // 悔棋
  function undo() {
    if (state.aiThinking || state.history.length === 0) return;
    // 悔两步（玩家+AI），如果最后一步是玩家的则只悔一步
    let steps = 1;
    if (state.history.length >= 2 && state.history[state.history.length - 1].player !== state.playerColor) {
      steps = 2;
    }
    for (let i = 0; i < steps && state.history.length > 0; i++) {
      const prev = state.history.pop();
      state.board = prev.board;
      state.captures = prev.captures;
      state.koPoint = prev.koPoint;
      state.lastMove = prev.lastMove;
      state.consecutivePasses = prev.consecutivePasses;
      state.currentPlayer = prev.player;
    }
    state.gameOver = false;
    render();
    updateInfo();
  }

  // 认输
  function resign() {
    if (state.gameOver) return;
    state.gameOver = true;
    const winner = state.currentPlayer === BLACK ? WHITE : BLACK;
    showResult(winner, "认输");
  }

  // 终局计算（中国数子法）
  function endGame() {
    state.gameOver = true;
    const { blackScore, whiteScore, blackTerritory, whiteTerritory } = calculateScore();
    const blackTotal = blackScore;
    const whiteTotal = whiteScore + KOMI;
    const winner = blackTotal > whiteTotal ? BLACK : WHITE;
    const margin = Math.abs(blackTotal - whiteTotal);
    showResult(winner, "数目", { blackTotal, whiteTotal, blackTerritory, whiteTerritory, margin });
  }

  function calculateScore() {
    const size = state.size;
    const board = state.board;
    let blackStones = 0, whiteStones = 0;
    for (let i = 0; i < board.length; i++) {
      if (board[i] === BLACK) blackStones++;
      else if (board[i] === WHITE) whiteStones++;
    }

    // 计算领地：空点的连通块，如果只被一种颜色包围则属于该颜色
    const visited = new Set();
    let blackTerritory = 0, whiteTerritory = 0;
    for (let i = 0; i < board.length; i++) {
      if (board[i] !== EMPTY || visited.has(i)) continue;
      // BFS找空点连通块
      const emptyGroup = [];
      const borderingColors = new Set();
      const stack = [i];
      while (stack.length) {
        const p = stack.pop();
        if (visited.has(p)) continue;
        visited.add(p);
        emptyGroup.push(p);
        for (const n of getNeighbors(p, size)) {
          if (board[n] === EMPTY && !visited.has(n)) stack.push(n);
          else if (board[n] !== EMPTY) borderingColors.add(board[n]);
        }
      }
      if (borderingColors.size === 1) {
        if (borderingColors.has(BLACK)) blackTerritory += emptyGroup.length;
        else if (borderingColors.has(WHITE)) whiteTerritory += emptyGroup.length;
      }
    }

    return {
      blackScore: blackStones + blackTerritory,
      whiteScore: whiteStones + whiteTerritory,
      blackStones, whiteStones, blackTerritory, whiteTerritory,
    };
  }

  // ---------- AI (Web Worker) ----------
  function initWorker() {
    if (state.worker) state.worker.terminate();
    state.worker = new Worker("ai-worker.js");
    state.worker.onmessage = (e) => {
      const msg = e.data;
      if (msg.type === "progress") {
        const reuseText = msg.reused ? " · 树复用" : "";
        $("thinkingStat").textContent = `模拟 ${msg.simulations} 次${reuseText}`;
      } else if (msg.type === "result") {
        state.aiThinking = false;
        $("thinkingOverlay").style.display = "none";
        if (msg.move === -1) {
          // AI pass
          aiPass();
        } else {
          aiPlaceStone(msg.move);
        }
      }
    };
  }

  function aiMove() {
    if (state.gameOver) return;
    state.aiThinking = true;
    $("thinkingOverlay").style.display = "flex";
    $("thinkingStat").textContent = "模拟 0 次";

    state.worker.postMessage({
      type: "think",
      board: Array.from(state.board),
      size: state.size,
      player: state.currentPlayer,
      koPoint: state.koPoint,
      simulations: state.aiSimulations,
    });
  }

  function aiPlaceStone(pos) {
    const result = tryPlace(state.board, pos, state.currentPlayer, state.size, state.koPoint);
    if (!result.ok) {
      // AI落子失败，pass
      aiPass();
      return;
    }

    state.history.push({
      pos,
      player: state.currentPlayer,
      board: new Int8Array(state.board),
      captures: { ...state.captures },
      koPoint: state.koPoint,
      lastMove: state.lastMove,
      consecutivePasses: state.consecutivePasses,
    });

    state.board = result.board;
    state.captures[state.currentPlayer] += result.captured.length;
    state.koPoint = result.koPoint;
    state.lastMove = pos;
    state.consecutivePasses = 0;
    state.currentPlayer = state.currentPlayer === BLACK ? WHITE : BLACK;

    render();
    updateInfo();
  }

  function aiPass() {
    state.history.push({
      pos: -1,
      player: state.currentPlayer,
      board: new Int8Array(state.board),
      captures: { ...state.captures },
      koPoint: state.koPoint,
      lastMove: state.lastMove,
      consecutivePasses: state.consecutivePasses,
    });

    state.consecutivePasses++;
    state.koPoint = -1;
    state.lastMove = -1;
    state.currentPlayer = state.currentPlayer === BLACK ? WHITE : BLACK;

    updateInfo();

    if (state.consecutivePasses >= 2) {
      endGame();
    }
  }

  // ---------- 棋盘渲染 ----------
  const canvas = $("boardCanvas");
  const ctx = canvas.getContext("2d");

  function resizeCanvas() {
    const maxWidth = Math.min(window.innerWidth - 400, 700);
    const displaySize = Math.max(300, Math.min(maxWidth, 680));
    const dpr = window.devicePixelRatio || 1;
    state.cellSize = displaySize / (state.size + 1);
    state.padding = state.cellSize;
    const totalSize = state.cellSize * (state.size + 1);

    canvas.style.width = totalSize + "px";
    canvas.style.height = totalSize + "px";
    canvas.width = totalSize * dpr;
    canvas.height = totalSize * dpr;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  }

  function render() {
    const size = state.size;
    const cs = state.cellSize;
    const pad = state.padding;
    const totalSize = cs * (size + 1);

    // 背景（木纹）
    ctx.clearRect(0, 0, totalSize, totalSize);

    // 网格线
    ctx.strokeStyle = "#3a2a10";
    ctx.lineWidth = 1;
    for (let i = 0; i < size; i++) {
      // 横线
      ctx.beginPath();
      ctx.moveTo(pad, pad + i * cs);
      ctx.lineTo(pad + (size - 1) * cs, pad + i * cs);
      ctx.stroke();
      // 竖线
      ctx.beginPath();
      ctx.moveTo(pad + i * cs, pad);
      ctx.lineTo(pad + i * cs, pad + (size - 1) * cs);
      ctx.stroke();
    }

    // 星位
    const starPoints = getStarPoints(size);
    ctx.fillStyle = "#3a2a10";
    for (const [r, c] of starPoints) {
      ctx.beginPath();
      ctx.arc(pad + c * cs, pad + r * cs, 3.5, 0, Math.PI * 2);
      ctx.fill();
    }

    // 坐标
    if ($("showCoords").checked) {
      ctx.fillStyle = "#5a4a20";
      ctx.font = `${Math.max(9, cs * 0.28)}px sans-serif`;
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      const letters = "ABCDEFGHJKLMNOPQRST";
      for (let i = 0; i < size; i++) {
        ctx.fillText(letters[i], pad + i * cs, pad / 2);
        ctx.fillText(letters[i], pad + i * cs, totalSize - pad / 2);
        ctx.fillText(String(size - i), pad / 2, pad + i * cs);
        ctx.fillText(String(size - i), totalSize - pad / 2, pad + i * cs);
      }
    }

    // 棋子
    for (let i = 0; i < state.board.length; i++) {
      if (state.board[i] === EMPTY) continue;
      const r = Math.floor(i / size), c = i % size;
      const x = pad + c * cs, y = pad + r * cs;
      drawStone(x, y, cs * 0.44, state.board[i]);
    }

    // 最后一手标记
    if (state.lastMove >= 0) {
      const r = Math.floor(state.lastMove / size), c = state.lastMove % size;
      const x = pad + c * cs, y = pad + r * cs;
      ctx.strokeStyle = state.board[state.lastMove] === BLACK ? "#fff" : "#000";
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.arc(x, y, cs * 0.18, 0, Math.PI * 2);
      ctx.stroke();
    }
  }

  function drawStone(x, y, radius, color) {
    // 阴影
    ctx.beginPath();
    ctx.arc(x + 1.5, y + 2, radius, 0, Math.PI * 2);
    ctx.fillStyle = "rgba(0,0,0,0.35)";
    ctx.fill();

    // 棋子主体
    const gradient = ctx.createRadialGradient(
      x - radius * 0.35, y - radius * 0.35, radius * 0.1,
      x, y, radius
    );
    if (color === BLACK) {
      gradient.addColorStop(0, "#666");
      gradient.addColorStop(0.4, "#333");
      gradient.addColorStop(1, "#000");
    } else {
      gradient.addColorStop(0, "#fff");
      gradient.addColorStop(0.6, "#f0f0f0");
      gradient.addColorStop(1, "#ccc");
    }
    ctx.beginPath();
    ctx.arc(x, y, radius, 0, Math.PI * 2);
    ctx.fillStyle = gradient;
    ctx.fill();

    // 高光
    ctx.beginPath();
    ctx.arc(x - radius * 0.3, y - radius * 0.3, radius * 0.25, 0, Math.PI * 2);
    ctx.fillStyle = color === BLACK ? "rgba(255,255,255,0.15)" : "rgba(255,255,255,0.6)";
    ctx.fill();
  }

  function getStarPoints(size) {
    if (size === 9) return [[2,2],[2,6],[4,4],[6,2],[6,6]];
    if (size === 13) return [[3,3],[3,9],[6,6],[9,3],[9,9]];
    return [[3,3],[3,9],[3,15],[9,3],[9,9],[9,15],[15,3],[15,9],[15,15]];
  }

  // 点击落子
  canvas.addEventListener("click", (e) => {
    if (state.gameOver || state.aiThinking) return;
    if (state.currentPlayer !== state.playerColor) return;

    const rect = canvas.getBoundingClientRect();
    const scaleX = canvas.width / rect.width / (window.devicePixelRatio || 1);
    const x = (e.clientX - rect.left) * scaleX;
    const y = (e.clientY - rect.top) * scaleX;

    const cs = state.cellSize;
    const pad = state.padding;
    const c = Math.round((x - pad) / cs);
    const r = Math.round((y - pad) / cs);

    if (r < 0 || r >= state.size || c < 0 || c >= state.size) return;

    // 检查点击是否在交叉点附近
    const px = pad + c * cs, py = pad + r * cs;
    if (Math.abs(x - px) > cs * 0.45 || Math.abs(y - py) > cs * 0.45) return;

    placeStone(r * state.size + c);
  });

  // ---------- UI 更新 ----------
  function updateInfo() {
    $("currentPlayer").textContent = state.currentPlayer === BLACK ? "⚫ 黑方" : "⚪ 白方";
    $("moveCount").textContent = state.history.length;
    $("blackCaptures").textContent = state.captures[BLACK];
    $("whiteCaptures").textContent = state.captures[WHITE];
  }

  function showResult(winner, method, details) {
    const winnerName = winner === BLACK ? "⚫ 黑方" : "⚪ 白方";
    $("resultTitle").textContent = "对局结束";
    let html = `<div class="result-winner">${winnerName} 胜</div>`;
    if (method === "认输") {
      html += `<div class="result-detail">对方认输</div>`;
    } else if (method === "数目") {
      html += `<div class="result-detail">
        黑方：<strong>${details.blackTotal}</strong> 子（棋子+领地）<br/>
        白方：<strong>${details.whiteTotal}</strong> 子（棋子+领地+贴目${KOMI}）<br/>
        黑方领地：${details.blackTerritory} · 白方领地：${details.whiteTerritory}<br/>
        胜负：<strong>${details.margin.toFixed(1)}</strong> 子
      </div>`;
    }
    $("resultContent").innerHTML = html;
    $("resultModal").style.display = "flex";
  }

  // ---------- 新对局 ----------
  function newGame() {
    state.size = Number($("boardSize").value);
    state.playerColor = $("playerColor").value === "black" ? BLACK : WHITE;
    state.aiSimulations = Number($("aiLevel").value);
    state.board = new Int8Array(state.size * state.size);
    state.currentPlayer = BLACK;
    state.captures = { 1: 0, 2: 0 };
    state.history = [];
    state.koPoint = -1;
    state.lastMove = -1;
    state.consecutivePasses = 0;
    state.gameOver = false;
    state.aiThinking = false;

    // 重置 AI 搜索树（树复用到新对局为止）
    if (state.worker) state.worker.postMessage({ type: "reset" });

    resizeCanvas();
    render();
    updateInfo();
    $("resultModal").style.display = "none";

    // 如果玩家执白，AI先手
    if (state.playerColor === WHITE) {
      setTimeout(aiMove, 500);
    }
  }

  // ---------- 事件绑定 ----------
  function bindEvents() {
    $("newGameBtn").addEventListener("click", newGame);
    $("undoBtn").addEventListener("click", undo);
    $("passBtn").addEventListener("click", pass);
    $("resignBtn").addEventListener("click", resign);
    $("resultNewGame").addEventListener("click", newGame);
    $("resultClose").addEventListener("click", () => $("resultModal").style.display = "none");
    $("showCoords").addEventListener("change", render);
    $("boardSize").addEventListener("change", () => {
      if (confirm("切换棋盘大小将开始新对局，确定吗？")) newGame();
      else $("boardSize").value = state.size;
    });
    $("playerColor").addEventListener("change", () => {
      if (confirm("切换执子颜色将开始新对局，确定吗？")) newGame();
      else $("playerColor").value = state.playerColor === BLACK ? "black" : "white";
    });
    $("aiLevel").addEventListener("change", () => {
      state.aiSimulations = Number($("aiLevel").value);
    });

    window.addEventListener("resize", () => {
      resizeCanvas();
      render();
    });
  }

  // ---------- 初始化 ----------
  function init() {
    bindEvents();
    initWorker();
    newGame();
  }

  init();
})();
