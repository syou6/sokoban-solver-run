// Sokoban solver for make.fun's sokoban-solver-01-run-20261121 (program/v1: node /bot/main.ts,
// Node 22). A rerun of sokoban-solver-01 with the same generator and the same level family.
//
// Approach. The levels this competition draws are a one-square hallway with one to four small
// rooms off it, each room holding 3 or 4 boxes and as many goals, and a box can never leave its
// room — so a level's push optimum is the sum of its rooms' optima. This program therefore:
//   1. splits the level into rooms (the dead squares of the player's own row — the hallway —
//      are cut out of the floor; each part left that holds a box is a room),
//   2. solves each room on its own with an exact A* search over pushes: a state is the boxes'
//      squares plus the player's reachable region, the estimate is a minimum-cost matching of
//      boxes to goals over true one-box push distances (admissible, so the first solution an
//      A* pop settles is push-optimal), with dead-square, frozen 2x2 and freeze-deadlock
//      pruning and a transposition table,
//   3. falls back to the same exact search over the whole level when a level is not a set of
//      rooms, and verifies its own answer by replay before writing it.
// Every budget is a count of expanded states, never the clock, and every tie is broken by
// square order, so two runs of this program write the same bytes.
//
// Local run: mkdir -p out && MAKEFUN_INPUT_DIR=<input> MAKEFUN_OUTPUT_DIR=out node main.ts
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

/** Per-search expansion budgets (work, never time): generous beside what these rooms need. */
const ROOM_BUDGET = 1500000;
const LEVEL_BUDGET = 4000000;

/** The four directions: [dx, dy, walk letter, push letter]. */
const DIRS = [
  [0, -1, 'u', 'U'],
  [0, 1, 'd', 'D'],
  [-1, 0, 'l', 'L'],
  [1, 0, 'r', 'R'],
];

/**
 * A level in XSB text (# wall, space floor, . goal, $ box, * box on a goal, @ player,
 * + player on a goal), one row a line. Short rows and the outer frame read as walls.
 */
function parseLevel(text) {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals = [];
  const boxes = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x];
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
    }
  }
  boxes.sort((a, b) => a - b);
  goals.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player };
}

/**
 * For each goal, the fewest pushes that bring one box from any square onto it, other boxes
 * ignored: a breadth-first search backwards over pulls. -1 where no push sequence reaches.
 */
function pushDistances(wall, goals, w) {
  const size = wall.length;
  return goals.map((goal) => {
    const dist = new Int32Array(size).fill(-1);
    dist[goal] = 0;
    const queue = [goal];
    for (let qi = 0; qi < queue.length; qi++) {
      const x = queue[qi];
      for (let k = 0; k < 4; k++) {
        const d = k === 0 ? -w : k === 1 ? w : k === 2 ? -1 : 1;
        const y = x - d; // a box on y pushes onto x when the player stands on y - d
        if (y < 0 || y >= size || wall[y] || wall[y - d] || dist[y] !== -1) continue;
        dist[y] = dist[x] + 1;
        queue.push(y);
      }
    }
    return dist;
  });
}

/** The squares from which a box can reach some goal at all (the union of pushDistances). */
function liveSquares(dists, size) {
  const live = new Uint8Array(size);
  for (const dist of dists) {
    for (let i = 0; i < size; i++) if (dist[i] >= 0) live[i] = 1;
  }
  return live;
}

/**
 * The admissible estimate: the cheapest matching of boxes to distinct goals over the push
 * distances (each push moves one box one square, so no solution pushes less). Infinity when
 * some box can reach no goal it could be matched to. Exact matching by permutation for the
 * small counts these levels hold; the sum of each box's nearest distance above that.
 */
function estimate(dists, boxes) {
  boxes = Array.from(boxes);
  const n = boxes.length;
  if (n === 0) return 0;
  if (n !== dists.length) {
    let sum = 0;
    for (const b of boxes) {
      let best = Infinity;
      for (const dist of dists) if (dist[b] >= 0 && dist[b] < best) best = dist[b];
      if (best === Infinity) return Infinity;
      sum += best;
    }
    return sum;
  }
  if (n > 7) {
    let sum = 0;
    for (let bi = 0; bi < n; bi++) {
      let best = Infinity;
      for (let gi = 0; gi < n; gi++) {
        const c = dists[gi][boxes[bi]];
        if (c >= 0 && c < best) best = c;
      }
      if (best === Infinity) return Infinity;
      sum += best;
    }
    return sum;
  }
  // cost[bi][gi]
  const cost = boxes.map((b) => dists.map((dist) => dist[b]));
  for (let bi = 0; bi < n; bi++) {
    if (cost[bi].every((c) => c < 0)) return Infinity;
  }
  const used = new Uint8Array(n);
  let best = Infinity;
  const walk = (bi, acc) => {
    if (acc >= best) return;
    if (bi === n) {
      best = acc;
      return;
    }
    for (let gi = 0; gi < n; gi++) {
      if (used[gi] || cost[bi][gi] < 0) continue;
      used[gi] = 1;
      walk(bi + 1, acc + cost[bi][gi]);
      used[gi] = 0;
    }
  };
  walk(0, 0);
  return best;
}

/** Whether a box sits in a frozen 2x2 block of walls and boxes while off its goal. */
function frozenBlock(wall, occupied, goalSet, t, w) {
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1;
    const c = a + w;
    const d = c + 1;
    if (!(wall[a] || occupied[a]) || !(wall[b] || occupied[b]) || !(wall[c] || occupied[c]) || !(wall[d] || occupied[d])) continue;
    if ((occupied[a] && !goalSet[a]) || (occupied[b] && !goalSet[b]) || (occupied[c] && !goalSet[c]) || (occupied[d] && !goalSet[d])) return true;
  }
  return false;
}

/**
 * Whether some box can never move again and is off its goal: a box hemmed in on both axes by
 * walls or by boxes themselves frozen, grown to a fixed point. Only provably immovable boxes
 * are marked, so no solvable state is ever pruned by this.
 */
function frozenOffGoal(wall, boxes, goalSet, w) {
  const n = boxes.length;
  const indexAt = new Int16Array(wall.length).fill(-1);
  for (let i = 0; i < n; i++) indexAt[boxes[i]] = i;
  const frozen = new Uint8Array(n);
  let changed = true;
  while (changed) {
    changed = false;
    for (let i = 0; i < n; i++) {
      if (frozen[i]) continue;
      const b = boxes[i];
      const blocked = (c) => wall[c] === 1 || (indexAt[c] >= 0 && frozen[indexAt[c]] === 1);
      if (blocked(b - 1) && blocked(b + 1) && blocked(b - w) && blocked(b + w)) {
        frozen[i] = 1;
        changed = true;
      }
    }
  }
  for (let i = 0; i < n; i++) if (frozen[i] && !goalSet[boxes[i]]) return true;
  return false;
}

/** The shortest walk from `from` to `to` around walls and boxes, in lower LURD letters. */
function walkTo(wall, occupied, from, to, w, size) {
  if (from === to) return '';
  const prev = new Int32Array(size).fill(-1);
  const how = new Array(size);
  const queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi];
    if (p === to) break;
    for (const [dx, dy, letter] of DIRS) {
      const q = p + dy * w + dx;
      if (q < 0 || q >= size || wall[q] || occupied[q] || prev[q] !== -1) continue;
      prev[q] = p;
      how[q] = letter;
      queue.push(q);
    }
  }
  if (prev[to] === -1) return null;
  let s = '';
  for (let p = to; p !== from; p = prev[p]) s = how[p] + s;
  return s;
}

/**
 * The exact push-optimal solution of one (sub-)level: {pushes, moves}, or null when the
 * expansion budget runs out first. A* over pushes; a state is the sorted boxes plus the
 * lowest square of the player's reachable region, and states are stored in flat pools.
 */
function solveOptimal(level, budget) {
  const { w, wall, goals, player } = level;
  const size = wall.length;
  const n = level.boxes.length;
  const goalSet = new Uint8Array(size);
  for (const g of goals) goalSet[g] = 1;
  const dists = pushDistances(wall, goals, w);
  const live = liveSquares(dists, size);
  if (level.boxes.some((b) => !live[b])) return null;
  if (level.boxes.every((b) => goalSet[b])) return { pushes: 0, moves: '' };

  const numericKeys = size ** (n + 1) < 2 ** 53;
  const keyOf = (boxes, low) => {
    if (numericKeys) {
      let k = low;
      for (const b of boxes) k = k * size + b;
      return k;
    }
    return String.fromCharCode(low, ...boxes);
  };

  // Flat state pools, doubled as they fill.
  let cap = 1 << 16;
  let boxesPool = new Int32Array(cap * n);
  let playerPool = new Int32Array(cap);
  let parentPool = new Int32Array(cap);
  let gPool = new Int32Array(cap);
  let fromPool = new Int32Array(cap);
  let toPool = new Int32Array(cap);
  let count = 0;
  const grow = () => {
    const bigger = (arr, fill) => {
      const next = new Int32Array(cap * 2 * fill);
      next.set(arr);
      return next;
    };
    boxesPool = bigger(boxesPool, n);
    playerPool = bigger(playerPool, 1);
    parentPool = bigger(parentPool, 1);
    gPool = bigger(gPool, 1);
    fromPool = bigger(fromPool, 1);
    toPool = bigger(toPool, 1);
    cap *= 2;
  };

  const occupied = new Uint8Array(size);
  // Two stamp grids: `seen` holds the region of the state being expanded (push generation
  // tests it), `mark` the regions of its successors — one grid would let a successor's flood
  // overwrite the very marks its siblings are tested against.
  const seen = new Int32Array(size);
  const mark = new Int32Array(size);
  const stack = new Int32Array(size);
  let seenStamp = 0;
  let markStamp = 0;
  // Flood the player's region from `from` into `grid`; returns its lowest square.
  const flood = (grid, stampValue, from) => {
    let low = from;
    let top = 0;
    stack[top++] = from;
    grid[from] = stampValue;
    while (top > 0) {
      const p = stack[--top];
      if (p < low) low = p;
      for (let k = 0; k < 4; k++) {
        const q = k === 0 ? p - w : k === 1 ? p + w : k === 2 ? p - 1 : p + 1;
        if (q >= 0 && q < size && !wall[q] && !occupied[q] && grid[q] !== stampValue) {
          grid[q] = stampValue;
          stack[top++] = q;
        }
      }
    }
    return low;
  };
  const region = (from) => flood(seen, ++seenStamp, from);
  const regionMark = (from) => flood(mark, ++markStamp, from);
  const setOccupied = (idx) => {
    occupied.fill(0);
    const off = idx * n;
    for (let i = 0; i < n; i++) occupied[boxesPool[off + i]] = 1;
  };

  // The open list: a binary heap on (f, then deeper g, then insertion order) — deterministic.
  const heapNode = [];
  const heapF = [];
  const heapOrd = [];
  let ord = 0;
  const less = (a, b) =>
    heapF[a] !== heapF[b]
      ? heapF[a] < heapF[b]
      : gPool[heapNode[a]] !== gPool[heapNode[b]]
        ? gPool[heapNode[a]] > gPool[heapNode[b]]
        : heapOrd[a] < heapOrd[b];
  const heapPush = (node, f) => {
    let i = heapNode.length;
    heapNode.push(node);
    heapF.push(f);
    heapOrd.push(ord++);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!less(i, p)) break;
      [heapNode[i], heapNode[p]] = [heapNode[p], heapNode[i]];
      [heapF[i], heapF[p]] = [heapF[p], heapF[i]];
      [heapOrd[i], heapOrd[p]] = [heapOrd[p], heapOrd[i]];
      i = p;
    }
  };
  const heapPop = () => {
    const topNode = heapNode[0];
    const lastNode = heapNode.pop();
    const lastF = heapF.pop();
    const lastOrd = heapOrd.pop();
    if (heapNode.length > 0) {
      heapNode[0] = lastNode;
      heapF[0] = lastF;
      heapOrd[0] = lastOrd;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= heapNode.length) break;
        if (c + 1 < heapNode.length && less(c + 1, c)) c++;
        if (!less(c, i)) break;
        [heapNode[i], heapNode[c]] = [heapNode[c], heapNode[i]];
        [heapF[i], heapF[c]] = [heapF[c], heapF[i]];
        [heapOrd[i], heapOrd[c]] = [heapOrd[c], heapOrd[i]];
        i = c;
      }
    }
    return topNode;
  };

  const best = new Map();
  const addState = (boxes, playerSq, parent, from, to, g) => {
    if (count >= cap) grow();
    const idx = count++;
    boxesPool.set(boxes, idx * n);
    playerPool[idx] = playerSq;
    parentPool[idx] = parent;
    gPool[idx] = g;
    fromPool[idx] = from;
    toPool[idx] = to;
    return idx;
  };

  const rootBoxes = level.boxes.slice();
  for (const b of rootBoxes) occupied[b] = 1;
  const rootLow = region(player);
  occupied.fill(0);
  const h0 = estimate(dists, rootBoxes);
  if (h0 === Infinity) return null;
  const root = addState(rootBoxes, player, -1, -1, -1, 0);
  best.set(keyOf(rootBoxes, rootLow), 0);
  heapPush(root, h0);

  let expanded = 0;
  let found = -1;
  const curBoxes = new Int32Array(n);
  while (heapNode.length > 0) {
    const idx = heapPop();
    const g = gPool[idx];
    curBoxes.set(boxesPool.subarray(idx * n, idx * n + n));
    // Skip stale heap entries: a cheaper route to this state was settled after this push.
    setOccupied(idx);
    const lowNow = region(playerPool[idx]);
    if (best.get(keyOf(curBoxes, lowNow)) !== g) continue;
    let solved = true;
    for (let i = 0; i < n; i++) if (!goalSet[curBoxes[i]]) { solved = false; break; }
    if (solved) {
      found = idx;
      break;
    }
    if (++expanded > budget) return null;
    const here = seenStamp;
    for (let bi = 0; bi < n; bi++) {
      const b = curBoxes[bi];
      for (let k = 0; k < 4; k++) {
        const d = k === 0 ? -w : k === 1 ? w : k === 2 ? -1 : 1;
        const t = b + d;
        if (seen[b - d] !== here || wall[t] || occupied[t] || !live[t]) continue;
        const next = Int32Array.from(curBoxes);
        next[bi] = t;
        next.sort();
        // Deadlocks in the new configuration: a frozen 2x2, or a box frozen off its goal.
        occupied[b] = 0;
        occupied[t] = 1;
        const dead = frozenBlock(wall, occupied, goalSet, t, w) || frozenOffGoal(wall, next, goalSet, w);
        let key = null;
        let h = Infinity;
        if (!dead) {
          h = estimate(dists, next);
          if (h !== Infinity) key = keyOf(next, regionMark(b));
        }
        occupied[t] = 0;
        occupied[b] = 1;
        if (dead || h === Infinity) continue;
        const ng = g + 1;
        const known = best.get(key);
        if (known !== undefined && known <= ng) continue;
        best.set(key, ng);
        heapPush(addState(next, b, idx, b, t, ng), ng + h);
      }
    }
  }
  if (found < 0) return null;

  // Rebuild the moves: walk to each push's stand square on the parent's configuration, then push.
  const path = [];
  for (let s = found; s > 0; s = parentPool[s]) path.push(s);
  path.reverse();
  let moves = '';
  for (const s of path) {
    const parent = parentPool[s];
    const from = fromPool[s];
    const to = toPool[s];
    const d = to - from;
    const dir = DIRS.find(([dx, dy]) => dy * w + dx === d);
    setOccupied(parent);
    const walk = walkTo(wall, occupied, playerPool[parent], from - d, w, size);
    if (walk === null) return null;
    moves += walk + dir[3];
  }
  return { pushes: path.length, moves };
}

/**
 * The level's rooms: cut the dead squares of the player's row (the hallway: a box there can
 * reach no goal) out of the floor; each part left that holds a box is a room, its squares,
 * boxes and goals. Null when some part holds more or fewer boxes than goals, or a box starts
 * in the hallway: then the level is no set of rooms.
 */
function roomsOf(level) {
  const { w, wall, goals, boxes, player } = level;
  const size = wall.length;
  const live = liveSquares(pushDistances(wall, goals, w), size);
  const row = Math.floor(player / w);
  const cut = new Uint8Array(size);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !live[i]) cut[i] = 1;
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(size).fill(-1);
  const parts = [];
  for (let s = 0; s < size; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares = [s];
    part[s] = parts.length;
    for (let i = 0; i < squares.length; i++) {
      for (let k = 0; k < 4; k++) {
        const q = squares[i] + (k === 0 ? -w : k === 1 ? w : k === 2 ? -1 : 1);
        if (q >= 0 && q < size && !wall[q] && !cut[q] && part[q] < 0) {
          part[q] = parts.length;
          squares.push(q);
        }
      }
    }
    parts.push({ squares, boxes: [], goals: [] });
  }
  for (const b of boxes) parts[part[b]].boxes.push(b);
  for (const g of goals) if (part[g] >= 0) parts[part[g]].goals.push(g);
  if (goals.some((g) => part[g] < 0) || parts.some((p) => p.boxes.length !== p.goals.length)) return null;
  return parts.filter((p) => p.boxes.length > 0);
}

/** The square the player stands on after `moves` (LURD, case aside) from `from`. */
function endOf(w, from, moves) {
  let p = from;
  for (const ch of moves.toLowerCase()) p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  return p;
}

/**
 * The level solved room by room: each room's push-optimal solution in turn, the other rooms'
 * boxes standing as walls (on their goals once their room is done), the player walking on
 * from where the last room left it. Null when a room's search gives up or the level is no
 * set of rooms.
 */
function solveByRooms(level) {
  const rooms = roomsOf(level);
  if (rooms === null) return null;
  let player = level.player;
  let pushes = 0;
  let moves = '';
  for (const room of rooms) {
    const wall = level.wall.slice();
    for (const other of rooms) {
      if (other === room) continue;
      for (const b of other.done ? other.goals : other.boxes) wall[b] = 1;
    }
    const sub = {
      w: level.w,
      h: level.h,
      wall,
      goals: room.goals.slice().sort((a, b) => a - b),
      boxes: room.boxes.slice().sort((a, b) => a - b),
      player,
    };
    const solved = solveOptimal(sub, ROOM_BUDGET);
    if (solved === null) return null;
    pushes += solved.pushes;
    moves += solved.moves;
    player = endOf(level.w, player, solved.moves);
    room.done = true;
  }
  return { pushes, moves };
}

/** Replay `moves` on the level exactly as the checker does; true when it ends solved. */
function replaySolves(level, moves) {
  const { w, wall } = level;
  const goalSet = new Uint8Array(wall.length);
  for (const g of level.goals) goalSet[g] = 1;
  const box = new Uint8Array(wall.length);
  for (const b of level.boxes) box[b] = 1;
  let player = level.player;
  for (const ch of moves.toLowerCase()) {
    const d = ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
    const next = player + d;
    if (wall[next]) return false;
    if (box[next]) {
      const beyond = next + d;
      if (wall[beyond] || box[beyond]) return false;
      box[next] = 0;
      box[beyond] = 1;
    }
    player = next;
  }
  for (let i = 0; i < box.length; i++) if (box[i] && !goalSet[i]) return false;
  return true;
}

/** One level's answer: the rooms' optima where the level is a set of rooms, else the whole
 *  level searched at once; an empty string (a valid, scoreless answer) when nothing solves. */
function solve(text) {
  const level = parseLevel(text);
  if (level.player < 0 || level.boxes.length === 0) return '';
  const byRooms = solveByRooms(level);
  if (byRooms !== null && replaySolves(level, byRooms.moves)) return byRooms.moves;
  const whole = solveOptimal(level, LEVEL_BUDGET);
  if (whole !== null && replaySolves(level, whole.moves)) return whole.moves;
  return '';
}

for (const id of readdirSync(INPUT_DIR).sort()) {
  const moves = solve(readFileSync(join(INPUT_DIR, id, 'level.txt'), 'utf8'));
  mkdirSync(join(OUTPUT_DIR, id), { recursive: true });
  writeFileSync(join(OUTPUT_DIR, id, 'solution.txt'), `${moves}\n`);
}
