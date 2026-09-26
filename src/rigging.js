'use strict';

/*
 * 舞台吊挂布景载荷核算
 *
 * 同一横梁上的吊点具有横坐标 x（整数厘米）与额定载荷（整数千克）；
 * 吊挂件具有重量（整数千克）、重心横坐标（整数厘米）、左右吊点与生效起止秒数。
 * 仅允许重心位于两吊点之间（含吊点正上方），且左吊点横坐标必须小于右吊点。
 *
 * 每件吊挂件按力矩平衡分担到两吊点：
 *   左分担 = 重量 × (右吊点 x − 重心 x) / (右吊点 x − 左吊点 x)
 *   右分担 = 重量 × (重心 x − 左吊点 x) / (右吊点 x − 左吊点 x)
 * 分担量是有理数：全程以分数（BigInt 分子分母，始终约分）累计与比较，
 * 载荷恰好等于额定不算超额，避免临界值（如 1/3 + 2/3 = 1）的浮点舍入误判。
 *
 * 各吊点载荷按半开时段 [起, 止) 汇总：同一秒结束先于开始
 * （与按时刻分组求和等价——零时长的瞬态不产生任何区间）。
 * 输出每个吊点的峰值载荷、超额区间及超额量（峰值载荷 − 额定载荷），
 * 相邻的连续超额区间合并为一条。
 */

/* ---------- 分数（有理数）运算：{ n, d }，BigInt，d > 0，始终约分 ---------- */

function gcdBig(a, b) {
  a = a < 0n ? -a : a;
  b = b < 0n ? -b : b;
  while (b !== 0n) {
    const t = a % b;
    a = b;
    b = t;
  }
  return a;
}

/** 构造约分后的分数 */
function frac(n, d) {
  let bn = BigInt(n);
  let bd = BigInt(d);
  if (bd < 0n) {
    bn = -bn;
    bd = -bd;
  }
  if (bn === 0n) return { n: 0n, d: 1n };
  const g = gcdBig(bn, bd);
  return { n: bn / g, d: bd / g };
}

const FRAC_ZERO = frac(0, 1);

function addFrac(a, b) {
  return frac(a.n * b.d + b.n * a.d, a.d * b.d);
}

function negFrac(a) {
  return { n: -a.n, d: a.d };
}

function subFrac(a, b) {
  return addFrac(a, negFrac(b));
}

/** 比较两个分数：a < b 返回 -1，相等返回 0，a > b 返回 1（BigInt 交叉相乘，精确） */
function cmpFrac(a, b) {
  const l = a.n * b.d;
  const r = b.n * a.d;
  return l < r ? -1 : l > r ? 1 : 0;
}

function isZeroFrac(f) {
  return f.n === 0n;
}

/* ---------- 载荷值展示 ---------- */

/**
 * 分数转 JSON：text 为可直接展示的文本（有限小数直接给出，无限小数保留 4 位并附精确分数），
 * kg 为 6 位小数近似值，num/den 为精确分子分母（字符串，避免大数精度丢失）。
 */
function fracToJson(f) {
  const r = frac(f.n, f.d);
  const value = Number(r.n) / Number(r.d);
  let text;
  if (r.d === 1n) {
    text = r.n.toString();
  } else {
    const dec = (Math.round(value * 10000) / 10000).toString();
    // 4 位小数内可精确表示时直接给出，否则附精确分数
    text = (r.n * 10000n) % r.d === 0n ? dec : `${dec}…（=${r.n}/${r.d}）`;
  }
  return { text, kg: Math.round(value * 1e6) / 1e6, num: r.n.toString(), den: r.d.toString() };
}

/* ---------- 吊挂件几何约束（写入前已由路由校验，此处兜底：非法件不参与核算） ---------- */

/** 返回 null 表示合法，否则返回原因文本 */
function loadGeometryError(load, pointById) {
  const left = pointById.get(load.leftPointId);
  const right = pointById.get(load.rightPointId);
  if (!left || !right) return '左 / 右吊点不存在';
  if (left.id === right.id) return '左右吊点是同一吊点';
  if (left.x >= right.x) return '左吊点未位于右吊点左侧';
  if (load.cgX < left.x || load.cgX > right.x) return '重心横坐标不在两吊点之间';
  if (!Number.isInteger(load.start) || !Number.isInteger(load.end) || load.start < 0 || load.start >= load.end) {
    return '生效起止秒数非法';
  }
  return null;
}

/** 力矩平衡分担：返回 { left, right } 两个分数（kg） */
function shareOf(load, leftX, rightX) {
  const span = rightX - leftX;
  return {
    left: frac(BigInt(load.weightKg) * BigInt(rightX - load.cgX), BigInt(span)),
    right: frac(BigInt(load.weightKg) * BigInt(load.cgX - leftX), BigInt(span)),
  };
}

/* ---------- 单吊点载荷扫描 ---------- */

/**
 * 对单个吊点的分担记录 [{ share, start, end }] 做时间扫描。
 * 半开区间 [start, end)：同一秒结束先于开始（按时刻分组求和，与「先出后进」等价）。
 * 返回 { peak, peakStart, peakEnd, overloads }：
 *   peak 为峰值载荷分数（无任何分担时为 null），peakStart/peakEnd 为首次达到峰值的区间；
 *   overloads 为合并相邻连续区间后的超额列表，每条含起止、持续秒数、峰值载荷与超额量（均为分数）。
 */
function sweepPoint(ratedKg, entries) {
  const events = [];
  for (const e of entries) {
    if (isZeroFrac(e.share)) continue; // 零分担不产生载荷变化
    events.push({ t: e.start, d: e.share });
    events.push({ t: e.end, d: negFrac(e.share) });
  }
  events.sort((a, b) => a.t - b.t);

  // 按时刻分组求和，得到逐段恒定载荷 [t, nextT)
  const segments = [];
  let level = FRAC_ZERO;
  let i = 0;
  while (i < events.length) {
    const t = events[i].t;
    while (i < events.length && events[i].t === t) {
      level = addFrac(level, events[i].d);
      i++;
    }
    const nextT = i < events.length ? events[i].t : null;
    if (nextT !== null) segments.push({ start: t, end: nextT, load: level });
  }

  const rated = frac(ratedKg, 1);
  let peak = null;
  let peakStart = null;
  let peakEnd = null;
  const overloads = [];
  let cur = null; // 当前（合并中的）连续超额区间

  const closeCur = () => {
    overloads.push({
      start: cur.start,
      end: cur.end,
      durationSeconds: cur.end - cur.start,
      peakLoad: cur.peakLoad,
      excess: subFrac(cur.peakLoad, rated),
    });
    cur = null;
  };

  for (const seg of segments) {
    if (peak === null || cmpFrac(seg.load, peak) > 0) {
      peak = seg.load;
      peakStart = seg.start;
      peakEnd = seg.end;
    }
    if (cmpFrac(seg.load, rated) > 0) {
      if (cur) {
        // 扫描段天然首尾相接：相邻的连续超额区间合并为一条
        cur.end = seg.end;
        if (cmpFrac(seg.load, cur.peakLoad) > 0) cur.peakLoad = seg.load;
      } else {
        cur = { start: seg.start, end: seg.end, peakLoad: seg.load };
      }
    } else if (cur) {
      closeCur();
    }
  }
  if (cur) closeCur();

  return { peak, peakStart, peakEnd, overloads };
}

/* ---------- 全量核算 ---------- */

/**
 * 核算全部吊点载荷。
 * 返回 {
 *   points: [{ id, name, x, ratedKg, loadCount, status, peak, peakStart, peakEnd, overloads }]（按横坐标排序）,
 *   loads:  [{ id, name, weightKg, cgX, start, end, left/right 吊点信息与分担量 }]（数据顺序）,
 *   invalidLoads: [{ id, name, reason }]（几何非法、未参与核算的吊挂件，正常 API 写入不会产生）,
 *   summary: { points, loads, invalidLoads, overloadedPoints, overloadIntervals }
 * }
 */
function computeRigging(data) {
  const points = (Array.isArray(data.rigPoints) ? data.rigPoints : [])
    .slice()
    .sort((a, b) => a.x - b.x || String(a.id).localeCompare(String(b.id)));
  const loads = Array.isArray(data.rigLoads) ? data.rigLoads : [];
  const pointById = new Map(points.map((p) => [p.id, p]));

  const byPoint = new Map(points.map((p) => [p.id, []]));
  const loadResults = [];
  const invalidLoads = [];

  for (const load of loads) {
    const err = loadGeometryError(load, pointById);
    if (err) {
      invalidLoads.push({ id: load.id, name: load.name, reason: err });
      continue;
    }
    const left = pointById.get(load.leftPointId);
    const right = pointById.get(load.rightPointId);
    const shares = shareOf(load, left.x, right.x);
    byPoint.get(left.id).push({ share: shares.left, start: load.start, end: load.end });
    byPoint.get(right.id).push({ share: shares.right, start: load.start, end: load.end });
    loadResults.push({
      id: load.id,
      name: load.name,
      weightKg: load.weightKg,
      cgX: load.cgX,
      start: load.start,
      end: load.end,
      leftPointId: left.id,
      leftPointName: left.name,
      leftX: left.x,
      rightPointId: right.id,
      rightPointName: right.name,
      rightX: right.x,
      leftShare: fracToJson(shares.left),
      rightShare: fracToJson(shares.right),
    });
  }

  const pointResults = points.map((p) => {
    const entries = byPoint.get(p.id);
    const { peak, peakStart, peakEnd, overloads } = sweepPoint(p.ratedKg, entries);
    return {
      id: p.id,
      name: p.name,
      x: p.x,
      ratedKg: p.ratedKg,
      loadCount: entries.length,
      status: entries.length === 0 ? 'idle' : overloads.length > 0 ? 'over' : 'ok',
      peak: peak ? fracToJson(peak) : null,
      peakStart,
      peakEnd,
      overloads: overloads.map((o) => ({
        start: o.start,
        end: o.end,
        durationSeconds: o.durationSeconds,
        peakLoad: fracToJson(o.peakLoad),
        excess: fracToJson(o.excess),
      })),
    };
  });

  const summary = {
    points: points.length,
    loads: loads.length,
    invalidLoads: invalidLoads.length,
    overloadedPoints: pointResults.filter((p) => p.status === 'over').length,
    overloadIntervals: pointResults.reduce((n, p) => n + p.overloads.length, 0),
  };

  return { points: pointResults, loads: loadResults, invalidLoads, summary };
}

module.exports = { computeRigging, sweepPoint, shareOf, fracToJson, frac, addFrac, cmpFrac };
