#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
depcheck.py — 依赖冲突提前检查工具（纯 Python 标准库，单文件，无需安装任何依赖）

用法:
    python3 depcheck.py deps.txt            # 完整检查（依赖树 + 冲突 + 环 + 缺失）
    python3 depcheck.py deps.txt --no-tree  # 只输出问题清单

输入格式（每行一条，# 开头为注释，空行忽略）:
    包名 依赖包 版本要求

版本要求写法:
    * 或 any            任意版本
    1.2.3 或 ==1.2.3    精确等于某一版本
    >1.0  >=1.0  <2.0  <=2.0
    >=1.0,<2.0          逗号表示“并且”（多个条件同时满足）
    [1.0,2.0)           区间写法：[ ] 闭区间，( ) 开区间，端点可省略，如 [1.0,) (,2.0]

交集判定规则（冲突判定依据）:
    每个版本要求被视为一个“可接受版本集合”（统一归一化为区间 [lo, hi]）。
    对同一个依赖包，把它的所有要求（无论直接还是间接来自谁）逐一求交集：
      - 交集非空 => 至少存在一个版本能同时满足所有要求 => 不算冲突；
      - 交集为空 => 不存在任何版本能让所有依赖方满意 => 判定冲突。
    精确等于 x 视为退化区间 [x, x]；“任意”视为 (-inf, +inf)，与任何区间相交都不改变对方。
    理由：集成时最终只能选定一个版本，判定标准就应该是“是否存在一个版本同时满足
    所有约束”，即集合论意义上的交集非空，而不是两两比较是否完全相同。

退出码: 0 = 未发现问题；1 = 发现冲突/环/缺失；2 = 用法或输入文件错误
"""

import argparse
import sys
from collections import defaultdict, deque


class InputError(Exception):
    """输入文件格式错误。"""


# ---------------------------------------------------------------- 版本

class Version:
    """点分版本号，按段数值比较，缺段补 0（1.2 与 1.2.0 相等）。"""

    __slots__ = ("text", "parts")

    def __init__(self, text):
        text = text.strip()
        if not text or not text[0].isdigit():
            raise ValueError("非法版本号: %r" % (text,))
        self.text = text
        parts = []
        for piece in text.split("."):
            digits = ""
            for ch in piece:
                if ch.isdigit():
                    digits += ch
                else:
                    break
            parts.append(int(digits) if digits else 0)
        self.parts = tuple(parts)

    def _padded(self, n):
        return self.parts + (0,) * max(0, n - len(self.parts))

    def __eq__(self, other):
        n = max(len(self.parts), len(other.parts))
        return self._padded(n) == other._padded(n)

    def __lt__(self, other):
        n = max(len(self.parts), len(other.parts))
        return self._padded(n) < other._padded(n)

    def __le__(self, other):
        return self == other or self < other


# ---------------------------------------------------------------- 版本要求（区间）

class Interval:
    """版本区间 [lo, hi]，lo/hi 为 None 表示该方向无界。"""

    __slots__ = ("lo", "lo_closed", "hi", "hi_closed")

    def __init__(self, lo=None, lo_closed=True, hi=None, hi_closed=True):
        self.lo = lo
        self.lo_closed = lo_closed
        self.hi = hi
        self.hi_closed = hi_closed

    @staticmethod
    def any():
        return Interval()

    def is_empty(self):
        if self.lo is None or self.hi is None:
            return False
        if self.lo < self.hi:
            return False
        if self.lo == self.hi:
            return not (self.lo_closed and self.hi_closed)
        return True

    def intersect(self, other):
        # 下界取两者较大者（相等时取更严格的开区间）
        if self.lo is None:
            lo, lo_closed = other.lo, other.lo_closed
        elif other.lo is None:
            lo, lo_closed = self.lo, self.lo_closed
        elif self.lo == other.lo:
            lo, lo_closed = self.lo, self.lo_closed and other.lo_closed
        elif self.lo < other.lo:
            lo, lo_closed = other.lo, other.lo_closed
        else:
            lo, lo_closed = self.lo, self.lo_closed
        # 上界取两者较小者（同理）
        if self.hi is None:
            hi, hi_closed = other.hi, other.hi_closed
        elif other.hi is None:
            hi, hi_closed = self.hi, self.hi_closed
        elif self.hi == other.hi:
            hi, hi_closed = self.hi, self.hi_closed and other.hi_closed
        elif self.hi < other.hi:
            hi, hi_closed = self.hi, self.hi_closed
        else:
            hi, hi_closed = other.hi, other.hi_closed
        return Interval(lo, lo_closed, hi, hi_closed)

    def __str__(self):
        if self.lo is None and self.hi is None:
            return "*"
        if (self.lo is not None and self.hi is not None
                and self.lo == self.hi and self.lo_closed and self.hi_closed):
            return "==%s" % self.lo.text
        left = "[" if self.lo_closed else "("
        right = "]" if self.hi_closed else ")"
        lo_s = self.lo.text if self.lo is not None else "-inf"
        hi_s = self.hi.text if self.hi is not None else "+inf"
        return "%s%s, %s%s" % (left, lo_s, hi_s, right)


def _comparator_interval(op, version):
    if op == ">=":
        return Interval(version, True, None, True)
    if op == "<=":
        return Interval(None, True, version, True)
    if op == ">":
        return Interval(version, False, None, True)
    if op == "<":
        return Interval(None, True, version, False)
    return Interval(version, True, version, True)  # == 或 =


def parse_requirement(spec):
    """把版本要求文本解析为区间。支持: * / any / 裸版本号 / 比较符 / 逗号与 / [a,b) 区间。"""
    spec = spec.strip()
    if spec in ("", "*", "any", "ANY", "Any", "all", "ALL"):
        return Interval.any()
    if spec[0] in "[(":
        if len(spec) < 2 or spec[-1] not in ")]" or "," not in spec:
            raise ValueError("无法识别的区间写法: %r" % spec)
        lo_s, hi_s = spec[1:-1].split(",", 1)
        lo = Version(lo_s) if lo_s.strip() else None
        hi = Version(hi_s) if hi_s.strip() else None
        return Interval(lo, spec[0] == "[", hi, spec[-1] == "]")
    result = Interval.any()
    for token in spec.split(","):
        token = token.strip()
        if not token:
            continue
        matched = False
        for op in (">=", "<=", "==", ">", "<", "="):
            if token.startswith(op):
                result = result.intersect(_comparator_interval(op, Version(token[len(op):])))
                matched = True
                break
        if not matched:
            if not token[0].isdigit():
                raise ValueError("无法识别的版本要求: %r" % token)
            v = Version(token)  # 裸版本号视为精确等于
            result = result.intersect(Interval(v, True, v, True))
    return result


# ---------------------------------------------------------------- 输入解析

class Edge:
    __slots__ = ("src", "dst", "spec", "req", "lineno")

    def __init__(self, src, dst, spec, req, lineno):
        self.src = src
        self.dst = dst
        self.spec = spec
        self.req = req
        self.lineno = lineno


def parse_file(path):
    edges = []
    defined = {}  # 包名 -> 首次定义行号
    with open(path, encoding="utf-8") as fh:
        for lineno, raw in enumerate(fh, 1):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split(None, 2)
            if len(parts) < 3:
                raise InputError("第 %d 行格式错误（应为: 包名 依赖包 版本要求）: %s"
                                 % (lineno, raw.rstrip()))
            src, dst, spec = parts
            try:
                req = parse_requirement(spec)
            except ValueError as exc:
                raise InputError("第 %d 行版本要求解析失败: %s" % (lineno, exc))
            edges.append(Edge(src, dst, spec, req, lineno))
            defined.setdefault(src, lineno)
    if not edges:
        raise InputError("文件中没有有效的依赖记录")
    return edges, defined


# ---------------------------------------------------------------- 图分析

def build_graph(edges):
    adjacency = defaultdict(list)   # src -> [Edge]
    incoming = defaultdict(list)    # dst -> [Edge]
    for e in edges:
        adjacency[e.src].append(e)
        incoming[e.dst].append(e)
    return adjacency, incoming


def find_roots(defined, incoming):
    roots = [p for p in defined if p not in incoming]
    return roots if roots else list(defined)  # 全部成环时以所有包为起点


def compute_paths(roots, adjacency):
    """BFS 求每个节点从根出发的一条最短路径。"""
    paths = {}
    queue = deque((r, [r]) for r in roots)
    while queue:
        node, path = queue.popleft()
        if node in paths:
            continue
        paths[node] = path
        for e in adjacency.get(node, ()):
            if e.dst not in paths:
                queue.append((e.dst, path + [e.dst]))
    return paths


def find_cycles(defined, adjacency):
    """DFS 找所有依赖环，返回环路径列表（如 [a, b, a]）。"""
    color = {p: 0 for p in defined}  # 0=未访问 1=在栈上 2=已完成
    stack = []
    cycles, seen = [], set()

    def normalize(cyc):
        i = cyc.index(min(cyc))
        return tuple(cyc[i:] + cyc[:i])

    for start in defined:
        if color[start]:
            continue
        color[start] = 1
        stack.append(start)
        work = [(start, iter(adjacency.get(start, ())))]
        while work:
            node, it = work[-1]
            descended = False
            for e in it:
                dst = e.dst
                if dst not in color:
                    continue  # 缺失包不参与环检测
                if color[dst] == 0:
                    color[dst] = 1
                    stack.append(dst)
                    work.append((dst, iter(adjacency.get(dst, ()))))
                    descended = True
                    break
                if color[dst] == 1:
                    idx = stack.index(dst)
                    cyc = stack[idx:]
                    key = normalize(cyc)
                    if key not in seen:
                        seen.add(key)
                        cycles.append(cyc + [dst])
            if not descended:
                color[node] = 2
                stack.pop()
                work.pop()
    return cycles


def find_conflicts(incoming):
    """同一依赖包的所有版本要求求交集，为空即冲突。"""
    conflicts = []
    for dst in sorted(incoming):
        reqs = sorted(incoming[dst], key=lambda e: e.lineno)
        acc = Interval.any()
        for e in reqs:
            acc = acc.intersect(e.req)
        if acc.is_empty():
            conflicts.append((dst, reqs))
    return conflicts


def find_missing(edges, defined):
    missing = defaultdict(list)
    for e in edges:
        if e.dst not in defined:
            missing[e.dst].append(e)
    return missing


# ---------------------------------------------------------------- 输出

def render_tree(roots, adjacency, defined):
    lines = []
    shown = set()

    def walk(node, prefix, active):
        edges = adjacency.get(node, [])
        for i, e in enumerate(edges):
            last = i == len(edges) - 1
            conn = "`-- " if last else "+-- "
            label = "%s  [%s]" % (e.dst, e.spec)
            if e.dst in active:
                lines.append(prefix + conn + label + "  <== 循环依赖!")
            elif e.dst not in defined:
                lines.append(prefix + conn + label + "  [缺失]")
            elif e.dst in shown:
                lines.append(prefix + conn + label + "  (见上)")
            else:
                lines.append(prefix + conn + label)
                shown.add(e.dst)
                walk(e.dst, prefix + ("    " if last else "|   "), active | {e.dst})

    for root in roots:
        lines.append(root)
        shown.add(root)
        walk(root, "", {root})
    return lines


def format_conflicts(conflicts, paths):
    out = []
    for dst, reqs in conflicts:
        out.append("[冲突] 包 <%s> 收到 %d 个互相矛盾的版本要求，交集为空:"
                   % (dst, len(reqs)))
        for i, e in enumerate(reqs, 1):
            path = paths.get(e.src, [e.src]) + [e.dst]
            out.append("  路径%d: %s" % (i, " -> ".join(path)))
            out.append("         要求 %-12s 来自第 %d 行: %s %s %s"
                       % (e.spec, e.lineno, e.src, e.dst, e.spec))
        out.append("  => 不存在能同时满足以上全部要求的 <%s> 版本" % dst)
        out.append("")
    return out


def format_cycles(cycles):
    out = []
    for cyc in cycles:
        out.append("[环] " + " -> ".join(cyc) +
                   "   （%s 通过传递链依赖了自身）" % cyc[0])
    return out


def format_missing(missing):
    out = []
    for pkg in sorted(missing):
        out.append("[缺失] 包 <%s> 被依赖但未在列表中定义:" % pkg)
        for e in missing[pkg]:
            out.append("         第 %d 行: %s 依赖 %s (%s)"
                       % (e.lineno, e.src, e.dst, e.spec))
    return out


# ---------------------------------------------------------------- 主流程

def main(argv=None):
    ap = argparse.ArgumentParser(
        description="依赖冲突提前检查工具（纯标准库单文件）")
    ap.add_argument("file", help="依赖列表文件，每行: 包名 依赖包 版本要求")
    ap.add_argument("--no-tree", action="store_true", help="不输出依赖树")
    args = ap.parse_args(argv)

    try:
        edges, defined = parse_file(args.file)
    except FileNotFoundError:
        print("错误: 找不到文件 %s" % args.file, file=sys.stderr)
        return 2
    except InputError as exc:
        print("错误: %s" % exc, file=sys.stderr)
        return 2

    adjacency, incoming = build_graph(edges)
    roots = find_roots(defined, incoming)
    paths = compute_paths(roots, adjacency)
    conflicts = find_conflicts(incoming)
    cycles = find_cycles(defined, adjacency)
    missing = find_missing(edges, defined)

    if not args.no_tree:
        print("========== 依赖树 ==========")
        for line in render_tree(roots, adjacency, defined):
            print(line)
        print()

    print("========== 版本冲突 (%d) ==========" % len(conflicts))
    if conflicts:
        for line in format_conflicts(conflicts, paths):
            print(line)
    else:
        print("无")
    print()

    print("========== 依赖环 (%d) ==========" % len(cycles))
    if cycles:
        for line in format_cycles(cycles):
            print(line)
    else:
        print("无")
    print()

    print("========== 缺失依赖 (%d) ==========" % len(missing))
    if missing:
        for line in format_missing(missing):
            print(line)
    else:
        print("无")
    print()

    problems = len(conflicts) + len(cycles) + len(missing)
    print("========== 汇总 ==========")
    if problems:
        print("发现 %d 处版本冲突、%d 个依赖环、%d 个缺失依赖，请修复后再集成。"
              % (len(conflicts), len(cycles), len(missing)))
        return 1
    print("未发现问题，可以集成。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
