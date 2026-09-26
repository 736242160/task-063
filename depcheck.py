#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
depcheck.py — 依赖冲突静态检查工具（纯 Python 标准库，单文件，开箱即用）

用法:
    python3 depcheck.py deps.txt          # 检查文件
    python3 depcheck.py - < deps.txt      # 从标准输入读取
    python3 depcheck.py deps.txt --root app --root auth   # 指定根包(可多个)

输入格式（每行一条，# 开头为注释）:
    包名  依赖包  版本要求
    包名  -       -        （声明一个无依赖的包，第二段为 - 时忽略第三段）

版本要求写法:
    * 或 any            任意版本
    1.2 或 ==1.2        精确等于
    !=1.2               不等于
    >1.0  >=1.0  <2.0  <=2.0
    [1.0,2.0)           区间（[] 闭区间、() 开区间，端点留空表示无界）
    >=1.0,<2.0          逗号组合（各条件取交集）

冲突判定规则（交集判定）:
    每个版本要求被规范化为若干区间的并集；两个要求"兼容"当且仅当它们的
    区间集合存在非空交集（开闭端点按数学定义处理）。对同一个依赖包，
    收集图中所有直接/间接施加在它身上的要求并求总交集：交集为空即
    判定冲突。理由：只要存在至少一个具体版本能同时满足所有要求，依赖
    求解器理论上就能解析成功，因此采用"交集为空才算冲突"的保守策略，
    最大限度减少误报。

退出码: 0 = 无问题；1 = 发现冲突/环/缺失/格式错误；2 = 用法错误。
"""

import argparse
import re
import sys
from collections import deque


# ---------------------------------------------------------------- 版本比较

def vkey(text):
    """把 '1.20.3' 这类版本串转成可比较的元组；数字段按数值、其余按字符串。"""
    key = []
    for part in re.split(r"[.\-_+]", text.strip()):
        if part.isdigit():
            key.append((0, int(part), ""))
        else:
            key.append((1, 0, part))
    return tuple(key)


def vcmp(a, b):
    n = max(len(a), len(b))
    a = a + ((0, 0, ""),) * (n - len(a))
    b = b + ((0, 0, ""),) * (n - len(b))
    return (a > b) - (a < b)


# ---------------------------------------------------------------- 区间与要求
# 区间 = (low, low_inc, high, high_inc)；low/high 为 None 表示无界。

ANY = [(None, True, None, True)]


def iv_intersect(a, b):
    """两个区间求交，返回新区间或 None（不相交）。"""
    # 下界取较大者
    if a[0] is None:
        low, linc = b[0], b[1]
    elif b[0] is None:
        low, linc = a[0], a[1]
    else:
        c = vcmp(a[0], b[0])
        if c > 0:
            low, linc = a[0], a[1]
        elif c < 0:
            low, linc = b[0], b[1]
        else:
            low, linc = a[0], a[1] and b[1]
    # 上界取较小者
    if a[2] is None:
        high, hinc = b[2], b[3]
    elif b[2] is None:
        high, hinc = a[2], a[3]
    else:
        c = vcmp(a[2], b[2])
        if c < 0:
            high, hinc = a[2], a[3]
        elif c > 0:
            high, hinc = b[2], b[3]
        else:
            high, hinc = a[2], a[3] and b[3]
    # 合法性检查
    if low is not None and high is not None:
        c = vcmp(low, high)
        if c > 0:
            return None
        if c == 0 and not (linc and hinc):
            return None
    return (low, linc, high, hinc)


def req_intersect(r1, r2):
    """两个要求（区间列表）求交，返回区间列表；空列表表示无交集。"""
    out = []
    for x in r1:
        for y in r2:
            iv = iv_intersect(x, y)
            if iv is not None:
                out.append(iv)
    return out


_INTERVAL_RE = re.compile(r"^\s*([\[\(])\s*([^,]*?)\s*,\s*([^\]\)]*?)\s*([\]\)])\s*$")
_OP_RE = re.compile(r"^\s*(>=|<=|==|!=|>|<)?\s*(\S+)\s*$")


def parse_req(text):
    """解析版本要求为区间列表；解析失败抛 ValueError。"""
    text = text.strip()
    if text in ("", "*", "any", "ANY"):
        return list(ANY)

    m = _INTERVAL_RE.match(text)
    if m:
        lo_s, hi_s = m.group(2), m.group(3)
        low = vkey(lo_s) if lo_s else None
        high = vkey(hi_s) if hi_s else None
        iv = (low, m.group(1) == "[", high, m.group(4) == "]")
        if low is not None and high is not None:
            c = vcmp(low, high)
            if c > 0 or (c == 0 and not (iv[1] and iv[3])):
                return []
        return [iv]

    req = list(ANY)
    for part in text.split(","):
        m = _OP_RE.match(part)
        if not m:
            raise ValueError("无法解析的版本要求: %r" % part)
        op, ver = m.group(1) or "==", vkey(m.group(2))
        if op == ">":
            sub = [(ver, False, None, True)]
        elif op == ">=":
            sub = [(ver, True, None, True)]
        elif op == "<":
            sub = [(None, True, ver, False)]
        elif op == "<=":
            sub = [(None, True, ver, True)]
        elif op == "==":
            sub = [(ver, True, ver, True)]
        elif op == "!=":
            sub = [(None, True, ver, False), (ver, False, None, True)]
        else:
            raise ValueError("未知运算符: %r" % op)
        req = req_intersect(req, sub)
    return req


# ---------------------------------------------------------------- 图构建

class DepGraph:
    def __init__(self):
        self.deps = {}        # 包 -> [(依赖包, 要求原文, 要求区间, 行号)]
        self.constraints = {} # 被依赖包 -> [(来源包, 要求原文, 要求区间, 行号)]
        self.errors = []      # 格式错误 [(行号, 内容, 原因)]

    def add_line(self, lineno, line):
        parts = line.split(None, 2)
        if len(parts) < 3:
            self.errors.append((lineno, line, "格式错误：应为 '包名 依赖包 版本要求' 三段"))
            return
        pkg, dep, req_text = parts[0], parts[1], parts[2].strip()
        if dep == "-":
            self.deps.setdefault(pkg, [])
            return
        try:
            req = parse_req(req_text)
        except ValueError as exc:
            self.errors.append((lineno, line, str(exc)))
            return
        self.deps.setdefault(pkg, []).append((dep, req_text, req, lineno))
        self.constraints.setdefault(dep, []).append((pkg, req_text, req, lineno))


def load_graph(stream):
    g = DepGraph()
    for lineno, raw in enumerate(stream, 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        g.add_line(lineno, line)
    return g


# ---------------------------------------------------------------- 路径与环

def compute_paths(g, roots):
    """BFS 求每个节点从根出发的一条路径；不可达节点（如孤立环）以其自身为根。"""
    path = {}

    def bfs(start):
        if start in path:
            return
        path[start] = [start]
        dq = deque([start])
        while dq:
            u = dq.popleft()
            for (v, _t, _r, _ln) in g.deps.get(u, []):
                if v not in path:
                    path[v] = path[u] + [v]
                    dq.append(v)

    for r in roots:
        bfs(r)
    for u in list(g.deps) + list(g.constraints):
        bfs(u)
    return path


def find_cycles(g):
    """DFS 找所有回边环，按旋转规范化去重。返回环路径列表（首尾相接）。"""
    color = {}
    stack = []
    cycles, seen = [], set()
    sys.setrecursionlimit(max(10000, len(g.deps) * 4 + 100))

    def norm(cyc):
        i = cyc.index(min(cyc))
        return tuple(cyc[i:] + cyc[:i])

    def dfs(u):
        color[u] = 1
        stack.append(u)
        for (v, _t, _r, _ln) in g.deps.get(u, []):
            if v not in g.deps:
                continue
            c = color.get(v, 0)
            if c == 0:
                dfs(v)
            elif c == 1:
                cyc = stack[stack.index(v):]
                key = norm(cyc)
                if key not in seen:
                    seen.add(key)
                    cycles.append(cyc + [v])
        stack.pop()
        color[u] = 2

    for u in g.deps:
        if color.get(u, 0) == 0:
            dfs(u)
    return cycles


# ---------------------------------------------------------------- 输出

def render_tree(g, roots):
    lines, printed = [], set()

    def rec(name, req_text, prefix, connector, stack):
        label = name + (" (%s)" % req_text if req_text else "")
        if name in stack:
            cyc = stack[stack.index(name):] + [name]
            lines.append(prefix + connector + label + "  [环: " + " -> ".join(cyc) + "]")
            return
        if name not in g.deps:
            lines.append(prefix + connector + label + "  [缺失]")
            return
        if name in printed:
            lines.append(prefix + connector + label + "  [...]")
            return
        lines.append(prefix + connector + label)
        printed.add(name)
        children = g.deps.get(name, [])
        child_prefix = prefix + ("    " if connector.startswith("└") else "│   " if connector else "")
        for i, (d, rt, _q, _ln) in enumerate(children):
            conn = "└── " if i == len(children) - 1 else "├── "
            rec(d, rt, child_prefix, conn, stack + [name])

    for r in roots:
        rec(r, None, "", "", [])
    # 根未覆盖到的节点（孤立环等）也各自成树
    for u in g.deps:
        if u not in printed:
            rec(u, None, "", "", [])
    return lines


def report(g, roots):
    out = []
    problems = 0

    out.append("=== 依赖树 ===")
    out.extend(render_tree(g, roots))
    out.append("")

    paths = compute_paths(g, roots)

    # 版本冲突：同一被依赖包的所有要求求总交集
    out.append("=== 版本冲突 ===")
    conflict_n = 0
    for dep in sorted(g.constraints):
        cons = g.constraints[dep]
        if len(cons) < 2:
            continue
        texts = {c[1] for c in cons}
        if len(texts) < 2:
            continue  # 要求完全一致，不可能冲突
        merged = list(ANY)
        for (_s, _t, req, _ln) in cons:
            merged = req_intersect(merged, req)
            if not merged:
                break
        if merged:
            continue
        conflict_n += 1
        out.append("[冲突 #%d] 包 '%s' 的版本要求无交集：" % (conflict_n, dep))
        for (src, req_text, _req, lineno) in cons:
            chain = paths.get(src, [src]) + [dep]
            out.append("    要求 %-12s 来自 %-8s (输入第 %d 行)  路径: %s"
                       % (req_text, src, lineno, " -> ".join(chain)))
        out.append("")
    if conflict_n == 0:
        out.append("（无）")
    out.append("")
    problems += conflict_n

    # 依赖环
    out.append("=== 依赖环 ===")
    cycles = find_cycles(g)
    if cycles:
        for i, cyc in enumerate(cycles, 1):
            out.append("[环 #%d] %s" % (i, " -> ".join(cyc)))
    else:
        out.append("（无）")
    out.append("")
    problems += len(cycles)

    # 缺失依赖
    out.append("=== 缺失依赖 ===")
    missing = [d for d in sorted(g.constraints) if d not in g.deps]
    if missing:
        for dep in missing:
            out.append("[缺失] 包 '%s' 被依赖但未在列表中定义：" % dep)
            for (src, req_text, _req, lineno) in g.constraints[dep]:
                chain = paths.get(src, [src]) + [dep]
                out.append("    被 %-8s 以要求 %-12s 引用 (输入第 %d 行)  路径: %s"
                           % (src, req_text, lineno, " -> ".join(chain)))
    else:
        out.append("（无）")
    out.append("")
    problems += len(missing)

    # 格式错误
    if g.errors:
        out.append("=== 格式错误 ===")
        for (lineno, line, why) in g.errors:
            out.append("[错误] 第 %d 行: %s  -- %s" % (lineno, line, why))
        out.append("")
        problems += len(g.errors)

    out.append("=== 汇总 ===")
    out.append("包 %d 个，依赖关系 %d 条；版本冲突 %d 处，依赖环 %d 个，缺失依赖 %d 个，格式错误 %d 处。"
               % (len(g.deps), sum(len(v) for v in g.deps.values()),
                  conflict_n, len(cycles), len(missing), len(g.errors)))
    return "\n".join(out), problems


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="依赖冲突静态检查工具（纯标准库单文件）",
        epilog="输入每行: 包名 依赖包 版本要求；版本要求支持 * == != > >= < <= [a,b) 及逗号组合。")
    ap.add_argument("file", help="依赖列表文件路径，'-' 表示标准输入")
    ap.add_argument("--root", action="append", default=[],
                    help="指定根包（可多次）；默认取没有入边的包")
    args = ap.parse_args(argv)

    try:
        if args.file == "-":
            g = load_graph(sys.stdin)
        else:
            with open(args.file, "r", encoding="utf-8") as f:
                g = load_graph(f)
    except OSError as exc:
        print("无法读取输入: %s" % exc, file=sys.stderr)
        return 2

    if args.root:
        roots = args.root
    else:
        incoming = set(g.constraints)
        roots = sorted(p for p in g.deps if p not in incoming) or sorted(g.deps)

    text, problems = report(g, roots)
    print(text)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
