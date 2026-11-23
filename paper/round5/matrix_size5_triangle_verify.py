#!/usr/bin/env python3
"""Integer transfer certificate for A={a}, P={0,p}, Q={0,p+a}."""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json

from matrix_mixed3_strip_verify import neighborhood, transpose, orbit


def interfaces():
    lower = [0] * 10
    J = [0] * 10
    D = [0] * 10
    for h, j, k in product(range(2), range(5), range(2)):
        J[5*h+j] |= 1 << (5*k+j)
        if k <= h:
            lower[5*h+j] |= 1 << (5*k+(j+1) % 5)
            D[5*h+j] |= 1 << (5*k+j)
        if h <= k:
            D[5*h+j] |= 1 << (5*k+(j+1) % 5)
    F = [a | b for a, b in zip(lower, transpose(lower))]
    return F, [J, D]


def verify_original(F, C):
    vertices = list(product(range(4), range(5), range(5)))

    def ambient(v):
        row, x, y = v
        return (2 if row in (0, 3) else 3,
                (x if row < 2 else -x) % 5,
                (y if row < 2 else -y) % 5,
                1 if row < 2 else 4)

    def add(x, y):
        return tuple((a+b) % 5 for a, b in zip(x, y))

    def sub(x, y):
        return tuple((a-b) % 5 for a, b in zip(x, y))

    # Q is -S_4; the actual fourth-layer tail is -p-a.
    seed = {(0,1,0,0), (1,0,0,0), (1,0,1,0),
            (4,0,0,0), (4,4,4,0)}
    assert not any(add(a, b) in seed for a in seed for b in seed)
    original = {v: set() for v in vertices}
    for u, v in combinations(vertices, 2):
        a, b = ambient(u), ambient(v)
        if add(a, b) in seed or sub(a, b) in seed or sub(b, a) in seed:
            original[u].add(v)
            original[v].add(u)
    loops = {add(a, b) for a in seed for b in seed}
    loops |= {sub(a, b) for a in seed for b in seed}
    loops |= {tuple(3*x % 5 for x in a) for a in seed}
    assert not any(ambient(v) in loops for v in vertices)
    assert all(len(adj) == 8 for adj in original.values())
    assert sum(map(len, original.values())) == 800
    # In fact each open neighborhood contains a P4 (three edges).
    assert all(sum(w in original[z] for z, w in combinations(adj, 2)) == 3
               for adj in original.values())

    def coord(vertex):
        row, x, y = vertex
        return 2*y+1-row % 2, 5*(row//2)+x

    assert len({coord(v) for v in vertices}) == 100
    strip = {(r, z): set() for r in range(10) for z in range(10)}

    def edge(v, w):
        strip[v].add(w)
        strip[w].add(v)

    for r, z, w in product(range(10), range(10), range(10)):
        if F[z] >> w & 1:
            edge((r, z), (r, w))
        if C[r % 2][z] >> w & 1:
            edge((r, z), ((r+1) % 10, w))
    assert {coord(v): {coord(w) for w in original[v]} for v in vertices} == strip
    print("PASS: original sum-free seed, no generic loops, 8-regular 100-point graph")
    print("PASS: every neighborhood has three edges; exact ten-slice strip isomorphism")


def build(F, C):
    independent = [s for s in range(1024) if not (neighborhood(F, s) & s)]
    assert len(independent) == 81
    deficit = {s: 1023 ^ (s | neighborhood(F, s)) for s in independent}
    out = [{s: neighborhood(c, s) for s in independent} for c in C]
    inc = [{s: neighborhood(transpose(c), s) for s in independent} for c in C]
    states = []
    for p in range(2):
        possible = {(s, deficit[s] & ~out[1-p][l]) for l in independent for s in independent if not (out[1-p][l] & s)}
        states.append(sorted((s, u) for s, u in possible if any(not (out[p][s] & t) and not (u & ~inc[p][t]) for t in independent)))
    index = [{s: i for i, s in enumerate(row)} for row in states]
    edges = []
    for p in range(2):
        phase = []
        for s, u in states[p]:
            successors = []
            for t in independent:
                target = (t, deficit[t] & ~out[p][s])
                if not (out[p][s] & t) and not (u & ~inc[p][t]) and target in index[1-p]:
                    successors.append(index[1-p][target])
            phase.append(successors)
        edges.append(phase)
    assert list(map(len, states)) == [305, 185]
    assert [sum(map(len, phase)) for phase in edges] == [3885, 480]
    return states, edges


def main():
    F, C = interfaces()
    verify_original(F, C)
    states, edges = build(F, C)
    # B follows two transitions, starting and ending in phase one.
    B = [Counter(j for middle in row for j in edges[0][middle]) for row in edges[1]]

    def apply(x):
        return [sum(m*x[j] for j, m in row.items()) for row in B]

    b1 = apply([1]*185)
    weight = apply(b1)
    bw = apply(weight)
    assert all(w > 0 for w in weight)
    assert all(b <= 64*w for b, w in zip(bw, weight))
    assert 185*64**5 == 198642237440 < 3**25

    index = {s: i for i, s in enumerate(states[1])}
    table = []
    for i, state in enumerate(states[1]):
        orb = orbit(state)
        assert len(set(orb)) == 5
        assert all(t in index for t in orb)
        assert all((b1[index[t]], weight[index[t]], bw[index[t]]) == (b1[i], weight[i], bw[i]) for t in orb)
        if state == min(orb):
            table.append([*state, b1[i], weight[i], bw[i]])
    assert len(table) == 37

    trace = 0
    for start in range(185):
        current = [0]*185
        current[start] = 1
        for k in range(5):
            nxt = [0]*185
            for i, row in enumerate(B):
                for j, multiplicity in row.items():
                    nxt[j] += current[i]*multiplicity
            current = nxt
        trace += current[start]
    assert trace == 428140310 < 185*64**5
    print("PASS: 305/185 active states; 3885/480 one-step transitions")
    print("PASS: positive integer weight B^2 1 satisfies B w <= 64 w")
    print("PASS: exact trace", trace, "<=", 185*64**5, "<", 3**25)

    root = Path(__file__).parent
    data = {"states": states, "transitions": edges,
            "two_step": [dict(row) for row in B], "orbit_table": table,
            "bound": 185*64**5, "exact_trace": trace}
    (root / "matrix_size5_triangle_certificate.json").write_text(json.dumps(data, separators=(",", ":")) + "\n")
    text = ["S U B1 w=B^2 1 Bw=B^3 1"]
    text += ["%4d %4d %5d %7d %9d" % tuple(row) for row in table]
    text += ["bound = " + str(185*64**5), "exact trace = " + str(trace)]
    (root / "matrix_size5_triangle_table.txt").write_text("\n".join(text) + "\n")


if __name__ == "__main__":
    main()
