#!/usr/bin/env python3
"""Integer certificates for both rank-two one-zero/two-nonzero link blocks.

No numerical linear algebra and no nonstandard packages are used.
The transfer construction is checked against the original group equations.
"""
from collections import Counter
from itertools import product
import json
from pathlib import Path

from matrix_mixed3_verify import graph


def transpose(C):
    n = len(C)
    result = [0] * n
    for i in range(n):
        for j in range(n):
            if C[i] >> j & 1:
                result[j] |= 1 << i
    return result


def neighborhood(C, s):
    result = 0
    while s:
        bit = s & -s
        result |= C[bit.bit_length() - 1]
        s ^= bit
    return result


def interface(upper=False):
    C = [0] * 10
    for t, j, u in product(range(2), range(5), range(2)):
        if (t <= u) if upper else (u <= t):
            C[5*t+j] |= 1 << (5*u+(j+1) % 5)
    return C


def rotate(mask):
    def r5(a):
        return ((a << 1) & 31) | (a >> 4)
    return r5(mask & 31) | (r5(mask >> 5) << 5)


def orbit(state):
    result = []
    for _ in range(5):
        result.append(state)
        state = tuple(map(rotate, state))
    return result


def verify_strip_isomorphism(case, C, F):
    vertices, original_adj, _ = graph(case)
    offsets = (0, 4, 0, 4) if case == "same" else (0, 1, 0, 1)

    def coord(vertex):
        row, (x, y) = vertex
        j = (x+2*y+offsets[row]) % 5
        if case == "opposite":
            r = 2*y+(row % 2)
            t = row // 2
        else:
            r = 2*y+(1-row % 2)
            t = row // 2
        return r, 5*t+j

    assert len({coord(v) for v in vertices}) == 100
    strip_adj = {(r, z): set() for r in range(10) for z in range(10)}

    def edge(v, w):
        strip_adj[v].add(w)
        strip_adj[w].add(v)

    for r in range(10):
        for z in range(10):
            for w in range(10):
                if F[z] >> w & 1:
                    edge((r, z), (r, w))
                if C[r % len(C)][z] >> w & 1:
                    edge((r, z), ((r+1) % 10, w))
    assert {coord(v): {coord(w) for w in original_adj[v]} for v in vertices} == strip_adj
    print("PASS", case, "100-point link is isomorphic to the asserted ten-slice strip")


def build(case):
    lower, upper = interface(), interface(True)
    F = [a | b for a, b in zip(lower, transpose(lower))]
    assert all(row.bit_count() == 3 for row in F)
    C = [lower] if case == "opposite" else [upper, lower]
    phases = len(C)
    verify_strip_isomorphism(case, C, F)
    independent = [s for s in range(1024) if not (neighborhood(F, s) & s)]
    assert len(independent) == 81
    D = {s: 1023 ^ (s | neighborhood(F, s)) for s in independent}
    out = [{s: neighborhood(c, s) for s in independent} for c in C]
    inc = [{s: neighborhood(transpose(c), s) for s in independent} for c in C]
    states = []
    for phase in range(phases):
        prev = (phase - 1) % phases
        possible = {(s, D[s] & ~out[prev][l]) for s in independent for l in independent if not (out[prev][l] & s)}
        live = sorted((s, u) for s, u in possible if any(not (out[phase][s] & t) and not (u & ~inc[phase][t]) for t in independent))
        states.append(live)
    index = [{state: i for i, state in enumerate(s)} for s in states]
    transitions = []
    for phase in range(phases):
        nxt = (phase + 1) % phases
        edges = []
        for s, u in states[phase]:
            successors = []
            for t in independent:
                target = (t, D[t] & ~out[phase][s])
                if not (out[phase][s] & t) and not (u & ~inc[phase][t]) and target in index[nxt]:
                    successors.append(index[nxt][target])
            edges.append(successors)
        transitions.append(edges)
    assert list(map(len, states)) == ([120] if case == "opposite" else [105, 105])
    assert [sum(map(len, e)) for e in transitions] == ([725] if case == "opposite" else [710, 710])
    return states, transitions


def apply(transitions, values):
    phases = len(transitions)
    return [[sum(values[(p+1) % phases][j] for j in row) for row in transitions[p]] for p in range(phases)]


def certify(case):
    states, transitions = build(case)
    one = [[1] * len(s) for s in states]
    degree = apply(transitions, one)
    w = apply(transitions, degree)
    aw = apply(transitions, w)
    assert all(value > 0 for row in w for value in row)
    assert all(a <= 8*b for ar, wr in zip(aw, w) for a, b in zip(ar, wr))
    n = len(states[0])
    assert n * 8**10 < 3**25
    table = []
    for p, row in enumerate(states):
        lookup = {state: i for i, state in enumerate(row)}
        for i, state in enumerate(row):
            orb = orbit(state)
            assert len(set(orb)) == 5
            assert all(t in lookup for t in orb)
            assert all((degree[p][lookup[t]], w[p][lookup[t]], aw[p][lookup[t]]) == (degree[p][i], w[p][i], aw[p][i]) for t in orb)
            if state == min(orb):
                table.append([p, *state, degree[p][i], w[p][i], aw[p][i]])
    assert len(table) == (24 if case == "opposite" else 42)

    # A second, stronger certificate: exact ten-step diagonal path counts.
    # All values and operations are nonnegative integers.
    trace = 0
    for start in range(n):
        current = [0] * n
        current[start] = 1
        for k in range(10):
            p = k % len(states)
            nxt = [0] * len(states[(p+1) % len(states)])
            for i, row in enumerate(transitions[p]):
                for j in row:
                    nxt[j] += current[i]
            current = nxt
        trace += current[start]
    assert trace <= n*8**10 < 3**25
    print("PASS", case, "positive integer weight A^2 1 satisfies A w <= 8 w")
    print("PASS", case, "trace", trace, "<=", n*8**10, "<", 3**25)
    return {"case": case, "states": states, "transitions": transitions,
            "orbit_table": table, "bound": n*8**10, "exact_trace": trace}


if __name__ == "__main__":
    results = [certify(case) for case in ("opposite", "same")]
    root = Path(__file__).parent
    (root / "matrix_mixed3_strip_certificate.json").write_text(json.dumps(results, separators=(",", ":")) + "\n")
    table_text = []
    for result in results:
        table_text += [result["case"], "phase   S    U   outdeg   w=A^2 1   Aw=A^3 1"]
        table_text += ["%5d %4d %4d %8d %9d %10d" % tuple(row) for row in result["orbit_table"]]
        table_text += ["exact trace = " + str(result["exact_trace"]), "bound = " + str(result["bound"]), ""]
    (root / "matrix_mixed3_strip_table.txt").write_text("\n".join(table_text) + "\n")
