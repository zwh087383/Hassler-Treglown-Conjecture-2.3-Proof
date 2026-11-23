#!/usr/bin/env python3
"""Independent original-link reconstruction for the two remaining rank-two triples."""
from collections import Counter
from itertools import combinations, product


def add(x, y):
    return tuple((a + b) % 5 for a, b in zip(x, y))


def sub(x, y):
    return tuple((a - b) % 5 for a, b in zip(x, y))


def graph(case):
    points = list(product(range(5), repeat=2))
    verts = [(r, x) for r in range(4) for x in points]
    adj = {v: set() for v in verts}

    def edge(v, w):
        assert v != w
        adj[v].add(w)
        adj[w].add(v)

    u, v = (1, 0), (0, 1)
    for r, x in verts:
        edge((r, x), (r, add(x, u)))
    for x in points:
        edge((0, x), (2, sub(x, u)))
        edge((1, x), (3, sub(x, u)))
        for p in ((0, 0), v) if case == "same" else ((0, 0),):
            edge((0, x), (1, add(x, p)))
            edge((2, x), (3, add(x, p)))
            edge((1, x), (2, sub(x, p)))
        if case == "opposite":
            edge((0, x), (1, sub(x, v)))
            edge((2, x), (3, sub(x, v)))
            edge((0, x), (3, sub(x, v)))

    def ambient(vertex):
        r, (x, y) = vertex
        if r == 0:
            return (2, x, y, 1)
        if r == 1:
            return (3, x, y, 1)
        if r == 2:
            return (3, -x % 5, -y % 5, 4)
        return (2, -x % 5, -y % 5, 4)

    seed = {(0, 1, 0, 0), (1, 0, 0, 0),
            (1, 0, 1, 0) if case == "same" else (4, 0, 1, 0)}
    original = {v: set() for v in verts}
    for x, y in combinations(verts, 2):
        ax, ay = ambient(x), ambient(y)
        if add(ax, ay) in seed or sub(ax, ay) in seed or sub(ay, ax) in seed:
            original[x].add(y)
            original[y].add(x)
    assert adj == original
    for x in verts:
        for y in adj[x]:
            assert not (adj[x] & adj[y])
    deg = {x: len(adj[x]) for x in verts}
    assert Counter(deg.values()) == (Counter({5: 50, 7: 50}) if case == "same" else Counter({6: 100}))
    if case == "same":
        assert all(sum(deg[y] == 5 for y in adj[x]) == 3 for x in verts if deg[x] == 7)

    offsets = (0, 4, 0, 4) if case == "same" else (0, 1, 0, 1)

    def layer(vertex):
        r, (x, y) = vertex
        return ((x + 2 * y + offsets[r]) % 5, 5 * r + y)

    interfaces = [[0] * 20 for _ in range(5)]
    for x in verts:
        lx, ix = layer(x)
        for y in adj[x]:
            ly, iy = layer(y)
            assert (ly - lx) % 5 in (1, 4)
            if (ly - lx) % 5 == 1:
                interfaces[lx][ix] |= 1 << iy
    assert all(mat == interfaces[0] for mat in interfaces)
    expected = {
        "same": [65,130,260,520,48,1057,2114,4228,8456,16912,66625,133250,266500,533000,49200,33824,67648,135296,270592,541184],
        "opposite": [33,66,132,264,528,34,68,136,272,513,33825,67650,135300,270600,541200,34850,69700,139400,278800,525825]
    }
    assert interfaces[0] == expected[case]
    print("PASS", case, "original adjacency, triangle-free, degree distribution", sorted(Counter(deg.values()).items()), "and five identical interfaces")
    return verts, adj, interfaces[0]


if __name__ == "__main__":
    graph("same")
    graph("opposite")
