#!/usr/bin/env python3
"""Exact certificates for zero_eight_potential_audit.txt; standard library only."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product


EXPONENTIAL_CERTIFICATES = [
    ("degree5_exclude", 11, 79, 100),
    ("degree5_include", 71, 21, 100),
    ("degree6_exclude", 10, 81, 100),
    ("degree6_include", 76, 19, 100),
    ("degree7_exclude", 9, 41, 50),
    ("degree7_include", 79, 9, 50),
    ("degree8_exclude", 8, 21, 25),
    ("degree8_include", 83, 4, 25),
    ("degree4_exclude", 12, 49, 64),
    ("degree4_irregular_include", 65, 15, 64),
    ("degree4_regular_include", 64, 1, 4),
    ("leaf_exclude", 29, 21, 40),
    ("leaf_include", 44, 3, 8),
    ("degree3_exclude", 13, 3, 4),
    ("degree3_mixed_include", 56, 3, 10),
    ("degree3_regular_include", 55, 3, 10),
    ("ordered_degree3_0", 42, 2, 5),
    ("ordered_degree3_1", 56, 29, 100),
    ("ordered_degree3_2", 70, 21, 100),
    ("ordered_degree4_0", 52, 8, 25),
    ("ordered_degree4_1", 65, 6, 25),
    ("ordered_degree4_2", 78, 9, 50),
    ("ordered_degree4_3", 91, 27, 200),
]


def verify_constants():
    for name, a, p, q in EXPONENTIAL_CERTIFICATES:
        assert q**31 < p**31 * 2**a, name
    assert Fraction(79, 100) + Fraction(21, 100) == 1
    assert Fraction(81, 100) + Fraction(19, 100) == 1
    assert Fraction(41, 50) + Fraction(9, 50) == 1
    assert Fraction(21, 25) + Fraction(4, 25) == 1
    assert Fraction(49, 64) + Fraction(15, 64) == 1
    assert Fraction(21, 40) + Fraction(3, 8) == Fraction(9, 10)
    assert Fraction(2, 5) + Fraction(29, 100) + Fraction(21, 100) == Fraction(9, 10)
    assert sum(map(Fraction, ["8/25", "6/25", "9/50", "27/200"])) == Fraction(7, 8)
    assert Fraction(9, 10) * Fraction(3, 4) + Fraction(3, 10) == Fraction(39, 40) < 1
    assert Fraction(7, 8) * Fraction(49, 64) + Fraction(1, 4) == Fraction(471, 512) < 1
    for length, count in [(4, 2), (5, 5), (6, 5)]:
        assert count * 18**length < 25**length
    assert Fraction(18, 25)**2 + Fraction(18, 25)**3 == Fraction(13932, 15625) < 1
    assert 25**31 < 18**31 * 2**15
    assert 2**49 < 3**31
    print(f"PASS: {len(EXPONENTIAL_CERTIFICATES)} exponential integer certificates")
    print("PASS: rational branch sums, cycle estimates, and target comparison")


def add_mod(u, v):
    return tuple((x + y) % 5 for x, y in zip(u, v))


def sub_mod(u, v):
    return tuple((x - y) % 5 for x, y in zip(u, v))


def verify_generic_graph():
    points = list(product(range(5), repeat=2))
    vertices = [(row, x) for row in range(4) for x in points]
    row_adj = {v: set() for v in vertices}

    def edge(u, v):
        assert u != v
        row_adj[u].add(v)
        row_adj[v].add(u)

    e1, e2 = (1, 0), (0, 1)
    for row, x in vertices:
        for e in (e1, e2):
            edge((row, x), (row, add_mod(x, e)))
    for x in points:
        for e in (e1, e2):
            edge((0, x), (2, sub_mod(x, e)))
            edge((1, x), (3, sub_mod(x, e)))
        edge((0, x), (1, x))
        edge((1, x), (2, x))
        edge((2, x), (3, x))

    # Independent reconstruction in G=F_5 x F_5^3, with K in the first
    # two tail coordinates and t=(0,0,1) in the third tail coordinate.
    def ambient(v):
        row, (x, y) = v
        if row == 0:
            return (2, x, y, 1)
        if row == 1:
            return (3, x, y, 1)
        if row == 2:
            return (3, -x % 5, -y % 5, 4)
        return (2, -x % 5, -y % 5, 4)

    seed = {(0, 1, 0, 0), (0, 0, 1, 0), (1, 0, 0, 0)}
    loops = {add_mod(s, t) for s in seed for t in seed}
    loops |= {sub_mod(s, t) for s in seed for t in seed}
    loops |= {tuple(3 * coordinate % 5 for coordinate in s) for s in seed}
    original_adj = {v: set() for v in vertices}
    for v in vertices:
        assert ambient(v) not in loops
    for u, v in combinations(vertices, 2):
        au, av = ambient(u), ambient(v)
        if add_mod(au, av) in seed or sub_mod(au, av) in seed or sub_mod(av, au) in seed:
            original_adj[u].add(v)
            original_adj[v].add(u)
    assert original_adj == row_adj

    degrees = {v: len(row_adj[v]) for v in vertices}
    assert Counter(degrees.values()) == Counter({7: 50, 8: 50})
    assert sum(degrees.values()) // 2 == 375
    for v in vertices:
        if degrees[v] == 8:
            assert sum(degrees[u] == 7 for u in row_adj[v]) == 3
        for u in row_adj[v]:
            assert not (row_adj[v] & row_adj[u])
    assert Fraction(16 * len(vertices) - sum(degrees.values()) // 2, 31) == Fraction(1225, 31)
    print("PASS: original link and four-row adjacency agree on all 100 vertices")
    print("PASS: 50 vertices of each degree 7/8; 375 edges; each degree-8 vertex has exactly 3 degree-7 neighbors")
    print("PASS: loop-free, triangle-free, and exact potential 1225/31")


if __name__ == "__main__":
    verify_constants()
    verify_generic_graph()
