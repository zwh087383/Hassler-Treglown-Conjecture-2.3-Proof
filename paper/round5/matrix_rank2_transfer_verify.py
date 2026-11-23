#!/usr/bin/env python3
"""Exact arithmetic certificate for the rank-two mixed three-seed matrix.

No external packages. Two separate constructions of the 83-state transition
matrix are compared: direct row choices, and a maximal-preimage criterion.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
FULL = 31


def rot(x):
    return ((x << 1) & FULL) | (x >> 4)


def dilate(x):
    return x | rot(x)


def interior(x):
    # Indices i for which i and i+1 both belong to x.
    return x & ((x >> 1) | ((x & 1) << 4))


def masks(word):
    p = sum((c == "2") << i for i, c in enumerate(word))
    q = sum((c != "0") << i for i, c in enumerate(word))
    return p, q


def word_of(state):
    p, q = state
    return "".join("2" if p >> i & 1 else "1" if q >> i & 1 else "0"
                   for i in range(5))


def canonical(word):
    return min(word[i:] + word[:i] for i in range(5))


def matrix_product(a, b):
    bt = list(zip(*b))
    return [[sum(x * y for x, y in zip(row, col)) for col in bt]
            for row in a]


def main():
    direct_states = {(dilate(x), dilate(x | y))
                     for x in range(32) for y in range(32)}
    word_states = set()
    for digits in product("012", repeat=5):
        word = "".join(digits)
        if all(word[i] <= max(word[(i-1) % 5], word[(i+1) % 5])
               for i in range(5)):
            word_states.add(masks(word))
    assert direct_states == word_states
    states = sorted(direct_states)
    assert len(states) == 83
    index = {s: i for i, s in enumerate(states)}
    size = len(states)

    # Construction 1: actual choices of the two row subsets in a layer.
    inputs = [(x | y, y, index[(dilate(x), dilate(x | y))])
              for x in range(32) for y in range(32)]
    a = [[0] * size for _ in states]
    for i, (p, q) in enumerate(states):
        transitions = {(t | p, y | q, j) for t, y, j in inputs}
        for u, v, j in transitions:
            a[i][j] += 1

    # Construction 2: test output pairs by an explicit maximal preimage.
    b = [[0] * size for _ in states]
    for i, (p, q) in enumerate(states):
        outputs = [(u, v) for u in range(32) if u & p == p
                   for v in range(32) if v & q == q]
        for j, (r, s) in enumerate(states):
            er, es = interior(r), interior(s)
            count = 0
            for u, v in outputs:
                t = u & es & (er | v)
                if (u & ~p & ~t) or (v & ~q & ~t):
                    continue
                if dilate(t) == s and dilate(t & er) == r:
                    count += 1
            b[i][j] = count
    assert a == b

    row_numerators = []
    for i, (p, q) in enumerate(states):
        row_numerators.append(sum(
            a[i][j] ** 2 * (1 << (5 + q.bit_count() - s.bit_count()))
            for j, (r, s) in enumerate(states)))
    total = sum(row_numerators)
    assert total == 1433053
    assert total < 32 * 3**10 == 1889568

    orbits = {}
    for i, state in enumerate(states):
        rep = canonical(word_of(state))
        orbits.setdefault(rep, []).append(i)
    assert len(orbits) == 19
    table = []
    for rep, ids in sorted(orbits.items()):
        entries = {row_numerators[i] for i in ids}
        assert len(entries) == 1
        row_num = entries.pop()
        table.append({"word": rep, "multiplicity": len(ids),
                      "row_numerator": row_num,
                      "orbit_numerator": len(ids) * row_num})
    assert sum(r["orbit_numerator"] for r in table) == total

    a2 = matrix_product(a, a)
    a3 = matrix_product(a2, a)
    trace5 = sum(a2[i][j] * a3[j][i]
                 for i in range(size) for j in range(size))
    assert trace5 == 142457592583
    assert trace5 < 3**25

    certificate = {
        "description": "Rank-two mixed three-seed transition certificate",
        "states": states, "matrix": a,
        "state_word_rule": "No strict cyclic local maximum in a word over 012",
        "norm_squared_numerator": total, "norm_squared_denominator": 32,
        "threshold_numerator": 32 * 3**10,
        "orbit_table": table, "trace5": trace5,
        "target": 3**25,
    }
    (HERE / "matrix_rank2_transfer_data.json").write_text(
        json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
    lines = ["word multiplicity row_numerator orbit_numerator"]
    lines.extend(f"{r['word']} {r['multiplicity']} {r['row_numerator']} "
                 f"{r['orbit_numerator']}" for r in table)
    lines.extend([f"TOTAL {total}", f"FROBENIUS_SQUARED {Fraction(total,32)}",
                  f"THRESHOLD {32*3**10}", f"TRACE5 {trace5}",
                  f"TARGET {3**25}"])
    output = "\n".join(lines) + "\n"
    (HERE / "matrix_rank2_transfer_table.txt").write_text(output, encoding="utf-8")
    print(output, end="")
    print("PASS: both transition constructions agree entry by entry.")


if __name__ == "__main__":
    main()
