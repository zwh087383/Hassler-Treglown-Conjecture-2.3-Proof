#!/usr/bin/env python3
"""Independent exact four-input entropy audit; no numerical optimization."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product

BLOCKED = {"P": (0, 1, 3, 3), "Q": (0, 3, 2, 3), "D": (0, 3, 3, 3)}
OUTPUT = (3, 1, 2, 0)
WP = (F(1), F(1, 2), F(1, 2), F(1, 2))

def check(name, colors, weights, expected, expected_parts):
    total = F(0)
    by_output = defaultdict(F)
    count = 0
    for values in product(range(4), repeat=4):
        if values[3] == 2 and any(values[:3]):
            continue
        blocked = 0
        for color, value in zip(colors, values):
            blocked |= BLOCKED[color][value]
        output = OUTPUT[blocked]
        ratio = F(1)
        for value, weight in zip(values, weights):
            ratio *= weight[value] / weight[output]
        total += ratio
        by_output[output] += ratio
        count += 1
    assert count == 193
    assert total == expected < 81
    assert dict(by_output) == expected_parts
    print(f"PASS {name}: {count} allowed inputs, exact sum {total} < 81")
    print(f"  Output subtotals: {dict(sorted(by_output.items()))}")

if __name__ == "__main__":
    check("A", "PPPQ", [WP] * 3 + [(F(1), F(1), F(1), F(1, 2))],
          F(1259, 16), {3: F(16), 0: F(571, 16), 2: F(8), 1: F(19)})
    check("C", "DPPQ", [(F(1),) * 4] + [WP] * 2
          + [(F(1), F(1, 2), F(1), F(1, 2))],
          F(279, 4), {3: F(8), 0: F(191, 4), 2: F(4), 1: F(10)})
