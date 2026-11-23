#!/usr/bin/env python3
"""Exact certificates for the triangle-free maximum-degree-eight extension."""

from fractions import Fraction


checks = [
    ("irregular_exclude", 8, 46, 55),
    ("irregular_include", 81, 9, 55),
    ("regular_all_excluded", 32, 489, 1000),
    ("regular_include_0", 80, 21, 125),
    ("regular_include_1", 89, 137, 1000),
    ("regular_include_2", 98, 14, 125),
    ("regular_include_3", 107, 23, 250),
]


def main():
    for name, exponent, numerator, denominator in checks:
        assert denominator**31 < numerator**31 * 2**exponent, name
        print(f"PASS {name}")
    assert Fraction(46, 55) + Fraction(9, 55) == 1
    coefficient = sum(Fraction(p, q) for _, _, p, q in checks[2:])
    assert coefficient == Fraction(499, 500) < 1
    assert 2**49 < 3**31
    print("PASS four-stage coefficient < 499/500 and final target comparison")


if __name__ == "__main__":
    main()
