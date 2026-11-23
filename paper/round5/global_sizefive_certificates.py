#!/usr/bin/env python3
"""Exact numerical checks for global_sizefive_progress.txt."""
from fractions import Fraction as F


def main() -> None:
    checks = {
        "9/6 and 9/7 exclude": 2**7 * 107**31 > 125**31,
        "9/6 and 9/7 include": 2**87 * 18**31 > 125**31,
        "9/6 worst exponent": 2**49 < 3**31,
        "nine-regular beta allowed": 3**25 < 2**42,
        "residual eight first": 3 * 5**6 > 6**6,
        "residual eight second": 3**71 > 6**42,
        "six neighborhood edges first": 3 * 6**7 > 7**7,
        "six neighborhood edges second": 3**25 > 7**14,
        "two low neighbors first": 3 * 171**7 > 200**7,
        "two low neighbors second": 3**37 * 29**21 > 200**21,
        "partner degree8 second": 3**12 * 47**7 > 300**7,
        "partner degree9 second": 3**13 * 27**7 > 200**7,
        "root include": 3**12 * 153**7 > 1000**7,
        "partner degree8 sum": F(5,6)+F(47,300)==F(99,100),
        "partner degree9 sum": F(171,200)+F(27,200)==F(99,100),
        "root sum": F(99,100)*F(171,200)+F(153,1000)
                    ==F(19989,20000)<1,
    }
    for name, condition in checks.items():
        assert condition, name
        print(f"PASS {name}")


if __name__ == "__main__":
    main()
