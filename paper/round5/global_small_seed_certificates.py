#!/usr/bin/env python3
"""Integer certificates for the size-six/seven generic-seed reduction."""
from fractions import Fraction as F


def main() -> None:
    checks = {
        "2A beta allowed": 3**25 < 2**51,
        "2A residual degree9 first": 3**3 * 5**17 > 6**17,
        "2A residual degree9 second": 3**33 > 6**17,
        "2A high-degree first": 2**51 > 3**32,
        "2B beta allowed": 3**5 < 2**9,
        "2B residual degree9 first": 3**7 * 17**45 > 20**45,
        "2B residual degree9 second": 3**124 > 20**45,
        "2B degree10 first": 3**2 * 13**15 > 15**15,
        "2B degree10 second": 3**83 * 2**45 > 15**45,
    }
    for name, condition in checks.items():
        assert condition, name
        print(f"PASS {name}")
    for d in range(10,13):
        assert d*d-(d-9)*(d-6)==15*d-54
        assert F(18-d,17)>=F(6,17)
        assert F(3*d+72,17)>=6
    print("PASS degree-cap polynomial identities")


if __name__ == "__main__":
    main()
