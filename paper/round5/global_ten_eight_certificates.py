#!/usr/bin/env python3
"""Exact scalar checks for the mixed generic 10/8 proof."""
from fractions import Fraction as F


def main() -> None:
    checks = {
        "beta allowed": 3**25 < 2**42,
        "residual max8 first": 3*5**6 > 6**6,
        "residual max8 second": 3**71 > 6**42,
        "residual max9 first": 3*171**7 > 200**7,
        "residual max9 second": 3**37*29**21 > 200**21,
        "strong deficit first": 3**5*87741**42 > 100000**42,
        "strong deficit second": 3**27*12019**14 > 100000**14,
        "partner exclude precise": 3*8327**6 > 10000**6,
        "partner include": 3**5*1603**3 > 10000**3,
        "positive deficit root include": 3**79*127**42 > 1000**42,
        "root exclude": 3**5*8775**42 > 10000**42,
        "root include": 3**13*13**7 > 100**7,
        "partner exclude convenient": 3*833**6 > 1000**6,
        "eta sum": F(87741,100000)+F(12019,100000)==F(9976,10000),
        "partner sum": F(8327,10000)+F(1603,10000)==F(993,1000),
        "positive deficit coefficient": F(8775,10000)*F(993,1000)
                       +F(127,1000)<1,
        "whole-graph coefficient": F(8775,10000)*(
                       F(833,1000)*F(9976,10000)+F(1603,10000))
                       +F(13,100)==F(249966613,250000000)<1,
    }
    for name, condition in checks.items():
        assert condition, name
        print(f"PASS {name}")


if __name__ == "__main__":
    main()
