#!/usr/bin/env python3
"""Exact arithmetic audit of round-5 general-graph potential constants.

This verifies numerical inequalities only, not the full graph induction,
and is not a Lean formalization. No floating-point arithmetic is used.
"""
from fractions import Fraction
from math import lcm


def term_less(p: int, q: Fraction, r: int, s: int) -> bool:
    """Certify 2^(-p*c+q) < r/s, where c=log_2(3)/3."""
    q = Fraction(q)
    assert p >= 0 and q >= 0 and r > 0 and s > 0
    denominator = lcm(3, q.denominator)
    return (3 ** (p * denominator // 3) * r ** denominator
            > 2 ** (q.numerator * (denominator // q.denominator))
            * s ** denominator)


def check(name: str, condition: bool) -> None:
    assert condition, name
    print(f"PASS {name}")


def low_degree_checks(beta: Fraction, prefix: str) -> None:
    for name, p, multiple, r, s in [
        ("leaf first", 2, 1, 1, 2),
        ("leaf second", 3, 1, 7, 20),
        ("degree-three deletion", 1, 2, 3, 4),
        ("mixed closed neighborhood", 4, 4, 13, 50),
        ("pendant triangle / K4", 4, 2, 1, 4),
        ("cubic closed neighborhood", 4, 5, 4, 15),
    ]:
        check(f"{prefix}: {name}", term_less(p, multiple * beta, r, s))


def main() -> None:
    beta0 = Fraction(27, 800)
    master_beta = Fraction(1, 25)
    low_degree_checks(master_beta, "master beta=1/25")
    check("master degree-four first", term_less(1, 3 * master_beta, 19, 25))
    check("master degree-four second", term_less(5, 11 * master_beta, 6, 25))
    check("master degree-four sum", Fraction(19, 25) + Fraction(6, 25) == 1)
    check("degree-four first", term_less(1, 3 * beta0, 3, 4))
    check("degree-four second", term_less(5, 11 * beta0, 1, 4))
    check("D=10 first", term_less(1, Fraction(243, 800), 6, 7))
    check("D=10 second", term_less(11, Fraction(2403, 800), 1, 7))
    low_degree_checks(beta0, "beta=27/800")
    check("leaf coefficient", Fraction(1, 2) + Fraction(7, 20) == Fraction(17, 20))
    check("mixed coefficient", Fraction(17, 20) * Fraction(3, 4)
          + Fraction(13, 50) < Fraction(19, 20))
    check("pendant coefficient", 2 * Fraction(7, 20) + Fraction(1, 4)
          == Fraction(19, 20))
    check("cubic coefficient", Fraction(19, 20) * Fraction(3, 4)
          + Fraction(4, 15) == Fraction(47, 48))
    check("regular exponent below target", 3 ** 50 < 2 ** 81)
    check("D=22 beta allowed", Fraction(3, 160) < beta0)
    check("D=22 first", term_less(1, Fraction(63, 160), 911, 1000))
    check("D=22 second", term_less(23, Fraction(1383, 160), 89, 1000))
    check("D=22 coefficient", Fraction(911, 1000) + Fraction(89, 1000) == 1)
    check("two-degree exponent below target", 3 ** 160 < 2 ** 261)
    check("target-adapted beta allowed", 3 ** 25 < 2 ** 48)
    check("target-adapted (10,10) first", 3**7 * 6**48 > 7**48)
    check("target-adapted (10,10) second", 3**87 > 7**48)
    check("target-adapted (17,10) first", 3**7 * 17**69 > 19**69)
    check("target-adapted (17,10) second", 3**143 * 2**69 > 19**69)
    low_degree_checks(Fraction(19, 500), "special beta=19/500")


if __name__ == "__main__":
    main()
