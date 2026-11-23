#!/usr/bin/env python3
"""Integer-only certificates for global_trianglefree_potential.txt."""
from fractions import Fraction as F


def check(name: str, condition: bool) -> None:
    assert condition, name
    print(f"PASS {name}")


def main() -> None:
    checks = {
        "T1 leaf degree2 first": 2**35 * 51**36 > 100**36,
        "T1 leaf degree2 second": 2**103 * 3**72 > 8**72,
        "T1 leaf degree3 first": 2**17 * 21**18 > 40**18,
        "T1 leaf degree3 second": 2**5 > 3**3,
        "T1 mixed first": 3**12 > 2**19,
        "T1 mixed second": 9**6 > 2**19,
        "T1 cubic second": 2**65 * 29**36 > 100**36,
        "T1 cycle base4": 2 * 5**4 < 7**4,
        "T1 cycle base5": 5**6 < 7**5,
        "T1 cycle base6": 5**7 < 7**6,
        "T1 cycle growth": 7**72 < 5**72 * 2**35,
        "T1 degree4 first": 2**29 * 19**72 > 25**72,
        "T1 degree4 second": 2**17 * 6**8 > 25**8,
        "T1 degree10 first": 2**17 * 17**72 > 20**72,
        "T1 degree10 second": 2**23 * 3**8 > 20**8,
        "T2 degree4 first": 3**12 > 2**19,
        "T2 high first": 2 * 7**5 > 8**5,
        "T2 D12 x": 2**31 * 87**154 > 100**154,
        "T2 D12 y": 2**41 * 33**14 > 250**14,
        "T2 D12 z1": 2**65 * 13**22 > 100**22,
        "T2 D12 z2": 2**459 * 127**154 > 1000**154,
        "two-degree target1": 2**19 < 3**12,
        "two-degree target2": 2**122 < 3**77,
    }
    for name, condition in checks.items():
        check(name, condition)
    check("leaf sum2", F(51,100)+F(3,8)==F(177,200))
    check("leaf sum3", F(21,40)+F(1,3)<F(177,200))
    check("mixed coefficient", F(177,200)*F(3,4)+F(9,32)==F(189,200))
    check("cubic coefficient", F(189,200)*F(3,4)+F(29,100)==F(799,800))
    check("D12 first refinement", F(87,100)+F(127,1000)==F(997,1000))
    check("D12 second refinement", F(87,100)*F(997,1000)+F(13,100)
          ==F(99739,100000))
    check("D12 final coefficient", F(87,100)*F(99739,100000)+F(33,250)
          ==F(9997293,10000000)<1)
    matrix = [[0,1,0],[1,0,1],[1,0,0]]
    def mul(a,b):
        return [[sum(a[i][k]*b[k][j] for k in range(3))
                 for j in range(3)] for i in range(3)]
    cubic = mul(mul(matrix,matrix),matrix)
    check("cycle transition identity", cubic ==
          [[matrix[i][j]+int(i==j) for j in range(3)] for i in range(3)])


if __name__ == "__main__":
    main()
