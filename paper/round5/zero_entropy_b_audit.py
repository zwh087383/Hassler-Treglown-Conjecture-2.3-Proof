#!/usr/bin/env python3
"""Independent mask-based enumeration of the type-B entropy certificate."""
from fractions import Fraction as F
from itertools import product

central = (F(1), F(1, 4), F(1), F(1))
pleaf = (F(1), F(1, 3), F(2, 3), F(1, 2))
qleaf = (F(1), F(2, 3), F(1, 3), F(1, 2))
outweight = (F(1), F(2, 27), F(2, 27), F(1, 8))
pmask, qmask = (0, 1, 3, 3), (0, 3, 2, 3)
swap_unblocked = (3, 1, 2, 0)

def nor(a, b, c, d):
    return swap_unblocked[pmask[a] | pmask[b] | qmask[c] | qmask[d]]

def main():
    balance = [central[s] * pleaf[s]**2 * qleaf[s]**4 for s in range(4)]
    assert balance == [F(1), F(4, 729), F(4, 729), F(1, 64)]
    assert balance == [x*x for x in outweight]
    subtotals = []
    for s in range(4):
        subtotal = F(0)
        for a, b, c in product(range(4), repeat=3):
            subtotal += pleaf[a] * qleaf[b] * qleaf[c] / outweight[nor(s, a, b, c)]
        subtotals.append(subtotal)
    assert subtotals == [F(2629, 72), F(775, 24), F(125, 8), F(125, 8)]
    direct = F(0)
    for z in product(range(4), repeat=7):
        f0 = nor(z[0], z[1], z[3], z[4])
        f1 = nor(z[0], z[2], z[5], z[6])
        weight = central[z[0]] * pleaf[z[1]] * pleaf[z[2]]
        for j in (3, 4, 5, 6):
            weight *= qleaf[z[j]]
        direct += weight / (outweight[f0] * outweight[f1])
    factored = sum(central[s] * subtotals[s]**2 for s in range(4))
    assert direct == factored == F(43177189, 20736)
    assert 43177189 < 3**7 * 20736 == 45349632
    print("PASS statewise balance identities")
    print("PASS four independent conditional sums:", subtotals)
    print("PASS all 16,384 inputs:", direct, "<", 3**7)

if __name__ == "__main__":
    main()
