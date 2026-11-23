"""Exact scalar certificates for zero_triple_proof.txt.
For c=log_2(3)/3 and beta=19/500, certify 2^(-k*c+j*beta)<p/q.
The universal exponent 1500 clears every denominator.
"""
from fractions import Fraction
checks=[
 ('leaf_first',2,1,1,2),
 ('leaf_second',3,1,7,20),
 ('mixed_exclude',1,2,3,4),
 ('mixed_include',4,4,13,50),
 ('pendant_include',4,2,1,4),
 ('triangle_two_first',3,2,9,25),
 ('cubic_include',4,5,4,15),
 ('cubic_none',5,10,21,100),
 ('degree4_exclude',1,3,10,13),
 ('degree4_include',5,11,3,13),
 ('degree8_exclude',1,7,21,25),
 ('degree8_include',9,55,4,25),
 ('degree9_exclude',1,8,6,7),
 ('degree9_include',10,65,1,7),
]
for name,k,j,p,q in checks:
 lhs=2**(57*j)*q**1500
 rhs=3**(500*k)*p**1500
 assert lhs<rhs,name
 print(name,'PASS')
assert 3**250<2**399
print('final_base PASS')
assert Fraction(17,20)*Fraction(3,4)+Fraction(13,50)<Fraction(19,20)
assert Fraction(19,20)*Fraction(3,4)+Fraction(4,15)==Fraction(47,48)
assert 3*Fraction(13,50)+Fraction(21,100)==Fraction(99,100)
print('All 15 strict integer certificates and all rational sums passed.')
