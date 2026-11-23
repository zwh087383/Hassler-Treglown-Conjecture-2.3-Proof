"""Exact local entropy certificates; independent of all MIS constructors."""
from fractions import Fraction as Q
from itertools import product

def swapped_output(inputs, colors):
    blocked_c = blocked_d = False
    for state, color in zip(inputs, colors):
        x, y = state & 1, (state >> 1) & 1
        if color == 'P':
            blocked_c |= bool(x or y); blocked_d |= bool(y)
        elif color == 'Q':
            blocked_c |= bool(x); blocked_d |= bool(x or y)
        elif color == 'D':
            blocked_c |= bool(x or y); blocked_d |= bool(x or y)
        else:
            raise ValueError(color)
    return int(not blocked_d) + 2*int(not blocked_c)

def certificate(kind):
    half=Q(1,2)
    if kind=='A':
        colors='PPPQ'
        weights=[(Q(1),half,half,half)]*3+[(Q(1),Q(1),Q(1),half)]
        expected=Q(1259,16)
    else:
        colors='DPPQ'
        weights=[(Q(1),)*4]+[(Q(1),half,half,half)]*2+[(Q(1),half,Q(1),half)]
        expected=Q(279,4)
    totals=[Q(0)]*4; counts=[0]*4
    for inputs in product(range(4),repeat=4):
        output=swapped_output(inputs,colors)
        assert (output==2)==(inputs[3]==2 and inputs[:3]==(0,0,0))
        if inputs[3]==2 and inputs[:3]!=(0,0,0):
            continue
        term=Q(1)
        for w,state in zip(weights,inputs):
            term*=w[state]/w[output]
        totals[output]+=term; counts[output]+=1
    assert sum(counts)==193
    assert sum(totals)==expected<3**4
    print('PASS',kind,'local counts',counts,'weighted output sums',list(map(str,totals)),
          'Z =',expected,'<',3**4)
    return expected

if __name__=='__main__':
    certificate('A'); certificate('C')
