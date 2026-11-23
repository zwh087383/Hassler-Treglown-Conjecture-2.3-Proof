#!/usr/bin/env python3
"""Exact seven-input entropy certificate for P={0,u}, Q={v,w}.
Checks all 4^7 configurations, a separate four-row factorization,
the 500-vertex automorphism, and the Shearer cover multiplicity.
No floating point and no external packages.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
import json

C = (F(1), F(1,4), F(1), F(1))
A = (F(1), F(1,3), F(2,3), F(1,2))
B = (F(1), F(2,3), F(1,3), F(1,2))
G = (F(1), F(2,27), F(2,27), F(1,8))


def output(p0,p1,q0,q1):
    first = (p0 == p1 == 0) and not (q0 & 1) and not (q1 & 1)
    second = not (p0 & 2) and not (p1 & 2) and q0 == q1 == 0
    return int(second)+2*int(first)


def direct_output(p0,p1,q0,q1):
    covered0 = covered1 = False
    for z in (p0,p1):
        covered0 |= bool(z)
        covered1 |= bool(z & 2)
    for z in (q0,q1):
        covered0 |= bool(z & 1)
        covered1 |= bool(z)
    right0,right1 = not covered0,not covered1
    return int(right1)+2*int(right0)


def verify_weights():
    assert all(C[s]*A[s]**2*B[s]**4 == G[s]**2 for s in range(4))
    for z in product(range(4),repeat=4):
        assert output(*z) == direct_output(*z)
    rows=[]
    for shared in range(4):
        value=F(0)
        for p,q0,q1 in product(range(4),repeat=3):
            value += A[p]*B[q0]*B[q1]/G[output(shared,p,q0,q1)]
        rows.append(value)
    assert rows == [F(2629,72),F(775,24),F(125,8),F(125,8)]
    factored=sum(C[s]*rows[s]**2 for s in range(4))
    direct=F(0)
    configurations=0
    for z in product(range(4),repeat=7):
        y0=direct_output(z[0],z[1],z[3],z[4])
        y1=direct_output(z[0],z[2],z[5],z[6])
        value=C[z[0]]*A[z[1]]*A[z[2]]
        for i in (3,4,5,6):
            value *= B[z[i]]
        direct += value/(G[y0]*G[y1])
        configurations+=1
    assert configurations == 4**7 == 16384
    assert direct == factored == F(43177189,20736)
    assert 3**7*20736 == 45349632 > 43177189
    print("PASS: all four exact statewise balance identities")
    print("PASS: 256 direct NOR checks, 4-row factorization and 16,384-configuration sum")
    print("PASS: Z=43177189/20736 < 2187=3^7")
    return rows,direct


def verify_geometry():
    points=list(product(range(5),repeat=3))
    point_index={x:i for i,x in enumerate(points)}
    zero=(0,0,0)
    u,v,w=(1,0,0),(0,1,0),(0,0,1)
    def add(x,y):
        return tuple((a+b)%5 for a,b in zip(x,y))
    def neg(x):
        return tuple(-a%5 for a in x)
    def sub(x,y):
        return add(x,neg(y))
    shape=[zero,neg(u),u,neg(v),neg(w),sub(u,v),sub(u,w)]
    assert len(set(shape)) == 7
    cover=Counter(add(t,x) for t in points for x in shape)
    assert all(cover[x] == 7 for x in points)
    P={zero,u}; Q={v,w}; q=125
    adjacency=[set() for _ in range(4*q)]
    for i,x in enumerate(points):
        for left,right,translations in [(0,2,P|Q),(0,3,Q),(1,2,P),(1,3,P|Q)]:
            for t in translations:
                a=left*q+i; b=right*q+point_index[add(x,t)]
                adjacency[a].add(b); adjacency[b].add(a)
    assert all(len(row) == 6 for row in adjacency)
    target_block=(3,2,1,0)
    def phi(vertex):
        block,index=divmod(vertex,q)
        return target_block[block]*q+point_index[neg(points[index])]
    for i,row in enumerate(adjacency):
        assert {phi(j) for j in row} == adjacency[phi(i)]
    n0={sub(zero,t) for t in P|Q}; n1={sub(u,t) for t in P|Q}
    assert n0|n1 == set(shape) and n0&n1 == {zero}
    print("PASS: seven distinct coordinates and exact 7-fold translated cover")
    print("PASS: 500-vertex graph has the claimed side-swap/inversion automorphism")
    return shape


def verify_collision_reduction():
    points=list(product(range(5),repeat=3))
    zero=(0,0,0); u=(1,0,0)
    def add(x,y):
        return tuple((a+b)%5 for a,b in zip(x,y))
    def neg(x):
        return tuple(-a%5 for a in x)
    def sub(x,y):
        return add(x,neg(y))
    def shape(u,v,w):
        return [zero,neg(u),u,neg(v),neg(w),sub(u,v),sub(u,w)]
    line={(k,0,0) for k in range(5)}
    bad={neg(u),add(u,u)}
    checked=0
    for v,w in combinations([x for x in points if x not in (zero,u)],2):
        parallel=sub(w,v) in {u,neg(u)}
        collision=(v in bad or w in bad or parallel)
        assert (len(set(shape(u,v,w)))<7) == collision
        if collision and not parallel and not (v in line and w in line):
            if v not in bad:
                v,w=w,v
            assert v in line and w not in line
            z=sub(w,v)
            newv,neww=neg(v),sub(u,v)
            assert len(set(shape(z,newv,neww))) == 7
        checked+=1
    assert checked == 7503

    # Independent Boolean row computation of the parallel factorization.
    points=list(product(range(5),repeat=2)); ix={x:i for i,x in enumerate(points)}
    q=len(points); zero=(0,0); u=(1,0); t=(0,1)
    def matrix(P,Q):
        rows=[0]*(2*q)
        for i,x in enumerate(points):
            for left,right,T in [(0,0,P|Q),(0,1,Q),(1,0,P),(1,1,P|Q)]:
                for a in T:
                    rows[left*q+i] |= 1 << (right*q+ix[add(x,a)])
        return rows
    P={zero,u}; Q={add(x,t) for x in P}
    large=matrix(P,Q); small=matrix({zero},{t})
    product_rows=[]
    for block in range(2):
        for x in points:
            row=0
            for a in P:
                row |= small[block*q+ix[add(x,a)]]
            product_rows.append(row)
    assert product_rows == large
    assert 2*(1+5*3+10*9) == 212 < 3**5
    print("PASS: complete 7,503-case collision audit and color-swap reduction")
    print("PASS: Boolean parallel factorization and 212<3^5 paper constant")


if __name__ == "__main__":
    rows,z=verify_weights()
    shape=verify_geometry()
    verify_collision_reduction()
    data={"central_weight":[str(x) for x in C],
          "P_leaf_weight":[str(x) for x in A],
          "Q_leaf_weight":[str(x) for x in B],
          "output_weight":[str(x) for x in G],
          "conditional_sums":[str(x) for x in rows],
          "partition_sum":str(z),"threshold":3**7,
          "shape":shape,"configurations":4**7}
    Path(__file__).with_name("matrix_typeB_entropy_certificate.json").write_text(json.dumps(data,indent=2)+"\n")
