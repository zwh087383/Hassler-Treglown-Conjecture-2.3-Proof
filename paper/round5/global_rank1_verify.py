#!/usr/bin/env python3
"""Check explicit depth-six/seven Moon--Moser certificates for 20-point links."""
from collections import Counter

CASES = [
    ("86_r2", {1,4}, {0,2}, set(), {0:20,4:1,7:1,8:1,13:1}, 162),
    ("86_r3", {1,4}, {0,3}, set(), {0:20,4:1,7:1,8:1,13:1}, 162),
    ("76_r2", {1}, {0,2}, {0}, {0:17,2:1,3:1,6:1,8:1,14:1}, 211),
    ("76_r3", {1}, {0,3}, {0}, {0:22,2:2,4:3,8:2,14:1}, 236),
    ("87_r3", {1}, {0,3}, {1}, {0:14,2:7,3:1,7:2,14:1}, 217),
    ("88_r2", {1}, {0,2}, {0,3}, {0:14,2:5,4:1,5:1,6:1,14:1}, 205),
    ("same3_r2", {1}, {0,2}, set(), {0:21,2:2,4:1,5:1,9:2,13:1}, 197),
    ("same3_r3", {1}, {0,3}, set(), {0:20,2:3,3:1,4:1,9:2,13:1}, 195),
    ("opposite3_q1", {1}, {0}, {1}, {0:40,2:7,4:3,6:2,7:1,8:1,13:1}, 222),
    ("opposite3_q2", {1}, {0}, {2}, {0:42,2:2,3:5,6:2,7:1,12:1}, 172),
    ("opposite3_q3", {1}, {0}, {3}, {0:15,3:3,6:1,8:2,14:1}, 231),
]
DEPTH = {"opposite3_q1":7, "opposite3_q2":7}


def generic_graph(A, P, Q):
    vertices = [(s,r,x) for s in range(2) for r in range(2) for x in range(5)]
    adjacency = [0]*20
    U = P|Q
    directions = A|{(-a)%5 for a in A}
    for i,(s,r,x) in enumerate(vertices):
        for j in range(i):
            t,k,y = vertices[j]
            if s == t:
                edge = ((x-y)%5 in directions if r == k else
                        ((x-y)%5 in A if r == 0 else (y-x)%5 in A))
            else:
                labels = Q if r == k == 0 else P if r == k == 1 else U
                edge = (-x-y)%5 in labels
            if edge:
                adjacency[i] |= 1<<j
                adjacency[j] |= 1<<i
    return adjacency


def direct_link_graph(A, P, Q):
    add = lambda u,v: tuple((a+b)%5 for a,b in zip(u,v))
    neg = lambda u: tuple((-a)%5 for a in u)
    S = {(0,a,0) for a in A}|{(1,p,0) for p in P}|{(4,(-q)%5,0) for q in Q}
    assert all(add(u,v) not in S for u in S for v in S)
    vertices = []
    for sign in (1,4):
        for row in (0,1):
            for x in range(5):
                vertices.append((2,x,sign) if row == 0 else (3,(-x)%5,(-sign)%5))
    adjacency = [0]*20
    for i,u in enumerate(vertices):
        for j in range(i):
            v = vertices[j]
            if add(u,v) in S or add(u,neg(v)) in S or add(v,neg(u)) in S:
                adjacency[i] |= 1<<j
                adjacency[j] |= 1<<i
    return adjacency


def moon_moser(n):
    if n <= 1:
        return 1
    if n%3 == 0:
        return 3**(n//3)
    if n%3 == 1:
        return 4*3**((n-4)//3)
    return 2*3**((n-2)//3)


def histogram(adjacency, mask, depth):
    mask = sum(1<<i for i in range(20) if mask>>i&1 and adjacency[i]&mask)
    if not mask:
        return Counter({0:1})
    if depth == 0:
        return Counter({mask.bit_count():1})
    v = max((i for i in range(20) if mask>>i&1),
            key=lambda i: ((adjacency[i]&mask).bit_count(),-i))
    return (histogram(adjacency, mask&~(1<<v), depth-1)
            +histogram(adjacency, mask&~((1<<v)|adjacency[v]), depth-1))


def main():
    for name,A,P,Q,expected,upper in CASES:
        adjacency = generic_graph(A,P,Q)
        assert adjacency == direct_link_graph(A,P,Q), name
        depth = DEPTH.get(name,6)
        actual = histogram(adjacency,(1<<20)-1,depth)
        assert dict(actual) == expected, (name,actual)
        result = sum(moon_moser(n)*count for n,count in actual.items())
        assert result == upper < 3**5, name
        print(f"PASS {name}, depth={depth}: {dict(sorted(actual.items()))}, upper={upper}<243")


if __name__ == "__main__":
    main()
