#!/usr/bin/env python3
"""Short integer strip certificates for three remaining mixed size-four models."""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json

from matrix_mixed3_strip_verify import neighborhood, transpose, orbit
from matrix_size5_triangle_verify import interfaces


def model(name):
    F, (J, D) = interfaces()
    lower = [0]*10
    for h, j, k in product(range(2), range(5), range(2)):
        if k <= h:
            lower[5*h+j] |= 1 << (5*k+j)
    if name == "nested":
        seed = {(0,1,0,0), (1,0,0,0), (1,0,1,0), (4,0,0,0)}
        return seed, F, [J, lower], 1, 40, Counter({6:50, 7:50})
    if name == "triangle":
        seed = {(0,1,0,0), (1,0,0,0), (1,0,1,0), (4,4,0,0)}
        return seed, F, [transpose(D), lower], 0, 65, Counter({7:50, 8:50})
    assert name == "twozero"
    seed = {(0,1,0,0), (0,4,0,0), (1,0,0,0), (1,0,1,0)}
    F = [0]*10
    for h, j, k, shift in product(range(2), range(5), range(2), (-1,1)):
        F[5*h+j] |= 1 << (5*k+(j+shift) % 5)
    return seed, F, [transpose(lower), lower], 0, 36, Counter({6:50, 8:50})


def verify_original(seed, F, C, degrees):
    vertices = list(product(range(4), range(5), range(5)))

    def ambient(v):
        row, x, y = v
        return (2 if row in (0,3) else 3,
                (x if row < 2 else -x) % 5,
                (y if row < 2 else -y) % 5,
                1 if row < 2 else 4)

    def add(x, y):
        return tuple((a+b) % 5 for a, b in zip(x, y))

    def sub(x, y):
        return tuple((a-b) % 5 for a, b in zip(x, y))

    assert not any(add(a,b) in seed for a in seed for b in seed)
    original = {v:set() for v in vertices}
    for u,v in combinations(vertices,2):
        a,b = ambient(u),ambient(v)
        if add(a,b) in seed or sub(a,b) in seed or sub(b,a) in seed:
            original[u].add(v)
            original[v].add(u)
    assert Counter(map(len, original.values())) == degrees
    loops = {add(a,b) for a in seed for b in seed}
    loops |= {sub(a,b) for a in seed for b in seed}
    loops |= {tuple(3*x % 5 for x in a) for a in seed}
    assert not any(ambient(v) in loops for v in vertices)

    def coord(vertex):
        row,x,y = vertex
        return 2*y+1-row % 2, 5*(row//2)+x

    strip = {(r,z):set() for r in range(10) for z in range(10)}

    def edge(v,w):
        strip[v].add(w)
        strip[w].add(v)

    for r,z,w in product(range(10), range(10), range(10)):
        if F[z] >> w & 1:
            edge((r,z),(r,w))
        if C[r % 2][z] >> w & 1:
            edge((r,z),((r+1) % 10,w))
    assert {coord(v):{coord(w) for w in original[v]} for v in vertices} == strip


def build(F,C):
    independent = [s for s in range(1024) if not (neighborhood(F,s) & s)]
    deficit = {s:1023 ^ (s|neighborhood(F,s)) for s in independent}
    out = [{s:neighborhood(c,s) for s in independent} for c in C]
    inc = [{s:neighborhood(transpose(c),s) for s in independent} for c in C]
    states = []
    for p in range(2):
        possible = {(s,deficit[s] & ~out[1-p][l]) for l in independent for s in independent if not (out[1-p][l]&s)}
        states.append(sorted((s,u) for s,u in possible if any(not (out[p][s]&t) and not (u & ~inc[p][t]) for t in independent)))
    index = [{s:i for i,s in enumerate(row)} for row in states]
    edges = []
    for p in range(2):
        phase = []
        for s,u in states[p]:
            row = []
            for t in independent:
                target = (t,deficit[t] & ~out[p][s])
                if not (out[p][s]&t) and not (u & ~inc[p][t]) and target in index[1-p]:
                    row.append(index[1-p][target])
            phase.append(row)
        edges.append(phase)
    return states,edges,len(independent)


def certify(name):
    seed,F,C,phase,lam,degrees = model(name)
    verify_original(seed,F,C,degrees)
    states,edges,ni = build(F,C)
    expected = {"nested":([100,70],[615,340]), "triangle":([295,340],[925,3875]), "twozero":([75,75],[390,390])}
    assert list(map(len,states)) == expected[name][0]
    assert [sum(map(len,e)) for e in edges] == expected[name][1]
    B = [Counter(j for middle in row for j in edges[1-phase][middle]) for row in edges[phase]]
    weight = [sum(row.values()) for row in B]
    bw = [sum(m*weight[j] for j,m in row.items()) for row in B]
    assert all(w>0 for w in weight)
    assert all(a<=lam*w for a,w in zip(bw,weight))
    n = len(B)
    assert n*lam**5 < 3**25
    table = []
    index = {s:i for i,s in enumerate(states[phase])}
    for i,state in enumerate(states[phase]):
        orb = orbit(state)
        assert len(set(orb)) == 5
        assert all(s in index for s in orb)
        assert all((weight[index[s]],bw[index[s]]) == (weight[i],bw[i]) for s in orb)
        if state == min(orb):
            table.append([*state,weight[i],bw[i]])
    assert len(table)*5 == n

    trace = 0
    for start in range(n):
        current=[0]*n
        current[start]=1
        for _ in range(5):
            nxt=[0]*n
            for i,row in enumerate(B):
                for j,m in row.items():
                    nxt[j]+=current[i]*m
            current=nxt
        trace+=current[start]
    assert trace<=n*lam**5
    print("PASS",name,"original graph, exact strip isomorphism, degrees",sorted(degrees.items()))
    print("PASS",name,"states",list(map(len,states)),"phase",phase,"lambda",lam,"trace",trace,"bound",n*lam**5,"target",3**25)
    return {"name":name,"internal":F,"interfaces":C,"states":states,"transitions":edges,"phase":phase,"lambda":lam,"orbit_table":table,"bound":n*lam**5,"exact_trace":trace}


if __name__ == "__main__":
    results=[certify(name) for name in ("nested","triangle","twozero")]
    root=Path(__file__).parent
    (root/"matrix_size4_certificate.json").write_text(json.dumps(results,separators=(",",":"))+"\n")
    text=[]
    for result in results:
        text += [result["name"],"S U w=B1 Bw=B^2 1"]
        text += ["%4d %4d %5d %7d" % tuple(row) for row in result["orbit_table"]]
        text += ["lambda = "+str(result["lambda"]),"bound = "+str(result["bound"]),"exact trace = "+str(result["exact_trace"]),""]
    (root/"matrix_size4_table.txt").write_text("\n".join(text)+"\n")
