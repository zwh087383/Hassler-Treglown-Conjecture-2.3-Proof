"""Independent finite checks for the November 22 draft. Python standard library only.

Build links using x+y=z, allowing equal summands. In the six cyclic strips
the state records a slice and its full set of possible *next choices*.
Strip transitions are rebuilt from adjacency. For type B collisions, the
program generates all possible patterns, reads the proposed rational weights
from the certificate, and independently recomputes their weighted sums.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import prod
from pathlib import Path
import json


def add(a, b):
    return tuple((x+y) % 5 for x, y in zip(a, b))


def sub(a, b):
    return tuple((x-y) % 5 for x, y in zip(a, b))


def neg(a):
    return tuple(-x % 5 for x in a)


def free(s):
    return all(add(x, y) not in s for x in s for y in s)


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length()-1
        mask -= low


def seeds(a, p, q):
    return {(0,*x,0) for x in a} | {(1,*x,0) for x in p} | {(4,*neg(x),0) for x in q}


def linked(s, x, y):
    return add(x, y) in s or sub(x, y) in s or sub(y, x) in s


def raw_graph(s, vertices):
    assert free(s)
    assert all(free(s | {v}) for v in vertices)
    graph = [0] * len(vertices)
    for i, j in combinations(range(len(vertices)), 2):
        if linked(s, vertices[i], vertices[j]):
            graph[i] |= 1 << j
            graph[j] |= 1 << i
    return graph


def all_neighborhoods(rows):
    sets = [0]
    for row in rows:
        sets += [mask | row for mask in sets]
    return sets


def maximal_cliques_of_complement(rows):
    allv = (1 << len(rows))-1
    comp = [allv ^ (r | 1 << i) for i, r in enumerate(rows)]
    def visit(p, x):
        if not p:
            return int(not x)
        u = max(bits(p | x), key=lambda i: (p & comp[i]).bit_count())
        amount = 0
        for v in bits(p & ~comp[u]):
            amount += visit(p & comp[v], x & comp[v])
            p ^= 1 << v
            x |= 1 << v
        return amount
    return visit(allv, 0)


def rank_one():
    labels = [(i,k,0) for i,k in product((0,1,4),range(5)) if (i,k)!=(0,0)]
    verts = list(product((2,3), range(5), (1,4)))
    edge_masks = [[sum(1<<j for j,y in enumerate(verts) if x!=y and linked({s},x,y))
                   for x in verts] for s in labels]
    hist = Counter()
    best = 0
    def search(i, seed, rows):
        nonlocal best
        count = maximal_cliques_of_complement(rows)
        best = max(best, count)
        assert count <= 3**5
        hist[len(seed)] += 1
        for j in range(i,len(labels)):
            s = seed | {labels[j]}
            if free(s):
                search(j+1,s,[a | b for a,b in zip(rows,edge_masks[j])])
    search(0,set(),[0]*20)
    print('all rank-one seeds (generic block):',sum(hist.values()),'maximum',best,'size distribution',sorted(hist.items()))
    assert sum(hist.values()) == 1470 and best == 243
    for name,a,p,q in [('86 r2',[1,4],[0,2],[]),('86 r3',[1,4],[0,3],[]),
                        ('76 r2',[1],[0,2],[0]),('76 r3',[1],[0,3],[0]),
                        ('87 r3',[1],[0,3],[1]),('88 r2',[1],[0,2],[0,3]),
                        ('same r2',[1],[0,2],[]),('same r3',[1],[0,3],[]),
                        ('opp q1',[1],[0],[1]),('opp q2',[1],[0],[2]),('opp q3',[1],[0],[3])]:
        s=seeds(*[[(i,) for i in l] for l in (a,p,q)])
        print('20 vertices',name,maximal_cliques_of_complement(raw_graph(s,verts)))


def cyclic_trace(matrices):
    # matrices[p][i] is a dict from a successor index to its multiplicity.
    # Rotate the labeled circle to its smallest layer to reduce work.
    r=min(range(len(matrices)),key=lambda p:len(matrices[p]))
    matrices=matrices[r:]+matrices[:r]
    n=len(matrices[0])
    trace=0
    for start in range(n):
        current={start:1}
        for m in matrices:
            nxt=defaultdict(int)
            for i,ways in current.items():
                for j,mult in m[i].items():
                    nxt[j] += ways*mult
            current=nxt
        trace+=current.get(start,0)
    return trace


def strip_count(name, s, flip):
    # Slice y first. On the negative quotient coset normalize x and y by
    # negation. Horizontal ordering within each slice is arbitrary.
    by_slice=[[] for _ in range(10)]
    for head,x,y,tail in product((2,3),range(5),range(5),(1,4)):
        sign = 1 if tail==1 else -1
        row = {(2,1):0,(3,1):1,(3,4):2,(2,4):3}[(head,tail)]
        r=2*((sign*y)%5)+((row%2) ^ flip)
        by_slice[r].append((head,x,y,tail))
    assert all(len(row)==10 for row in by_slice)
    vertices=sum(by_slice,[])
    graph=raw_graph(s,vertices)
    previous=[]; inside=[]; forward=[]
    for r in range(10):
        rset={(r-1)%10,r,(r+1)%10}
        rows=graph[10*r:10*r+10]
        assert all(j//10 in rset for row in rows for j in bits(row))
        for bucket,offset in [(previous,-1),(inside,0),(forward,1)]:
            k=(r+offset)%10
            bucket.append(all_neighborhoods([(neighbors>>(10*k)) & 1023 for neighbors in rows]))
    choices=[[a for a in range(1024) if not a & inn[a]] for inn in inside]
    states=[]; ids=[]
    for r in range(10):
        before=(r-1)%10; after=(r+1)%10
        pairs={}; unique={}
        for middle in choices[r]:
            # Tabulate future slices that are compatible and cover a given deficit.
            need=1023 ^ (middle | inside[r][middle])
            compatible=[(k,previous[after][c]) for k,c in enumerate(choices[after]) if not forward[r][middle]&c]
            tails={}
            for left in choices[before]:
                occupied=forward[before][left]
                if occupied & middle:
                    continue
                missing=need & ~occupied
                if missing not in tails:
                    tails[missing]=sum(1<<k for k,hit in compatible if not missing & ~hit)
                admissible=tails[missing]
                if admissible:
                    key=(middle,admissible)
                    pairs[(left,middle)]=unique.setdefault(key,len(unique))
        states.append(list(unique)); ids.append(pairs)
    matrices=[]
    for r in range(10):
        after=(r+1)%10
        matrix=[]
        for chosen,allowed in states[r]:
            row={}
            for k in bits(allowed):
                j=ids[after].get((chosen,choices[after][k]))
                if j is not None:
                    row[j]=row.get(j,0)+1
            matrix.append(row)
        matrices.append(matrix)
    count=cyclic_trace(matrices)
    assert count < 3**25
    print('100 vertices',name,'exact MIS',count,'states',list(map(len,states))[:2])
    return count


def transfer_models():
    o=(0,0); a=(1,0); na=(4,0); r=(0,1)
    for name,aa,p,q,flip in [
        ('same triple',[a],[o,r],[],1),('opposite triple',[a],[o],[(0,4)],0),
        ('nested four',[a],[o,r],[o],1),('triangle four',[a],[o,r],[a],1),
        ('two zero four',[a,na],[o,r],[],1),('triangle five',[a],[o,r],[o,(1,1)],1)]:
        strip_count(name,seeds(aa,p,q),flip)


def row_union_model():
    # Build the two actual biadjacency interfaces of the seventh model
    # directly from translations. A cell stores the union of its columns.
    p={(0,0)}; q={(0,1),(1,1)}
    joins=[]
    for layer in (0,1):
        rows=[]
        for color,x in product(range(2),range(5)):
            row=0
            for side,y in product(range(2),range(5)):
                translations=(p|q) if color==side else (q if color==0 else p)
                if ((y-x)%5,layer) in translations:
                    row |= 1<<(5*side+y)
            rows.append(row)
        joins.append(all_neighborhoods(rows))
    now,carry=joins
    alphabet=sorted(set(carry))
    states={v:i for i,v in enumerate(alphabet)}
    matrix=[]
    for incoming in alphabet:
        labels={(states[next_carry],incoming|occupy) for occupy,next_carry in zip(now,carry)}
        matrix.append(Counter(c for c,_ in labels))
    upper=cyclic_trace([matrix]*5)
    frob=sum(Fraction(mult**2)*Fraction(2)**((alphabet[i]>>5).bit_count()-(alphabet[j]>>5).bit_count())
             for i,row in enumerate(matrix) for j,mult in row.items())
    assert upper < 3**25 and frob <3**10
    print('100 vertices no-zero triple: carry states',len(matrix),'labeled trace upper',upper,'weighted norm squared',frob)


def window(s,typ):
    # Read the printed biadjacency block at each translation in turn.
    hit=[False,False]
    for z,(p,q) in zip(s,typ):
        block=((p or q,q),(p,p or q))
        for i,j in product(range(2),repeat=2):
            hit[j] |= bool((z>>i)&1) and block[i][j]
    return int(not hit[1])+2*int(not hit[0])


def entropy_sums():
    from functools import lru_cache
    w=tuple(map(Fraction,(1,'1/2','1/2','1/2')))
    qa=tuple(map(Fraction,(1,1,1,'1/2')))
    qc=tuple(map(Fraction,(1,'1/2',1,'1/2')))
    for name,types,weights in [('A',[(1,0)]*3+[(0,1)],[w,w,w,qa]),
                                ('C',[(1,1),(1,0),(1,0),(0,1)],[(1,)*4,w,w,qc])]:
        parts=[Fraction(0)]*4; n=0
        for z in product(range(4),repeat=4):
            if z[-1]==2 and any(z[:-1]): continue
            f=window(z,types)
            parts[f]+=prod(Fraction(t[s],t[f]) for t,s in zip(weights,z)); n+=1
        assert n==193 and sum(parts)<81
        print('local entropy',name,n,parts,'sum',sum(parts))
    c,a,b,g=[tuple(map(Fraction,t)) for t in [(1,'1/4',1,1),(1,'1/3','2/3','1/2'),
                                               (1,'2/3','1/3','1/2'),(1,'2/27','2/27','1/8')]]
    assert all(x*y*y*z**4==u*u for x,y,z,u in zip(c,a,b,g))
    @lru_cache(None)
    def f(x,y,z,t):
        return window([x,y,z,t],[(1,0),(1,0),(0,1),(0,1)])
    total=sum(c[i]*a[j]*a[k]*b[l]*b[m]*b[n]*b[o]/(g[f(i,j,l,m)]*g[f(i,k,n,o)])
              for i,j,k,l,m,n,o in product(range(4),repeat=7))
    assert total<3**7
    print('local entropy B',4**7,'sum',total)


def global_small(d):
    points=list(product(range(5),repeat=d))[1:]
    count=Counter()
    def search(start,seed,available):
        if not available:
            count[len(seed)]+=1
        for j in sorted(available):
            if j<start: continue
            new=seed|{points[j]}
            search(j+1,new,{u for u in available if u!=j and free(new|{points[u]})})
    search(0,set(),set(range(len(points))))
    expected = {0: {0: 1}, 1: {2: 2}, 2: {5: 360, 10: 12}}
    assert dict(count) == expected[d]
    print('global F5 dimension',d,'maximal sum-free sets',sum(count.values()),'by size',sorted(count.items()))


def rank_zero():
    points = [(1,0),(4,0)]
    vertices = list(product((2,3),(1,4)))
    counts = [maximal_cliques_of_complement(raw_graph(set(seed), vertices))
              for n in range(3) for seed in combinations(points,n)]
    assert len(counts) == 4 and counts[0] == 1 and max(counts) == 3
    print('all rank-zero seeds (generic block):',len(counts),'maximum',max(counts),'empty seed',counts[0])


def pure_zero_triple():
    seed = {(0,1,0,0), (0,0,1,0), (0,4,4,0)}
    vertices = [(h,u,v,t) for h in (2,3) for u,v in product(range(5), repeat=2) for t in (1,4)]
    graph = raw_graph(seed, vertices)
    remaining = set(range(len(vertices)))
    counts = []
    while remaining:
        first = remaining.pop()
        component = [first]
        for vertex in component:
            new = set(bits(graph[vertex])) & remaining
            component.extend(new)
            remaining -= new
        indices = {v: i for i, v in enumerate(component)}
        subgraph = [sum(1 << indices[w] for w in bits(graph[v])) for v in component]
        counts.append((len(component), maximal_cliques_of_complement(subgraph)))
    assert counts == [(50,19245),(50,19245)]
    print('pure zero-sum triple: connected components and exact MIS', counts)


def ten_eight_certificate(vertices, rows):
    index = {point: i for i, point in enumerate(vertices)}
    degrees = [n.bit_count() for n in rows]
    assert set(degrees) == {8, 10} and sum(degrees) == 9 * len(rows)
    high = sum(1 << i for i, d in enumerate(degrees) if d == 10)

    def edges_twice(group):
        return sum((rows[i] & group).bit_count() for i in bits(group))

    def common(x, y):
        return (rows[x] & rows[y]).bit_count()

    for x in bits(high):
        near = rows[x]
        w = index[neg(vertices[x])]
        other = rows[w]
        assert sum(degrees[u] for u in bits(near)) <= 90 and edges_twice(near) >= 6
        for y in bits(near):
            kept = near ^ (1 << y)
            assert (kept & high).bit_count() <= 5 and edges_twice(kept) >= 2
        assert x != w and not (near >> w) & 1 and degrees[w] == 8
        assert sum(degrees[u] for u in bits(other)) <= 74 and edges_twice(other) >= 6
        assert common(x,w) >= 6
        for y in bits(other | (1 << w)):
            if (near >> y) & 1 or common(x,y) >= 3:
                continue
            assert common(x,y) >= 2
            assert any(not (rows[q] >> y) & 1 and common(q,y) >= 3 for q in bits(near & high))
        excluded = near | other | (1 << x) | (1 << w)
        assert any(common(z,x) + common(z,w) >= 3 for q in bits(near & high)
                   for z in bits(rows[q] & high & ~excluded))


def ten_eight_models():
    for dim in (2,3):
        field = list(product(range(5), repeat=dim))
        e = [tuple(int(i==j) for i in range(dim)) for j in range(dim)]
        vertices = [(h,*u,t) for h in (2,3) for u in field for t in (1,4)]
        checked = 0
        for c in (field if dim == 2 else [e[2]]):
            seed = seeds([e[0]], [(0,)*dim,e[1],c], [e[0]])
            if len(seed) != 5 or not free(seed):
                continue
            rows = raw_graph(seed, vertices)
            ten_eight_certificate(vertices, rows)
            checked += 1
        assert checked == {2:18, 3:1}[dim]
        print('10/8 actual neighborhood certificates: dimension',dim,'vertices',len(vertices),'models',checked)


def four_point_profiles():
    for dim in (2,3):
        field = list(product(range(5), repeat=dim))
        e = [tuple(int(i==j) for i in range(dim)) for j in range(dim)]
        vertices = [(h,*u,t) for h in (2,3) for u in field for t in (1,4)]
        checked = 0
        seen = 0
        clean_count = 0
        for j, l in product((0,1,4), repeat=2):
            for tail in (field if dim == 2 else [e[2]]):
                seen += 1
                seed = {(0,*e[0],0), (1,*(0,)*dim,0), (j,*e[1],0), (l,*tail,0)}
                if len(seed) != 4 or not free(seed):
                    continue
                rows = raw_graph(seed, vertices)
                signed = seed | {neg(v) for v in seed}
                z, p, q = [sum(v[0] == h for v in seed) for h in (0,1,4)]
                base = z + sum(v[0] in (0,1) for v in signed)
                assert all(row.bit_count() == base + (p if v[0] == 3 else q)
                           for row, v in zip(rows, vertices))
                if all(neg(add(x,y)) not in seed for x in seed for y in seed):
                    clean_count += 1
                    assert not any(row & rows[i] for row in rows for i in bits(row))
                checked += 1
        print('four-point models: dimension',dim,'inputs',seen,'valid seeds',checked,'zero-sum-free',clean_count)


def collision_certificates():
    # Equalities of seven vector offsets are intersections of the equalities
    # on their scalar coordinates, including the empty intersection.
    def pattern(items):
        items = list(items)
        labels = list(dict.fromkeys(items))
        return tuple(labels.index(item) for item in items)

    scalar = {pattern(x % 5 for x in (0,-u,u,-v,-w,u-v,u-w))
              for u,v,w in product(range(5),repeat=3)}
    reachable = {(0,)*7}
    while True:
        new = {pattern(zip(old,one)) for old in reachable for one in scalar}
        if new.issubset(reachable):
            break
        reachable.update(new)
    collisions = {p for p in reachable if len({p[0],p[1],p[3],p[4]}) == 4 and max(p) < 6}
    certs = json.loads((Path(__file__).parent/'Audit'/'collision-sums.json').read_text())
    assert len(certs)==len(collisions) and {tuple(c['pattern']) for c in certs} == collisions
    outputs = {x:window(x,[(1,0)]*2+[(0,1)]*2) for x in product(range(4),repeat=4)}
    for c in certs:
        inputs = c['pattern']
        n = c['width']
        weights = [list(map(Fraction,row)) for row in c['weights']]
        assert len(weights)==n+1 and all(x>0 for row in weights for x in row)
        denominators = [prod(row[s] for row in weights) for s in range(4)]
        value = Fraction(0)
        for z in product(range(4),repeat=n):
            i,j,k,l,m,p,q = (z[pos] for pos in inputs)
            f=outputs[i,j,l,m]; g=outputs[i,k,p,q]
            value += prod(table[state] for table,state in zip(weights,(*z,f))) / denominators[g]
        assert value == Fraction(c['sum']) and value < 3**n
        print('B collision', ''.join(map(str,inputs)), 'partition',value,'<',3**n)
    print('scalar patterns',len(scalar),'all-dimensional closure',len(reachable),'valid collision certificates',len(certs))


if __name__=='__main__':
    rank_zero()
    rank_one()
    transfer_models()
    row_union_model()
    entropy_sums()
    collision_certificates()
    global_small(0)
    global_small(1)
    global_small(2)
    pure_zero_triple()
    ten_eight_models()
    four_point_profiles()
