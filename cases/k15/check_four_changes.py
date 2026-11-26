from pathlib import Path
import json
from itertools import combinations
from collections import Counter
D=Path(__file__).resolve().parent
def find(f, initial):
    assert len(f) == 15
    for m in f:
        assert len(m) == 16 and all(0 <= v < 16 for v in m)
        assert all(m[v] != v and m[m[v]] == v for v in range(16))
    assert all({m[v] for m in f} == set(range(16)) - {v} for v in range(16))
    V=32767

    closed=set();square_counts=[0]*16
    for m in f:
        es=[(1<<i)|(1<<m[i]) for i in range(15) if i<m[i]<15]
        closed.update(e|(1<<m[15]) for e in es)
        closed.update(x|y|z for x,y,z in combinations(es,3))
    for m,n in combinations(f,2):
        for v in range(16):
            if m[n[m[n[v]]]]==v:square_counts[v]+=1
    assert len(set(square_counts[:15]))>1 and max(square_counts)>0
    def pure(m,g):
        cross={bool(g&(1<<i))!=bool(g&(1<<m[i])) for i in range(16)}
        return len(cross)==1
    assert not any(all(pure(m,g) for m in f) for g in range(1<<15) if g.bit_count()==8)
    allowed={}
    for t in combinations(range(15),3):
        mask=sum(1<<v for v in t)
        if mask not in closed:allowed[mask]=sum(a in t and b in t for a,b in initial)
    found=Counter();winner=[];best=-1
    def dfs(left,groups,retained):
        nonlocal best,winner
        if not left:
            found[retained]+=1
            if retained>best:best=retained;winner=groups
            return
        a=left&-left;x=left^a
        while x:
            k=x&-x;x-=k;y=x
            while y:
                z=y&-y;y-=z;t=a|k|z
                if t in allowed and all((s|t) not in closed for s in groups):
                    dfs(left^t,groups+[t],retained+allowed[t])
    dfs(V,[],0)
    new_edges=[]
    for t in winner:
        points=[v for v in range(15) if t>>v&1];keep=[e for e in initial if e[0] in points and e[1] in points]
        for e in combinations(points,2):
            if len(keep)<2 and e not in keep:keep.append(e)
        new_edges.extend(keep)
    return dict(mates=f,initial=initial,solution=new_edges,retained=best,counts_by_retained={str(k):found[k] for k in range(11)},four_cycle_counts=square_counts)
if __name__ == '__main__':
    example = json.loads((D / 'four-changes.json').read_text())
    original = [tuple(edge) for edge in example['initial']]
    result = find(example['mates'], original)
    assert result['counts_by_retained'] == example['counts_by_retained']
    assert result['four_cycle_counts'] == example['four_cycle_counts']
    assert result['retained'] == 6
    assert list(map(list, result['solution'])) == example['solution']
    print('All five-triple partitions examined. Working groupings by maximum number of original lines retained:')
    for count, frequency in result['counts_by_retained'].items():
        print(f'{count:>2}  {frequency:>6}')
