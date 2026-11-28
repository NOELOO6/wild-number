"""Check the eight-point certificates at K37 and K43 using only integer and rational arithmetic."""
from fractions import Fraction
from functools import cache
from itertools import combinations
from math import ceil, comb
from pathlib import Path
import json

from check import averages, conditional_mean, frame_fraction, surplus


def reduced(groups, edges):
    # Each internal color edge consumes an end at each incident block and joins them.
    owner = {v: i for i, group in enumerate(groups) for v in group}
    width = list(map(len, groups))
    component = list(range(len(groups)))
    for a, b in edges:
        i, j = owner[a], owner[b]
        width[i] -= 1
        width[j] -= 1
        old, new = component[j], component[i]
        component = [new if label == old else label for label in component]
    return tuple(sum(d for label, d in zip(component, width) if label == k)
                 for k in dict.fromkeys(component))


def matchings(vertices, count):
    if count == 0:
        yield ()
        return
    for a, b in combinations(vertices, 2):
        # Enforce increasing least endpoints to list every submatching once.
        remaining = tuple(x for x in vertices if x > a and x != b)
        for rest in matchings(remaining, count-1):
            yield ((a, b),) + rest


def verify(row):
    n = row["n"]
    assert n in (37, 43)
    budget = sum(comb(b, 2)*(b-2)//(n+1-b) for b in range(1, 8))
    vertices = tuple(range(8))
    ordinary = set(vertices[1:])
    layouts = [((0,), tuple(sorted(ordinary-set(triple))), triple)
               for triple in combinations(vertices[1:], 3)]
    assert len(layouts) == 35
    free = (n-7)//3
    mean = cache(lambda widths: conditional_mean(free, widths))
    equal = averages(n, (1,4,3))
    scale = 1000000
    index = {edge:i for i,edge in enumerate(combinations(vertices,2))}
    candidates, first = [], []
    for k in range(2, 5):
        cost = comb(k, 2)
        if cost > budget:
            continue
        for matching in matchings(vertices, k):
            mask = sum(1 << index[e] for e in matching)
            changes = [[], []]
            for g in layouts:
                repeated = mean(reduced(g, matching))
                singles = [mean(reduced(g, (edge,))) for edge in matching]
                empty = mean(tuple(map(len, g)))
                for i in range(2):
                    change = repeated[i]+(k-1)*empty[i]-sum(v[i] for v in singles)
                    changes[i].append(ceil(scale*change))
            # A permutation fixing the root sends the first matching to one of these two.
            if any(matching == tuple((j,j+1) for j in range(s,s+2*k,2)) for s in range(2)):
                first.append(len(candidates))
            candidates.append((mask, cost, changes))
    limits = [row["failure_upper"]-ceil(scale*equal[0]), row["deficit_upper"]-ceil(scale*equal[1])]
    assert all(limit >= 0 for limit in limits)
    def check(used, left, start, path):
        for i,limit in enumerate(limits):
            assert any(sum(candidates[j][2][i][g] for j in path) <= limit for g in range(35)), (n,path,i)
        count = 1
        if left:
            for j in range(start,len(candidates)):
                mask, cost, _ = candidates[j]
                if cost <= left and not mask & used:
                    count += check(used | mask, left-cost, j+1, (*path,j))
        return count
    total = 1
    for j in first:
        mask, cost, _ = candidates[j]
        total += check(mask, budget-cost, 0, (j,))
    gain = surplus(n,8,row["certificate"],missing=budget)
    # D and F can attain their upper bounds on different subdivisions of the eight points.
    near = 1-(Fraction(row["deficit_upper"],scale)-gain)/2
    colors = 1-(Fraction(row["failure_upper"],scale)-gain)/2
    result = [max(0,int(scale*near)),max(0,int(scale*colors))]
    assert result == ({37:[0,12377],43:[1808,22698]}[n]), (n,result)
    uniform = int(1000*result[int(n == 37)]*frame_fraction(n,8,allow_collisions=True)/35)
    assert uniform == {37:191,43:88}[n]
    print(n, total, *result)


if __name__ == "__main__":
    for record in json.loads(Path(__file__).with_name("eight-point.json").read_text()):
        verify(record)
