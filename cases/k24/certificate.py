"""Exact cut counts and inequalities for the two halves of K24."""
from collections import Counter
from fractions import Fraction as Q
from functools import cache
from itertools import combinations, combinations_with_replacement
from math import comb, lcm
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'k30'))
from counts import choose, long_model, ways

COLORS = 23
SIXES = COLORS*comb(12, 3)


def cycle_types(total=12, low=2):
    if total == 0:
        yield ()
    for length in range(low, total + 1):
        for tail in cycle_types(total-length, length):
            yield (length,) + tail


def cycle_variable(cs):
    return 'cycles_' + '_'.join(map(str, cs))


def block_probability(k):
    return Q(ways(8-k), ways(8))


def matching(cs):
    """One edge from each first-coordinate endpoint to the next second endpoint."""
    offset = 0
    for length in cs:
        for j in range(length):
            yield (1 << (2*(offset+j))) | (1 << (2*(offset+(j+1) % length)+1))
        offset += length


@cache
def six_intersections(cs):
    def sixes(edges):
        return [a | b | c for a, b, c in combinations(edges, 3)]
    return Counter((s & t).bit_count() for s in sixes(matching((1,)*12))
                   for t in sixes(matching(cs)))


@cache
def single_cycle(length):
    """Enumerate subsets of one alternating even cycle by vertex and internal edge counts."""
    result = Counter()
    for first in (0, 1):
        states = Counter({(first, first, 0, 0): 1})
        for position in range(1, 2*length):
            new = Counter()
            for (previous, size, a, b), count in states.items():
                for bit in (0, 1):
                    internal = previous*bit
                    new[bit, size+bit, a+(position % 2)*internal,
                        b+((position+1) % 2)*internal] += count
            states = new
        for (last, size, a, b), count in states.items():
            result[size, a, b + last*first] += count
    return result


@cache
def cut_table(cs):
    if not cs:
        return Counter({(0, 0, 0): 1})
    result = Counter()
    for (u, i, j), a in cut_table(cs[:-1]).items():
        for (v, k, l), b in single_cycle(cs[-1]).items():
            if u+v <= 12:
                result[u+v, i+k, j+l] += a*b
    return result


def half_table(cs):
    """Independently count cuts by choosing false and true endpoints separately."""
    # The second matching joins false index i to the true index following i.
    successor = []
    for length in cs:
        start = len(successor)
        successor.extend(start + (i + 1) % length for i in range(length))
    masks = [0] * (1 << len(successor))
    shapes = Counter()
    for mask in range(len(masks)):
        if mask:
            bit = mask & -mask
            masks[mask] = masks[mask ^ bit] | (1 << successor[bit.bit_length() - 1])
        shapes[mask.bit_count(), (mask & masks[mask]).bit_count()] += 1
    table = Counter()
    for (size, both), multiplicity in shapes.items():
        one = size - both
        neither = len(successor) - 2 * size + both
        for shared in range(both + 1):
            for first in range(one + 1):
                for second in range(one + 1):
                    selected = size + shared + first + second
                    choices = multiplicity * comb(both, shared) * comb(one, first) * comb(one, second)
                    for plain in range(min(neither, 12 - selected) + 1):
                        table[selected + plain, first + shared, second + shared] += choices * comb(neither, plain)
    return table


def populations(u):
    """All counts of the 23 colors by internal edge count on a fixed u-set."""
    def visit(i, colors, edges):
        if i == 1:
            if 0 <= edges <= colors:
                yield (colors-edges, edges)
            return
        for v in range(min(colors, edges//i)+1):
            for tail in visit(i-1, colors-v, edges-i*v):
                yield tail + (v,)
    return visit(u//2, COLORS, comb(u, 2))


def monomials(u):
    coords = range(2, u//2+1)
    return [()] + [(i,) for i in coords] + list(combinations_with_replacement(coords, 2))


def feature(h, term):
    if not term:
        return 1
    if len(term) == 1:
        return h[term[0]]
    i, j = term
    return h[i]*(h[j] - (i == j))


def feature_mean(table, u, term):
    if not term:
        return Q(1)
    mass = comb(24, u)
    if len(term) == 1:
        return Q(COLORS*sum(table[u, term[0], j] for j in range(u//2+1)), mass)
    i, j = term
    return Q(COLORS*(COLORS-1)*table[u, i, j], mass)


def polynomial_rows(model, shapes, pair_counts):
    for line in (HERE/'population-prices.txt').read_text().splitlines():
        raw_u, raw_b, *raw_prices = line.split()
        u, b = int(raw_u), int(raw_b)
        prices = list(map(Q, raw_prices))
        terms = monomials(u)
        assert len(prices) == len(terms)
        # Check the majorant pointwise on integer populations, using integer dot products.
        den = lcm(*(v.denominator for v in prices))
        ints = [int(v*den) for v in prices]
        for h in populations(u):
            inside = sum(k*choose(i, 3) for i, k in enumerate(h))
            outside = sum(k*choose(i + 12-u, 3) for i, k in enumerate(h))
            bound = inside if u == 12 else min(20*inside, inside*(inside-1))
            assert sum(v*feature(h, t) for v, t in zip(ints, terms)) >= den*bound*max(0, outside-b)
        row = [('z'+str(u), 1)]
        for cs in shapes:
            mean = sum(v*feature_mean(cut_table(cs), u, t) for v, t in zip(prices, terms))
            pairs = Q(pair_counts[cs][12-u], comb(24, u))
            row.append((cycle_variable(cs), -b*pairs-mean))
        model.add(f'population_{u}_{b}', row, '<=')


def model_and_objective():
    model = long_model(24)
    shapes = tuple(cycle_types())
    model.add('cycle_mass', [(cycle_variable(cs), 1) for cs in shapes], '=', 1)
    same = six_intersections((1,)*12)
    # Ordered pairs of labelled sixes. The two colors can coincide.
    pair_counts = {cs: [COLORS*(same[i] + (COLORS-1)*six_intersections(cs)[i])
                        for i in range(7)] for cs in shapes}
    for cs in shapes:
        tab = cut_table(cs)
        assert tab == half_table(cs)
        for u in (9, 12):
            assert sum(tab[u, i, j] for i in range(7) for j in range(7)) == comb(24, u)
        assert sum(tab[12, 6, i] for i in range(7)) == comb(12, 6)
    for i in range(7):
        model.add(f'profile_{i}', [(f'x{i}', 1)] + [(cycle_variable(cs),
            -Q((COLORS-1)*cut_table(cs)[12, 6, i], comb(12, 6))) for cs in shapes], '=', int(i == 6))
    for u, maximum in ((12, 220), (9, 329)):
        model.add(f'z{u}_raw', [(f'z{u}', 1)] + [(cycle_variable(cs),
            -Q(maximum*pair_counts[cs][12-u], comb(24, u))) for cs in shapes], '<=')
    polynomial_rows(model, shapes, pair_counts)
    p = block_probability
    B, Y, M, I, P, S = Q(9,14), Q(2,3), Q(3,14), Q(13,42), Q(1,3), Q(13,42)
    # A path has two central wedges and a star has three. At each free endpoint
    # at most 36 other triples in the 15-point remainder can extend the wedge.
    effective_y = Y - (P + S/3)*36*p(4)/p(3)
    assert effective_y > 0
    goal = {
        'y0_0_0': Q(COLORS*comb(12,6)*ways(4)**2, 2*ways(8)),
        'z12': M*comb(24,12)*1000*p(6)/6,
        'z9': I*comb(24,9)*10*p(5)/2,
        'D': -10*p(2) + B*100*780*p(4) + effective_y*1000*p(3)}
    for cs, h in pair_counts.items():
        goal[cycle_variable(cs)] = SIXES*10*p(2) - B*50*h[0]*p(4) - effective_y*h[3]*p(3)/2
    return model, goal
