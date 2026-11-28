"""Exact counting data for the K30 cut and moment bounds. Python 3.10+."""
from collections import Counter
from fractions import Fraction as Q
from functools import cache
from itertools import combinations, product
from math import comb, factorial

COLORS = 29
LABELS = COLORS * comb(15, 3)
TYPES = ('LL', 'LR', 'RR')


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def ways(t):
    """Partitions of 3t points into unordered triples."""
    return factorial(3 * t) // (6**t * factorial(t))


def prescribe(points, blocks):
    return Q(ways(points // 3 - blocks), ways(points // 3))


@cache
def signatures(sizes):
    """Matching edge counts in the upper triangle of the region matrix."""
    cells = list(combinations(range(len(sizes) + 1), 2))
    cells = [(i, j - 1) for i, j in cells]

    def visit(h, left, counts):
        if h == len(cells):
            if not any(left):
                yield tuple(counts)
            return
        i, j = cells[h]
        maximum = left[i] // 2 if i == j else min(left[i], left[j])
        for value in range(maximum + 1):
            left[i] -= value
            left[j] -= value
            if j != len(sizes) - 1 or left[i] == 0:
                yield from visit(h + 1, left, counts + [value])
            left[i] += value
            left[j] += value

    return tuple(visit(0, list(sizes), []))


def edge_totals(sizes):
    return [choose(a, 2) if i == j else a * sizes[j]
            for i, a in enumerate(sizes) for j in range(i, len(sizes))]


def first(i):
    """Expected labelled six-point cuts for one color closing i pairs on the left."""
    j, b = i + 3, 12 - 2 * i
    return (10 * choose(i, 3) * prescribe(12, 2),
            (choose(b, 3) + i*j*b) * prescribe(12, 1) * prescribe(18, 1),
            10 * choose(j, 3) * prescribe(18, 2))


def region_data(t, e):
    left = (6, 9, 12)[t]
    right = 24 - left
    a, b, c, d, f, g, h, x, y, z = e
    bills = [10 * choose(x, 3) * prescribe(left, 2),
             (choose(y, 3) + x*z*y) * prescribe(left, 1)*prescribe(right, 1),
             10 * choose(z, 3) * prescribe(right, 2)]
    sides = ((0, 0), (0, 1), (1, 1))[t]
    for side, internal, to_l, to_r in zip(sides, (a, f), (c, g), (d, h)):
        for zone, free_pairs, touching, points in ((0, x, to_l, left), (1, z, to_r, right)):
            choices = int(touching == 3) if internal == 0 else free_pairs * int(touching == 1)
            bills[side + zone] += choices * prescribe(points, 1)
    zone = sides + (0, 1)
    cells = [(i, j) for i in range(4) for j in range(i, 4)]
    inside = sum(v for v, (i, j) in zip(e, cells) if zone[i] == zone[j] == 0)
    anchor = all(not v or zone[i] == zone[j] for v, (i, j) in zip(e, cells))
    marked = c + d + g + h == 0
    complement = t == 0 and c + g + y == 0
    return bills, inside, anchor, marked, complement


def populations():
    """Vertices of the color-count polytope after setting one closing color aside."""
    for i, j in combinations(range(7), 2):
        a = Q(28*j - 60, j - i)
        if 0 <= a <= 28:
            p = [Q(0)] * 7
            p[6] = 1
            p[i] += a
            p[j] += 28 - a
            yield p


def duplicate_weight(t, i):
    """Chance a given six is hit in category t, at a random long cut of one anchor."""
    endpoint_counts = [2]*i + [1]*(6-2*i) + [0]*(9+i)
    good = sum(sum(s) == (6, 3, 0)[t] for s in combinations(endpoint_counts, 6))
    factors = (10*prescribe(12, 2), prescribe(12, 1)*prescribe(18, 1), 10*prescribe(18, 2))
    return Q(good, choose(15, 6)) * factors[t]


class Model:
    def __init__(self):
        self.rows = {}

    def add(self, name, terms, relation, value=0):
        coeff = Counter()
        for var, q in terms:
            coeff[var] += q
        self.rows[name] = ({v: Q(q) for v, q in coeff.items() if q}, relation, Q(value))


def long_model():
    """Exact inequalities for deleting all six-point cuts from the twelve-point loss."""
    model = Model()
    add = model.add
    xs = [f'x{i}' for i in range(7)]
    ds = [f'd{i}' for i in range(4)]
    states = list(product(range(7), range(25), range(16)))
    ys = ['y%d_%d_%d' % r for r in states]

    def moment(j, k=None):
        return [(v, r[j] * (1 if k is None else r[k] - int(k == j))) for r, v in zip(states, ys)]

    add('mass', zip(ys, [1]*len(ys)), '=', 1)
    add('colors', zip(xs, [1]*7), '=', 29)
    add('left_edges', zip(xs, range(7)), '=', 66)
    add('anchor_color', [(xs[6], 1)], '>=', 1)
    add('duplicate_colors', [*zip(ds, [1]*4), ('D', -29)], '=')
    add('duplicate_edges', [*zip(ds, range(4)), ('D', -15)], '=')
    add('duplicate_closing', [(ds[3], 1), ('D', -2)], '>=')
    ext = list(populations())
    for j, tag in enumerate(TYPES):
        u = 'u' + str(j)
        firsts = [first(i)[j] for i in range(7)]
        expectations = [sum(a*b for a, b in zip(p, firsts)) for p in ext]
        low_mass, high_mass = min(expectations)/5, max(expectations)
        add(tag+'_mean', moment(j) + [(u, -1)], '=')
        add(tag+'_distinct', [(u, 1)] + list(zip(xs, [-v for v in firsts]))
            + [(v, duplicate_weight(j, i)/29) for i, v in enumerate(ds)], '=')
        left = (6, 9, 12)[j]
        sizes = (3, 3, left, 24-left)
        sig = signatures(sizes)
        vs = ['v%d_%d' % (j, i) for i in range(len(sig))]
        data = [region_data(j, e) for e in sig]
        add(tag+'_colors', [(v, 1) for v in vs] + [(u, -29)], '=')
        for k, total in enumerate(edge_totals(sizes)):
            add(tag+'_edges_'+str(k), [(v, e[k]) for v, e in zip(vs, sig)] + [(u, -total)], '=')
        add(tag+'_anchor', [(v, q[2]) for v, q in zip(vs, data)] + [(u, -1)], '>=')
        for i in range(7):
            add(tag+'_closing_'+str(i), [(v, 1) for v, q in zip(vs, data) if q[1] == i and q[3]]
                + [(xs[i], -firsts[i])], '=')
            low, high = int(i == 6), max(p[i] for p in ext)
            for k, (a, b, relation) in enumerate(((low, low_mass, '>='), (high, high_mass, '>='),
                                                   (low, high_mass, '<='), (high, low_mass, '<='))):
                add(f'{tag}_product_{i}_{k}', [(v, 1) for v, q in zip(vs, data) if q[1] == i]
                    + [(u, -a), (xs[i], -b)], relation, -a*b)
        for k in range(3):
            add(f'{tag}_other_{k}', moment(j, k) + [(v, -q[0][k]) for v, q in zip(vs, data)], '<=')
        if j == 0:
            add('LL_complement', moment(0, 0) + [(v, q[4] - q[0][0]) for v, q in zip(vs, data)]
                + [(u, -1)], '<=')
    return model


def degree_sequences(slots, total, cap):
    if slots == 0:
        if total == 0:
            yield ()
        return
    for d in range(min(total, cap), -1, -1):
        if total - d > (slots - 1)*d:
            break
        for tail in degree_sequences(slots - 1, total - d, d):
            yield (d,) + tail


def check_small_graphs():
    for edges in range(1, 8):
        for degrees in degree_sequences(10, 2*edges, edges):
            if degrees[0] >= sum(d > 0 for d in degrees) or degrees[0] + degrees[1] > edges + 1:
                continue
            upper = 0
            for i, d in enumerate(degrees):
                others = degrees[:i] + degrees[i+1:]
                upper += max(0, d-1)*sum(max(0, k-1) for k in others[:d]) - d*(d-1)
            assert upper <= (edges-1)*(edges-3)*(edges-4)


def short_loss(d):
    p = lambda k: Q(ways(10-k), ways(10))
    x = max(0, (LABELS-d)*3004 - 3116*d) * 100*p(4)/2
    y = max(0, 4060*1898 - 2640*d)*p(3)/2
    dis = 10*942*p(6)/p(4)
    isolated = 10*1480*p(5)/p(3)
    neighbor = 51*p(4)/p(3)
    return ((LABELS-d)*10*p(2) - (Q(5,6) - dis/6)*x
            - (Q(2,3) - isolated/2 - neighbor/2)*y)
