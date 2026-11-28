"""Cut masses when the reserved singleton can avoid many isolated triples."""
from collections import defaultdict
from fractions import Fraction
from math import comb, factorial, prod

from check import completions, connected


def hard_masses(n):
    u = n-1
    t = u//3
    generic = n-1
    free_pairs = (u-2)//2
    masses = defaultdict(Fraction)
    # The third profile first separates x together with one free triple.
    # Charge one additional component only when its outside disconnects.
    easy_mass = Fraction(generic*free_pairs, comb(u-1, 2))
    profiles = [(generic, t, (1, 1), 0, True), (2, t, (), 0, False),
                (easy_mass, t-1, (1,), 1, True)]
    for weight, free, blocks, initial, is_generic in profiles:
        total = completions(sum(blocks), free)
        pairs = free_pairs if is_generic else u//2
        for mask in range(1 << len(blocks)):
            selected = tuple(v for i, v in enumerate(blocks) if mask & (1 << i))
            a = sum(selected)
            for j in range(1, free//2+1):
                if j == 1 and a == 1:
                    continue
                count = (comb(free, j) * connected(j, selected, True)
                         * completions(sum(blocks)-a, free-j))
                if count:
                    J, A = j+initial, a+initial
                    h = (3*J-A)//2
                    assert 2*h+A == 3*J and 0 <= h <= pairs
                    masses[J, A, pairs, h, is_generic] += (
                        weight * Fraction(count, total * (1 + (2*j == free))))
    return masses


def partitions(t):
    return factorial(3*t)//(6**t * factorial(t))


def covered_masses(n):
    """Mean number of hard far sides covered by excluded endpoint triples."""
    u = n-1
    t = u//3
    generic = n-1
    k = (u-2)//2
    w = generic*k
    result = []
    for j in range(2, t-1):
        a = j % 2
        b = (3*j-a)//2
        if b > k:
            continue
        p3 = Fraction(comb(b, 3), comb(k, 3))
        p2 = Fraction(comb(b, 2), comb(k, 2))
        eligible = w*p3 + Fraction((2+3*a)*w, generic)*(p2-p3)
        all_excluded = min(1, eligible/comb(3*j, 3))
        mass = Fraction(generic*comb(k, b)*partitions(j)*partitions(t-j), partitions(t))
        result.append((u-3*j, mass*all_excluded))
    # If all free triples are excluded, the first four in a uniform ordering are.
    all_excluded = prod(min(Fraction(1), Fraction(comb(q, 2), comb(q, 3)))
                        for q in range(u, u-12, -3))
    return result, all_excluded
