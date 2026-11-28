"""Exact absorption bounds with a prescribed singleton or pair. Python 3.10+, C++17."""
from collections import defaultdict
from fractions import Fraction
from functools import cache
from math import comb
from pathlib import Path
import argparse
import os
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "one-extra" / "piece-moments"))
from check import completions, connected

SCALE = 10**8


def profiles(n, reserved):
    """Weighted color count, exposed ends of each block, block labels, generic color."""
    if reserved == 2:
        yield n-3, (1, 2), (1, 2), True
        yield 2, (1,), (3,), False       # Root matched into the reserved pair.
        yield 2, (1,), (1,), False       # Special color, outside its isolated pair.
    else:
        yield n-1, (1, 1), (1, 2), True
        yield 2, (), (), False           # Special color, outside the root-singleton edge.


def component_masses(n, reserved):
    u = n-reserved
    t = u//3
    masses = defaultdict(Fraction)
    for weight, blocks, labels, generic in profiles(n, reserved):
        f = sum(blocks)
        k = (u-f)//2
        total = completions(f, t)
        for mask in range(1 << len(blocks)):
            selected = tuple(v for i, v in enumerate(blocks) if mask & (1 << i))
            side = sum(v for i, v in enumerate(labels) if mask & (1 << i))
            a = sum(selected)
            for j in range(t//2+1):
                if j == 1 and (side == 1 or (reserved == 1 and side == 2)):
                    continue
                if 3*j < a or (3*j-a) % 2:
                    continue
                h = (3*j-a)//2
                if h > k:
                    continue
                count = (weight * comb(t, j) * connected(j, selected, True)
                         * completions(f-a, t-j))
                if count:
                    masses[j, a, k, h, generic] += Fraction(count, total * (1 + (2*j == t)))
    return masses


def labeled_interval(n, roots, q):
    removed = n-q
    base = comb(n, 2) - 3*((n-1)//2)*removed
    return (roots * max(0, base+2*comb(removed, 2), q*max(0, q-(n+1)//2)),
            roots * min(comb(q, 2), base+3*comb(removed, 2)))


def distinct_interval(n, roots, u, w, m, q):
    degree = 3*roots*(u-1)//2
    low, high = labeled_interval(n, roots, q)
    low = max(low, w-(u-q)*degree)
    high = min(high, w)
    return (max(0, (low+2)//3, low-(w-m), m-(u-q)*degree),
            min(comb(q, 3), high, m-(w-high+2)//3))


def avoidance_table(executable, n, roots, q):
    output = subprocess.check_output([executable, str(n), str(roots), str(q)], text=True)
    table = []
    for line in output.splitlines():
        i, low, high = map(int, line.split())
        assert i == len(table)
        table.append((low, high))
    return table


def estimate(n, executable):
    reserved = n % 3
    if n % 2 == 0 or reserved not in (1, 2):
        raise ValueError("Choose an odd order congruent to 1 or 2 modulo 3.")
    roots = 3-reserved
    u = n-reserved
    w = roots * (comb(n, 2) - 3*((n-1)//2)*reserved + 3*comb(reserved, 2))
    degree_max = 3*roots*(u-1)//2
    degree_min = max(0, (roots*(3*((n-1)//2)-3*(n-u))+2)//3)
    generic_count = n-comb(reserved+1, 2)
    masses = component_masses(n, reserved)
    sizes = sorted({u, *(u-3*j for j, *_ in masses)})
    tables = {q: avoidance_table(executable, n, roots, q) for q in sizes}

    @cache
    def envelope(q, low, high):
        table = tables[q]
        points = [(i, table[i][1]) for i in range(low, min(high+1, len(table)))
                  if table[i][0] <= table[i][1]]
        if not points:
            return None
        first, last = points[0], points[-1]
        # A nonpositive secant slope gives an affine upper bound after raising
        # its intercept to cover every admissible integer in the interval.
        den = max(1, last[0]-first[0])
        num = min(0, last[1]-first[1])
        intercept = max(den*y-num*x for x, y in points)
        return max(y for _, y in points), num, den, intercept

    events = []
    for (j, a, k, h, generic), mass in masses.items():
        assert k >= 3
        p3 = Fraction(comb(k-h, 3), comb(k, 3))
        p2 = Fraction(comb(k-h, 2), comb(k, 2))
        outside = u-2*k-a
        incidences = max(0, outside*(degree_min-a*3*roots))
        events.append((u-3*j, a, generic, mass, p3, (p2-p3)*incidences))

    worst = None
    worst_count = None
    for m in range((w+2)//3, w+1):
        lo, hi = tables[u][m]
        if lo > hi:
            continue
        charge = Fraction(0)
        for q, a, generic, mass, p3, correction in events:
            low, high = distinct_interval(n, roots, u, w, m, q)
            bound = envelope(q, low, high)
            if bound is None:
                raise AssertionError((n, m, q, low, high))
            maximum, num, den, intercept = bound
            eligible = max(0, m-a*degree_max)
            if generic:
                eligible = max(eligible, Fraction(m*(generic_count-3*a), generic_count))
            mean = max(low, p3*eligible+correction)
            upper = min(maximum, (Fraction(intercept)+num*mean)/den)
            charge += mass*upper
        margin = (lo-charge/2)/SCALE
        if worst is None or margin < worst:
            worst, worst_count = margin, m
    assert worst is not None
    return worst, worst_count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("orders", nargs="*", type=int, default=[47, 53, 73])
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as temp:
        executable = Path(temp) / "avoidance"
        subprocess.run([os.environ.get("CXX", "c++"), "-std=c++17", "-O2", "-Wall",
                        "-Wextra", "-fsanitize=undefined", "-fno-sanitize-recover=all",
                        str(HERE / "avoidance.cpp"), "-o", str(executable)], check=True)
        for n in args.orders:
            margin, m = estimate(n, executable)
            ppm = margin*1_000_000
            expected = {47: 1910, 53: 39773, 73: 6447}
            if n in expected:
                assert ppm.numerator//ppm.denominator == expected[n], (n, m, ppm)
            print(f"K{n}: at least {ppm.numerator//ppm.denominator} per million; worst m={m}",
                  flush=True)


if __name__ == "__main__":
    main()
