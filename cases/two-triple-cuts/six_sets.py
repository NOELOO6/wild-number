"""A certificate for simultaneous closed six-sets in odd triple orders."""
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cache
from math import comb
from pathlib import Path
import argparse
import os
import subprocess
import sys
import tempfile

ABSORPTION = Path(__file__).resolve().parents[1] / "absorption"
sys.path.insert(0, str(ABSORPTION))
from small_components import avoidance_table, distinct_interval, SCALE
from check import completions, connected
from singleton_cuts import partitions


@cache
def region_labels(n, q):
    """Extrema for the sum of choose(i_c,3) on a q-point region."""
    if q < 6:
        return 0, 0
    total = comb(q, 2)
    mid, extra = divmod(total, n)
    least = n*comb(mid, 3) + extra*comb(mid, 2)
    low, high = max(0, q-(n+1)//2), q//2
    if low == high:
        return least, least
    full, rem = divmod(total-low*n, high-low)
    most = n*comb(low, 3) + full*(comb(high, 3)-comb(low, 3))
    most += comb(low+rem, 3)-comb(low, 3)
    return least, most


@dataclass(frozen=True)
class Bounds:
    vmin: int
    vmax: int
    bottom: F
    top: F
    max_lower: F
    lower_slope: F
    lower_intercept: F
    upper_slope: F
    upper_intercept: F

    def upper_mean(self, lower_v):
        return min(self.top, self.upper_intercept+self.upper_slope*max(self.vmin, lower_v))


def checker(n, executable, target):
    if n < 21 or n % 6 != 3 or n > 75:
        raise ValueError("Choose an odd multiple of three from 21 to 75.")
    t, k, w = n//3, (n-1)//2, comb(n, 2)
    labels = n*comb(k, 3)
    shape_mass = []
    den = completions(1, t)
    for j in range(2, t//2+1):
        a = j % 2
        count = (n*comb(t, j) * connected(j, (1,) if a else (), True)
                 * completions(1-a, t-j))
        shape_mass.append((j, a, (3*j-a)//2, F(count, den)))
    qs = {n, n-9, n-12, n-15, n-18, *(n-3*j for j, *_ in shape_mass)}
    tables = {q: avoidance_table(executable, n, 1, q) for q in qs}

    @cache
    def envelope(q, left, right):
        data = tables[q]
        rows = [(v, *data[v]) for v in range(left, min(right+1, len(data)))
                if data[v][0] <= data[v][1]]
        if not rows:
            raise AssertionError((q, left, right))
        v0, l0, h0 = rows[0]
        v1, l1, h1 = rows[-1]
        span = max(1, v1-v0)
        dl, dh = min(0, l1-l0), min(0, h1-h0)
        return Bounds(v0, v1, F(min(l for _, l, _ in rows), SCALE),
                      F(max(h for _, _, h in rows), SCALE), F(max(l for _, l, _ in rows), SCALE),
                      F(dl, span*SCALE), F(min(span*l-dl*v for v, l, _ in rows), span*SCALE),
                      F(dh, span*SCALE), F(max(span*h-dh*v for v, _, h in rows), span*SCALE))

    prob_one = F(10*partitions(t-2), partitions(t))
    prob_two = F(100*partitions(t-4), partitions(t))
    dis_min, dis_max = region_labels(n, n-6)
    third_max = region_labels(n, n-12)[1]
    vertex_degree = (n-1)*comb(k-1, 2)
    pair_degree = comb(k-1, 2)+(n-3)*(k-2)
    # A subdivision of the middle six-set uses an internal edge of its
    # chosen closing color on each triple in six of its ten subdivisions.
    shared_max = n-6-F(4, 10)+F(24, 10)*((n-12)//2)
    checked = 0
    least = 1
    for m in range((w+2)//3, w+1):
        full_lo, full_hi = tables[n][m]
        if full_lo > full_hi:
            continue
        bounds = {q: envelope(q, *distinct_interval(n, 1, n, w, m, q))
                  for q in qs if q != n}
        other = 0
        for j, a, b, mass in shape_mass:
            p3, p2 = F(comb(k-b, 3), comb(k, 3)), F(comb(k-b, 2), comb(k, 2))
            mean = F(m*(n-3*a), n)*p3 + F(3*m-w if a else 6*m, n)*(p2-p3)
            charge = mass*bounds[n-3*j].upper_mean(mean)
            if j == 2:
                labeled_charge = charge
            else:
                other += charge
        H = m*(n-6+3*(k-2))-w*(k-3)
        meet = m*(3*vertex_degree-3*pair_degree)+H
        sum_v = (m*labels-meet)*region_labels(n, n-9)[1]
        six, pair = bounds[n-6], bounds[n-12]
        centered_sum = sum_v-pair.vmin*labels*dis_min
        assert centered_sum >= 0
        third = (third_max*F(10*partitions(t-6), partitions(t-4))*bounds[n-18].top
                 + 2*shared_max/comb(n-13, 2)*bounds[n-15].top)
        base = F(full_lo, SCALE)-other
        intervals = [((labels+4)//5, labels)]
        while intervals:
            left, right = intervals.pop()
            min_neighbors = max((dis_min+4)//5, dis_min-(labels-left))
            max_neighbors = min(right, dis_max)
            pairs = left*min_neighbors
            assert pairs > 0
            lost = F(2*max_neighbors*H, 10)
            mean_v = min(pair.vmax, pair.vmin+F(centered_sum, pairs))
            lower_avoid = max(pair.bottom, pair.lower_intercept+pair.lower_slope*mean_v)
            A = prob_two*max(0, pair.bottom*(pairs-lost), pairs*lower_avoid-pair.max_lower*lost)
            B = prob_two*right*max_neighbors*third
            # Every nonnegative integer slope index is valid. Select the best
            # neighboring integers for these bounds, using the exact ratio.
            if A:
                y = 1+B//A
                credit = ((2*y+1)*A-B)/((y+1)*(y+2))
            else:
                credit = 0
            unique_hits = max(F(H, 5), H-9*(labels-left))
            six_cost = min(labeled_charge-prob_one*six.bottom*(labels-right),
                           right*prob_one*six.top) - prob_one*six.bottom*unique_hits/20
            margin = base-six_cost+credit
            if margin >= target:
                checked += 1
                least = min(least, margin)
            elif left < right:
                mid = (left+right)//2
                intervals.extend([(left, mid), (mid+1, right)])
            else:
                return False, m, left, margin
    return True, checked, least


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("order", type=int, default=75, nargs="?")
    parser.add_argument("--per-million", type=int, default=1500)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as temp:
        binary = Path(temp) / "avoidance"
        subprocess.run([os.environ.get("CXX", "c++"), "-std=c++17", "-O2", "-Wall", "-Wextra",
                        "-fsanitize=undefined", "-fno-sanitize-recover=all",
                        str(ABSORPTION / "avoidance.cpp"), "-o", str(binary)], check=True)
        result = checker(args.order, binary, F(args.per_million, 1_000_000))
        if not result[0]:
            _, m, e, bound = result
            raise AssertionError((args.order, m, e, bound))
        _, intervals, bound = result
        print(f"K{args.order}: {int(bound*1_000_000)} per million across {intervals} certified intervals")


if __name__ == "__main__":
    main()
