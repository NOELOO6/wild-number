"""Bounds on repeated six-sets and on the two sides of a longer component."""
from fractions import Fraction as F
from math import comb

from check import completions, connected
from singleton_cuts import partitions


def connected_fraction(j, marked):
    return F(connected(j, marked, True), completions(sum(marked), j))


class RemainingRegions:
    def __init__(self, n, m, labels, root_labels, inside_hits, disjoint_triples,
                 region_labels, bounds, shapes):
        self.n, self.m, self.labels = n, m, labels
        self.H, self.bounds = inside_hits, bounds
        self.sl, self.sh = region_labels(n, n-6)
        self.rl, self.rh = region_labels(n, n-12)
        self.dlo, self.dhi = region_labels(n, n-9)
        self.vsum_lower = disjoint_triples*self.dlo*region_labels(n, n-15)[0]
        t, k = n//3, (n-1)//2
        outside = bounds[n-6].vmin
        self.duplicate_excess = max(0, outside*self.dlo-bounds[n-12].vmin*self.sh)
        self.third_probability = F(10*partitions(t-6), partitions(t-4))
        self.shared_probability = F(10*partitions(t-5), partitions(t))
        self.peer_count = n-6+3*(k-2)
        self.peer_pairs = ((comb(n, 3)-m)
                           * (self.peer_count*(self.peer_count-1)-3*(k-2)*(k-3)))
        self.long_sides = []
        for j, a, b, mass in shapes:
            if j < 3:
                continue
            q, r = n-3*j, t-j
            local_lo, local_hi = region_labels(n, q)
            local_hit_cap = min(inside_hits, bounds[q].vmax*(n-3+3*((q-4)//2)))
            p = F(10*partitions(r-2), partitions(r))
            disjoint = (region_labels(n, q-6)[1]*F(10*partitions(r-4), partitions(r-2))
                        * bounds[q-12].top)
            peers = n-6-F(4, 10)+F(24, 10)*((q-6)//2)
            shared = 2*peers/comb(q-7, 2)*bounds[q-9].top

            p3, p2 = F(comb(b, 3), comb(k, 3)), F(comb(b, 2), comb(k, 2))
            plain = connected_fraction(j-1, (1, 3) if a else (3,))
            internal = connected_fraction(j-1, (1, 1) if a else (1,))
            with_root = connected_fraction(j-1, (2,)) if a else 0
            marked = ((m*(n-6)+root_labels)*p3*plain
                      + (3*m-root_labels)*p2*(internal+with_root))
            inside_loss = marked/(n*j*comb(3*j-1, 2)*connected_fraction(j, (1,) if a else ()))
            self.long_sides.append((mass, local_lo, local_hi, local_hit_cap, p, bounds[q-6].bottom,
                                    disjoint+shared, bounds[q].bottom, inside_loss))

    def pair_counts(self, left, right, min_count, max_count, centered, pair):
        missing_low, missing_high = self.labels-right, self.labels-left
        min_count = max(min_count, self.labels*self.sl-2*missing_high*self.sh)
        max_count = min(max_count, self.labels*self.sh-2*missing_low*self.sl+missing_high**2)
        centered -= max(0, 2*missing_low*self.duplicate_excess-missing_high**2*(pair.vmax-pair.vmin))
        return min_count, max_count, centered

    def third_bound(self, left, right, pmin, pmax, prob_two, shared_charge):
        n, labels = self.n, self.labels
        ds = self.bounds[n-18]
        least = max(pmin*max((self.rl+4)//5, self.rl-(labels-left)),
                    labels*self.sl*self.rl-3*(labels-left)*self.sh*self.rh)
        most = min(pmax*min(self.rh, right), labels*self.sh*self.rh)
        lab_lo, lab_hi = labels*self.sl*self.rl, labels*self.sh*self.rh
        missing_v = ds.vmax*lab_hi-self.vsum_lower
        mean = max(ds.vmin, ds.vmax-F(missing_v, least)) if least > 0 else ds.vmin
        counted = min(most*ds.upper_mean(mean),
                      lab_hi*ds.upper_mean(F(self.vsum_lower, lab_hi))-max(0, lab_lo-most)*ds.bottom)
        disjoint = prob_two*self.third_probability*counted
        unique_hits = max(F(self.H, 5), self.H-9*(labels-left))
        occurrences = 20*right-unique_hits
        shared_pairs = min(self.peer_pairs, occurrences*(self.peer_count-1))
        shared = min(prob_two*pmax*shared_charge,
                     self.shared_probability*self.dhi*shared_pairs*self.bounds[n-15].top)
        return disjoint+shared

    def long_credit(self, left, right):
        total = 0
        for mass, low, high, hits, p, floor, conditional, outside, inside in self.long_sides:
            count_low = max((low+4)//5, low-(self.labels-left))
            count_high = min(high, right)
            A = p*floor*max(0, count_low-F(hits, 10))
            B = p*count_high*conditional
            if A:
                y = B//A
                presence = max(0, ((2*y+2)*A-B)/((y+1)*(y+2)))
            else:
                presence = 0
            total += mass*(presence+inside*max(0, outside-presence))
        return total
