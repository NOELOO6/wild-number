"""Exact component averages and rooted-triple moment certificates. Python 3.10+."""
from fractions import Fraction
from functools import cache
from itertools import combinations
from math import comb, perm, prod
from pathlib import Path
import json


@cache
def completions(marked, triples, planted=True):
    """Marked endpoints must meet free endpoints; then pair the other free endpoints."""
    free = 3 * triples
    if not planted:
        size = marked + free
        return 0 if size % 2 else prod(range(1, size, 2))
    if free < marked or (free - marked) % 2:
        return 0
    return perm(free, marked) * prod(range(1, free - marked, 2))


def splits(groups):
    for count in range(len(groups) + 1):
        for indices in combinations(range(len(groups)), count):
            yield (tuple(v for i, v in enumerate(groups) if i in indices),
                   tuple(v for i, v in enumerate(groups) if i not in indices))


@cache
def connected(triples, groups, planted):
    total = completions(sum(groups), triples, planted)
    if not total or not (triples or groups):
        return 0
    if groups:
        # Specify the component of the first distinguished block.
        for inside, outside in splits(groups[1:]):
            for h in range(triples + 1):
                if outside or h < triples:
                    total -= (comb(triples, h) * connected(h, (groups[0],) + inside, planted)
                              * completions(sum(outside), triples - h, planted))
    else:
        # The first free triple serves as the distinguished block.
        for h in range(1, triples):
            total -= comb(triples - 1, h - 1) * connected(h, (), planted) * completions(0, triples - h, planted)
    return total


def conditional_mean(triples, groups, planted=True):
    denominator = completions(sum(groups), triples, planted)
    failure = 1 - Fraction(connected(triples, groups, planted), denominator)
    deficit = 0
    # Count components other than the one containing the root.
    for inside, outside in splits(groups[1:]):
        for h in range(triples + 1):
            deficit += (comb(triples, h) * connected(h, inside, planted)
                        * completions(groups[0] + sum(outside), triples - h, planted))
    return failure, Fraction(deficit, denominator)


def averages(n, groups):
    marked = sum(groups)
    triples = (n + 1 - marked) // 3
    profiles = [(n - comb(marked, 2), groups)]
    for i, m in enumerate(groups):
        for j in range(i + 1):
            new = list(groups)
            if j == i:
                if m < 2:
                    continue
                new[i] -= 2
                multiplicity = comb(m, 2)
            else:
                new[j] += new.pop(i) - 2
                multiplicity = m * groups[j]
            profiles.append((multiplicity, tuple(new)))
    failure = deficit = Fraction(0)
    for multiplicity, profile in profiles:
        f, d = conditional_mean(triples, profile)
        failure += multiplicity * f
        deficit += multiplicity * d
    return failure, deficit


def unrestricted_mean(n, groups):
    """With no planted block, all ends can pair, including ends in the distinguished groups."""
    t = (n + 1 - sum(groups)) // 3
    f, d = conditional_mean(t, groups, planted=False)
    return n*f, n*d


def elementary(a, b, c):
    """The first elementary symmetric polynomials of a ones, b twos and c threes."""
    p = a + 2*b + 3*c
    q = a + 4*b + 9*c
    r = a + 8*b + 27*c
    return (1, p, (p*p-q)//2, (p**3+2*r-3*p*q)//6)


def bounds(n, q, k):
    denominator = comb(q-1, 2) * k
    return (Fraction(q * max(0, q-(n+1)//2), denominator),
            Fraction(q * ((q-1)//2), denominator))


def surplus(n, marked, certificate, missing=0):
    if not certificate:
        return Fraction(0)
    u = n+1-marked
    t = u//3
    s0, s1 = map(Fraction, certificate["affine"])
    coeffs = []
    for entries in certificate["multipliers"]:
        coeff = [Fraction(0)]*4
        for j, pair in enumerate(entries):
            lower, upper = map(Fraction, pair)
            assert lower >= 0 and upper >= 0
            lo, hi = bounds(n, u-3*(j+1), j+1)
            coeff[j] += -lower*lo + upper*hi
            coeff[j+1] += lower-upper
        coeffs.append(coeff)
    for a in range(t+1):
        for b in range(t+1-a):
            for c in range(t+1-a-b):
                z = a+2*b+3*c
                counts = [a,b,c]
                score = s0+s1*z
                for index, count in enumerate(counts):
                    if count:
                        rest = counts.copy()
                        rest[index] -= 1
                        score += count * sum(x*y for x,y in zip(coeffs[index], elementary(*rest)))
                assert score <= max(0,z-2), (n, counts, score)
    incidences = u*((u-marked)//2) + comb(marked-1, 2)
    return s0 + s1*Fraction(incidences - (missing if s1 > 0 else 0), comb(u-1, 2))


def protection(n, frame, failure, deficit, gain):
    if frame is None:
        root = worst = failure/n
    else:
        groups = (1, *frame)
        triples = (n+1-sum(groups))//3
        probabilities = [conditional_mean(triples, groups)[0]]
        rooted = []
        for i, degree in enumerate(groups):
            for j in range(i+1):
                new = list(groups)
                if i == j:
                    if degree < 2:
                        continue
                    new[i] -= 2
                else:
                    new[j] += new.pop(i)-2
                probability = conditional_mean(triples, tuple(new))[0]
                probabilities.append(probability)
                if j == 0:
                    rooted.append(probability)
        root, worst = max(rooted), max(probabilities)
    def protected(mean):
        allowed = [k for k in range(n+1)
                   if mean-gain+min(2,k)*root+max(0,k-2)*worst < 2]
        return max(allowed, default=0)
    return [protected(deficit), protected(failure)]


def verify(path):
    rows = json.loads(Path(path).read_text())
    assert [r["n"] for r in rows] == [15, *range(19, 76, 2)]
    for row in rows:
        n, frame = row["n"], row["frame"]
        typical = n % 3
        fixed = (0,4,5)[typical]
        if frame is None:
            failure, deficit = unrestricted_mean(n, (1,fixed) if fixed else (1,))
            credit = 0
        else:
            assert all(v == 3 or (fixed and v == fixed) for v in frame)
            assert (fixed == 0 or frame.count(fixed) == 1)
            marked = 1+sum(frame)
            assert n+1 >= marked and (n+1-marked)%3 == 0
            assert all(b+comb(b,2)*(b-2) < n+1 for b in range(1,marked))
            failure, deficit = averages(n, (1, *frame))
            credit = surplus(n, marked, row.get("certificate"))
        # Report rigorous lower bounds per million layouts in the chosen family.
        near = max(0, 1-(deficit-credit)/2)
        colors = max(0, 1-(failure-credit)/2)
        result = [int(1000000*near), int(1000000*colors), int(1000000*max(0,1-deficit/3))]
        assert result == row["per_million"], (n,result)
        names = protection(n,frame,failure,deficit,credit)
        assert names == row["protect"]
        print(n, *result, *names)


if __name__ == "__main__":
    verify(Path(__file__).with_name("certificates.json"))
