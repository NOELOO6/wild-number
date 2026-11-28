"""Exact absorption bounds for a specified ordinary pair. Python standard library only."""
from fractions import Fraction as Q
from functools import cache
from math import comb, factorial


@cache
def ways(t):
    return factorial(3*t) // (6**t * factorial(t))


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def masses(n):
    """Expected number of charged closed sides of each size, before forbidden-triple avoidance."""
    u = n-2
    t = u//3
    assert n % 6 == 5 and t % 2 == 1
    # (multiplicity with penalty, number of forced free endpoints, sides).
    # Each side records its number of forced ends and whether it consists of the root alone.
    profiles = [(n-3, 3, ((0,False),(1,True),(2,False),(3,False))),
                (2, 1, ((0,False),(1,False))),
                (2, 1, ((0,False),(1,True)))]
    result = []
    for j in range(1, t//2+1):
        count = 0
        for colors, marked, sides in profiles:
            for inside, root in sides:
                if j == 1 and root:
                    continue
                if (3*j-inside) % 2 == 0:
                    count += colors*choose((u-marked)//2, (3*j-inside)//2)
        result.append(Q(count*ways(j)*ways(t-j),ways(t)))
    return result


def region_policy(n, m):
    u = n-2
    full = comb(n,2)
    degree = 3*(n-1)//2
    free_degree = 3*(u-1)//2
    w = full-2*degree+3

    @cache
    def allowed(q, used):
        k = n-q
        labeled_lo = max(0, full-degree*k+2*comb(k,2),
                         q*max(0,q-(n+1)//2), w-(u-q)*free_degree)
        labeled_hi = min(comb(q,2), full-degree*k+3*comb(k,2)-used, w)
        lo = max((labeled_lo+2)//3, labeled_lo-(w-m), m-(u-q)*free_degree)
        hi = min(comb(q,3), labeled_hi, m-max(used,(w-labeled_hi+2)//3))
        return lo, hi
    return allowed


def avoidance(q, allowed):
    """Odd/even inclusion-exclusion bounds, with a disjoint-pair bound on the upper side."""
    lower, upper = Q(0), Q(1)
    depth = min(6, q//3)
    for k in range(1, depth+1):
        a = b = Q(1)
        for j in reversed(range(k)):
            v = q-3*j
            l, h = allowed(v,j)
            den = comb(v-1,2)*(j+1)
            a, b = 1-(h if b>=0 else l)*b/den, 1-(l if a>=0 else h)*a/den
        if k % 2:
            lower = max(lower,a)
        else:
            upper = min(upper,b)
    if depth < 2:
        return lower,upper
    a,h = allowed(q,0)
    if a == 0:
        return lower,upper
    den = comb(q-1,2)
    # Thin the family to exactly a triples, and bound its ordered disjoint pairs.
    pairs = min(a*(a-1), a*(a+8)-(9*a*a+q-1)//q)
    degree = 3*(q-1)//2
    for k in range(2,depth+1,2):
        lo = hi = Q(1)
        for j in reversed(range(2,k)):
            v = q-3*j
            u_lo,u_hi = allowed(v,j)
            a_lo = max(0, a-3*j*degree, u_lo-(h-a))
            a_hi = min(a-j,u_hi)
            d = comb(v-1,2)*(j+1)
            lo,hi = 1-(a_hi if hi>=0 else a_lo)*hi/d, 1-(a_lo if lo>=0 else a_hi)*lo/d
        if hi >= 0:
            upper = min(upper,1-Q(a,den)+Q(pairs,2*den*comb(q-4,2))*hi)
    return lower,upper


def verify(n, per_million):
    u = n-2
    marks = comb(n,2)-3*(n-1)+3
    rates = masses(n)
    best = Q(1)
    for m in range((marks+2)//3, marks+1):
        allowed = region_policy(n,m)
        lower = avoidance(u,allowed)[0]
        upper_cost = sum(w*avoidance(u-3*j,allowed)[1] for j,w in enumerate(rates,1))
        best = min(best, lower-upper_cost/2)
    count = (1000000*best).__floor__()
    assert count >= per_million, (n,count,per_million)
    print(f"K{n}: at least {count} repairable partitions per million",flush=True)


if __name__ == "__main__":
    for n,bound in [(59,4000),(65,43000),(71,73000)]:
        verify(n,bound)
