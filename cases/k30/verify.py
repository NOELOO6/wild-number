"""Verify the K30 arithmetic with exact fractions and the supplied price vector."""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
from counts import LABELS, check_small_graphs, choose, long_model, short_loss, ways


def check_long():
    model = long_model()
    weights = {key: Q(value) for key, value in
               (line.split() for line in Path(__file__).with_name('long-prices.txt').read_text().splitlines())}
    coeff = Counter()
    total = Q(0)
    for name, price in weights.items():
        row, op, rhs = model.rows[name]
        assert op == '=' or (price >= 0 if op == '<=' else price <= 0)
        total += price*rhs
        for v, a in row.items():
            coeff[v] += price*a
    coeff['y0_0_0'] -= 1
    coeff['D'] += Q(1, 18000)
    assert all(q >= 0 for q in coeff.values()), 'negative reduced cost'
    assert total < Q(703, 1000)
    return total


def main():
    check_small_graphs()
    bound = check_long()
    long_mass = Q(29 * choose(15, 6) * ways(4)*ways(6), ways(10))
    worst = max((short_loss(d) + long_mass*min(1, bound + Q(d, 18000)), d)
                for d in range(LABELS + 1))
    assert worst[0] < 1, worst
    print('Upper bound on the fraction of losing partitions:', worst[0])
    print('Approximation:', float(worst[0]), 'at multiplicity defect', worst[1])
    winners = (ways(10)*(1-worst[0])).__ceil__()
    print('Lower bound on winning unordered partitions:', winners)


if __name__ == '__main__':
    main()
