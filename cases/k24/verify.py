"""Verify the K24 linear certificate over exact rational numbers."""
from collections import Counter
from fractions import Fraction as Q
from certificate import HERE, model_and_objective, ways


def main():
    model, goal = model_and_objective()
    coeff = Counter()
    rhs = Q(0)
    for line in (HERE/'cut-prices.txt').read_text().splitlines():
        name, raw = line.split()
        price = Q(raw)
        row, op, value = model.rows[name]
        assert op == '=' or (price >= 0 if op == '<=' else price <= 0)
        for var, a in row.items():
            coeff[var] += price*a
        rhs += price*value
    assert all(coeff[x] >= goal.get(x, 0) for x in coeff.keys() | goal.keys())
    assert rhs == Q(78926570703464883969, 79214135000000000000)
    assert rhs < 1
    print('Upper bound on losing partitions:', rhs)
    print('Lower bound on winning partitions:', (ways(8)*(1-rhs)).__ceil__())


if __name__ == '__main__':
    main()
