"""Independent exact controls for common messages and structured probes."""

from fractions import Fraction
from itertools import combinations, product


def require(condition, detail):
    if not condition:
        raise AssertionError(detail)


def interval_controls():
    intervals = [(Fraction(lo, 2), Fraction(hi, 2))
                 for lo in range(-2, 3) for hi in range(lo, 3)]
    count = 0
    for size in range(1, 5):
        for rows in combinations(intervals, size):
            endpoints = {value for row in rows for value in row}
            feasible = any(all(lo <= witness <= hi for lo, hi in rows) for witness in endpoints)
            pairwise = all(lo <= hi for lo, _ in rows for _, hi in rows)
            require(feasible == pairwise, "Interval feasibility disagrees with pairwise test")
            count += 1
    return count


def probe_controls():
    count = 0
    masks = range(8)
    for nonconstant in product(range(2), repeat=7):
        coeffs = (0,) + nonconstant
        degree = max((m.bit_count() for m in masks if coeffs[m]), default=0)
        evaluate = [sum(coeffs[m] for m in masks if m & s == m) % 2 for s in masks]
        for protected in masks:
            region = [s for s in masks if not s & protected]
            full = all(evaluate[s] == 0 for s in region)
            probes = all(evaluate[s] == 0 for s in region if s.bit_count() <= degree)
            require(full == probes, "Triangular probe test disagrees with full enumeration")
            count += 1
    return count


def shared_code_control():
    for left, right in product(range(2), repeat=2):
        message = left ^ right
        require(message ^ right == left and message ^ left == right, "Incorrect decoding")
    edges = [(i, (i + 1) % 5) for i in range(5)]
    valid = lambda code: all(code[i] != code[j] for i, j in edges)
    require(not any(valid(code) for code in product(range(2), repeat=5)), "C5 has no 2-coloring")
    require(valid((0, 1, 0, 1, 2)), "C5 three-color witness")
    return 5


if __name__ == "__main__":
    print("Exact interval systems:", interval_controls())
    print("Binary protection contracts:", probe_controls())
    print("Shared-message controls:", shared_code_control())
