"""Numerical check for colored partitions counted by color sum modulo m.

Partitions with parts colored by {0, ..., m - 1} are counted directly by
residue of the color sum, for all m <= M_MAX, and compared with

    (1 / m) * sum over d | m of c_d(r) * P(x^d)^(m / d),

where c_d(r) is the Ramanujan sum and P is the partition generating
function. The five OEIS entries are checked against their data.
"""
import cmath
from math import gcd

TERMS = 60
M_MAX = 8
OEIS_DATA = {
    (2, 1): ("A392002", [0, 1, 2, 5, 9, 18, 31, 55, 90, 150, 237, 376, 577,
                         885, 1325, 1978, 2900, 4235, 6100, 8745, 12400,
                         17501, 24477]),
    (3, 0): ("A389343", [1, 1, 3, 8, 17, 36, 75, 143, 270, 495, 880, 1533,
                         2626, 4403, 7281, 11865, 19074, 30294, 47597, 73970,
                         113883]),
    (3, 1): ("A390208", [0, 1, 3, 7, 17, 36, 73, 143, 270, 492, 880, 1533,
                         2621, 4403, 7281, 11858, 19074, 30294, 47586, 73970,
                         113883]),
    (4, 0): ("A390217", [1, 1, 4, 10, 28, 63, 146, 310, 651, 1295, 2536, 4802,
                         8941, 16240, 29050, 50996, 88303, 150587, 253720]),
    (4, 1): ("A387957", [0, 1, 3, 10, 25, 63, 141, 310, 640, 1295, 2518, 4802,
                         8907, 16240, 28995, 50996, 88208, 150587, 253570]),
}


def count_by_residue(m):
    """state[n][r] = number of colored partitions of n with color sum r mod m."""
    state = [[0] * m for _ in range(TERMS)]
    state[0][0] = 1
    for part in range(1, TERMS):
        for color in range(m):
            for n in range(part, TERMS):
                prev = state[n - part]
                row = state[n]
                for r in range(m):
                    row[r] += prev[(r - color) % m]
    return state


def ramanujan_sum(d, r):
    """Sum of xi^r over primitive d-th roots of unity, via the divisor formula."""
    g = gcd(d, r)
    return sum(mobius(d // e) * e for e in range(1, g + 1) if g % e == 0)


def ramanujan_sum_from_roots(d, r):
    """The definition: sum of xi^r over primitive d-th roots of unity xi."""
    total = sum(cmath.exp(2j * cmath.pi * k * r / d)
                for k in range(d) if gcd(k, d) == 1)
    assert abs(total.imag) < 1e-9 and abs(total.real - round(total.real)) < 1e-9
    return round(total.real)


def mobius(n):
    result = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            result = -result
        p += 1
    return -result if n > 1 else result


def partition_power(step, power):
    """Coefficients of P(x^step)^power."""
    series = [1] + [0] * (TERMS - 1)
    for j in range(step, TERMS, step):
        for _ in range(power):
            for n in range(j, TERMS):
                series[n] += series[n - j]
    return series


def main():
    for d in range(1, M_MAX + 1):
        for r in range(2 * d):
            assert ramanujan_sum(d, r) == ramanujan_sum_from_roots(d, r), (d, r)
    for m in range(1, M_MAX + 1):
        state = count_by_residue(m)
        for r in range(m):
            total = [0] * TERMS
            for d in range(1, m + 1):
                if m % d == 0:
                    c = ramanujan_sum(d, r)
                    series = partition_power(d, m // d)
                    for n in range(TERMS):
                        total[n] += c * series[n]
            direct = [state[n][r] for n in range(TERMS)]
            assert total == [m * v for v in direct], (m, r)
            if (m, r) in OEIS_DATA:
                name, data = OEIS_DATA[(m, r)]
                assert direct[:len(data)] == data, name
    print(f"theorem holds for all m <= {M_MAX}, all residues, {TERMS} terms")


if __name__ == "__main__":
    main()
