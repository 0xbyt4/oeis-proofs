"""Numerical check for A306598: sign of the circulant determinant of divisors.

Checks, with exact integer arithmetic:
  1. the first terms against the OEIS data,
  2. a(n) > 0 for squares and a(n) < 0 for non-squares, n <= LIMIT,
  3. Theorem 1 on random strictly increasing positive integer sequences,
  4. the divisibility statements of Remark 1.
"""
import random
from math import isqrt

LIMIT = 3000
OEIS_DATA = [1, -3, -8, 49, -24, -960, -48, -3375, 676, -8640, -120,
             -2247392, -168, -34560, -46080, 923521]


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def circulant(first_column):
    t = len(first_column)
    return [[first_column[(i - j) % t] for j in range(t)] for i in range(t)]


def det(matrix):
    """Exact determinant by fraction-free (Bareiss) elimination."""
    m = [row[:] for row in matrix]
    n = len(m)
    sign = 1
    prev = 1
    for k in range(n - 1):
        if m[k][k] == 0:
            for i in range(k + 1, n):
                if m[i][k] != 0:
                    m[k], m[i] = m[i], m[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                m[i][j] = (m[i][j] * m[k][k] - m[i][k] * m[k][j]) // prev
        prev = m[k][k]
    return sign * m[n - 1][n - 1]


def main():
    values = [det(circulant(divisors(n))) for n in range(1, LIMIT + 1)]
    assert values[:len(OEIS_DATA)] == OEIS_DATA, "mismatch with OEIS data"
    for n, v in enumerate(values, start=1):
        is_square = isqrt(n) ** 2 == n
        assert (v > 0) if is_square else (v < 0), n
        divs = divisors(n)
        assert v % sum(divs) == 0, n
        if not is_square:
            # alternating sum of divisors starting with n (A071324)
            alt = sum(d if i % 2 == 0 else -d
                      for i, d in enumerate(reversed(divs)))
            assert v % (sum(divs) * alt) == 0, n
    print(f"sign rule holds for all n <= {LIMIT}")

    rng = random.Random(1)
    trials = 2000
    for _ in range(trials):
        t = rng.randint(1, 9)
        seq = sorted(rng.sample(range(1, 200), t))
        v = det(circulant(seq))
        assert v != 0 and (v > 0) == (t % 2 == 1), seq
    print(f"Theorem 1 holds on {trials} random increasing sequences")


if __name__ == "__main__":
    main()
