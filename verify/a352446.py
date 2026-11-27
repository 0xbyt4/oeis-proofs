"""Numerical check for A352446, A341309, A204217 and A352269.

Partitions of n into consecutive parts are enumerated directly. Checks for
all n <= LIMIT:
  1. the generating function of A352446,
  2. A341309(n), defined as the sum of the odd divisors of n that are at most
     A003056(n), equals the total number of parts over odd numbers of parts,
  3. A352446(n) = A204217(n) - A341309(n), using the generating function of
     A204217 from its OEIS entry,
  4. the row sums of A352269 equal A341309(n),
  5. the divisor formula for A352446,
  6. the first terms against the OEIS data.
"""
from math import isqrt

LIMIT = 3000
A352446_DATA = [0, 0, 2, 0, 2, 0, 2, 0, 2, 4, 2, 0, 2, 4, 2, 0, 2, 4, 2, 0, 8,
                4, 2, 0, 2, 4, 8, 0, 2, 4, 2, 0, 8, 4, 2, 8, 2, 4, 8, 0, 2, 4,
                2, 8, 8]
A341309_DATA = [1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 9, 1, 1, 4, 1, 6, 4,
                1, 1, 4, 6, 1, 4, 8, 1, 9, 1, 1, 4, 1, 13, 4, 1, 1, 4, 6, 1,
                11, 1, 1, 18, 1, 1, 4, 8]
A204217_DATA = [1, 1, 3, 1, 3, 4, 3, 1, 6, 5, 3, 4, 3, 5, 11, 1, 3, 8, 3, 6,
                12, 5, 3, 4, 8, 5, 12, 8, 3, 13, 3, 1, 12, 5, 15, 12, 3, 5,
                12, 6, 3, 15, 3, 9, 26]


A352269_DATA = [1, 1, 1, 1, 1, 1, 3, 1, 0, 1, 0, 1, 3, 1, 0, 1, 0, 1, 3, 1, 0,
                1, 0, 1, 3, 5, 1, 0, 0, 1, 0, 0, 1, 3, 0, 1, 0, 0, 1, 0, 5, 1,
                3, 0, 1, 0, 0, 1, 0, 0, 1, 3, 0, 1, 0, 5, 1, 0, 0, 1]


def a003056(n):
    """Largest k with k (k + 1) / 2 <= n."""
    return (isqrt(8 * n + 1) - 1) // 2


def a352269_row(n):
    """Row n of A352269, from its definition."""
    row = []
    for k in range(1, (isqrt(8 * n + 1) + 1) // 4 + 1):
        parts = 2 * k - 1
        rest = n - parts * (parts - 1) // 2
        row.append(parts if rest > 0 and rest % parts == 0 else 0)
    return row


def main():
    even = [0] * (LIMIT + 1)   # total parts, even number of parts
    odd = [0] * (LIMIT + 1)    # total parts, odd number of parts
    for a in range(1, LIMIT + 1):
        total = 0
        k = 0
        while True:
            total += a + k
            k += 1
            if total > LIMIT:
                break
            (even if k % 2 == 0 else odd)[total] += k

    assert even[1:len(A352446_DATA) + 1] == A352446_DATA
    assert odd[1:len(A341309_DATA) + 1] == A341309_DATA

    gf = [0] * (LIMIT + 1)     # Statement 1
    h = 1
    while h * (2 * h + 1) <= LIMIT:
        for n in range(h * (2 * h + 1), LIMIT + 1, 2 * h):
            gf[n] += 2 * h
        h += 1
    assert gf == even

    a204217 = [0] * (LIMIT + 1)  # g.f. sum k x^(k(k+1)/2) / (1 - x^k)
    k = 1
    while k * (k + 1) // 2 <= LIMIT:
        for n in range(k * (k + 1) // 2, LIMIT + 1, k):
            a204217[n] += k
        k += 1
    assert a204217[1:len(A204217_DATA) + 1] == A204217_DATA

    triangle = []
    for n in range(1, LIMIT + 1):
        divs = [d for d in range(1, n + 1) if n % d == 0]
        assert odd[n] == sum(d for d in divs if d % 2 and d <= a003056(n))
        assert even[n] == a204217[n] - odd[n]
        row = a352269_row(n)
        triangle.extend(row)
        assert sum(row) == odd[n]
        assert even[n] == sum(2 * h for h in divs
                              if (n // h) % 2 and n // h >= 2 * h + 1)
    assert triangle[:len(A352269_DATA)] == A352269_DATA
    print(f"all four statements hold for all n <= {LIMIT}")


if __name__ == "__main__":
    main()
