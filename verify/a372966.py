"""Numerical check for A372966: sigma_8(n^2) / sigma_4(n^2) == 1 (mod 240).

Checks:
  1. Lemma 1: x^8 == x^4 (mod 240) for all residues x,
  2. the first terms against the OEIS data,
  3. exact divisibility and the congruence for all n <= LIMIT,
  4. for n <= BRUTE_LIMIT, the divisor sums computed from the factorization
     against sums over an explicit list of divisors of n^2.
"""

LIMIT = 20000
BRUTE_LIMIT = 400
OEIS_DATA = [1, 241, 6481, 61681, 390001, 1561921, 5762401, 15790321,
             42521761, 93990241, 214344241, 399754561]


def factorize(n):
    factors = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def sigma_of_square(n, k):
    """sigma_k(n^2), computed from the factorization of n."""
    result = 1
    for p, e in factorize(n).items():
        result *= sum(p ** (k * i) for i in range(2 * e + 1))
    return result


def main():
    assert all(pow(x, 8, 240) == pow(x, 4, 240) for x in range(240))
    values = []
    for n in range(1, LIMIT + 1):
        s8 = sigma_of_square(n, 8)
        s4 = sigma_of_square(n, 4)
        assert s8 % s4 == 0, n
        values.append(s8 // s4)
        assert values[-1] % 240 == 1, n
    assert values[:len(OEIS_DATA)] == OEIS_DATA, "mismatch with OEIS data"
    for n in range(1, BRUTE_LIMIT + 1):
        divs = [d for d in range(1, n * n + 1) if (n * n) % d == 0]
        assert sum(d ** 8 for d in divs) == sigma_of_square(n, 8), n
        assert sum(d ** 4 for d in divs) == sigma_of_square(n, 4), n
    print(f"a(n) == 1 (mod 240) for all n <= {LIMIT}")


if __name__ == "__main__":
    main()
