"""Numerical check for A365849.

The sequence is computed from its definition: triangular numbers that are
the product of two distinct primes, both congruent to 3 modulo 4. Checks:
  1. the first terms against the OEIS data,
  2. every term equals r * (2r + 1) with r, 2r + 1 prime and r == 3 (mod 4),
     and every such r gives a term,
  3. every term except 21 is congruent to 1 modulo 36,
  4. the differences between the terms after the first have gcd 36, so no
     larger modulus gives them a common residue.
"""
from math import gcd

M_LIMIT = 141420  # all triangular numbers m (m + 1) / 2 <= 10^10
OEIS_DATA = [21, 253, 1081, 13861, 34453, 64261, 73153, 114481, 126253,
             258121, 351541, 371953, 392941, 482653]


def is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def prime_factors(n):
    """Prime factors of n with multiplicity, by trial division."""
    out = []
    p = 2
    while p * p <= n:
        while n % p == 0:
            out.append(p)
            n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def main():
    terms = []
    for m in range(1, M_LIMIT + 1):
        # m and m + 1 are coprime, so factor them separately.
        fs = prime_factors(m) + prime_factors(m + 1)
        fs.remove(2)  # divide the product m (m + 1) by 2
        if len(fs) == 2 and fs[0] != fs[1] and all(p % 4 == 3 for p in fs):
            terms.append(m * (m + 1) // 2)
    assert terms[:len(OEIS_DATA)] == OEIS_DATA, "mismatch with OEIS data"

    from_formula = [r * (2 * r + 1) for r in range(2, M_LIMIT // 2 + 1)
                    if r % 4 == 3 and is_prime(r) and is_prime(2 * r + 1)]
    assert terms == from_formula
    assert terms[0] == 21 and all(t % 36 == 1 for t in terms[1:])
    g = 0
    for t in terms[2:]:
        g = gcd(g, t - terms[1])
    assert g == 36
    print(f"{len(terms)} terms up to {terms[-1]}: all checks pass")


if __name__ == "__main__":
    main()
