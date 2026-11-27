"""Numerical check for A343752.

Checks for all n <= LIMIT:
  1. the first terms against the OEIS data,
  2. a(n) = n exactly when n is triangular,
  3. the closed form a(T_k + j) = (j + 1) * T_k + T_j for 0 <= j <= k.
"""

LIMIT = 10**6
OEIS_DATA = [1, 3, 3, 7, 12, 6, 13, 21, 30, 10, 21, 33, 46, 60, 15, 31, 48,
             66, 85, 105, 21, 43, 66, 90, 115, 141, 168, 28]


def tri(k):
    return k * (k + 1) // 2


def main():
    a = [0, 1]
    for n in range(2, LIMIT + 1):
        prev = a[-1]
        a.append(n if prev % n == 0 else prev + n)
    assert a[1:len(OEIS_DATA) + 1] == OEIS_DATA, "mismatch with OEIS data"

    k = 1
    while tri(k) <= LIMIT:
        for j in range(k + 1):
            n = tri(k) + j
            if n > LIMIT:
                break
            assert a[n] == (j + 1) * tri(k) + tri(j), n
            assert (a[n] == n) == (j == 0), n
        k += 1
    print(f"closed form and equivalence hold for all n <= {LIMIT}")


if __name__ == "__main__":
    main()
