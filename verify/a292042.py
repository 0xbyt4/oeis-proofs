"""Numerical check for A292042 and A292043.

(i x; x)_infinity = A(x) + i B(x) is expanded with exact Gaussian integer
arithmetic and compared with
  2 A(x) = sum_n (-1)^(n(n-1)/2) x^(n(n-1)/2) / (x; x)_n,
  2 B(x) = sum_n (-1)^(n(n+1)/2) x^(n(n-1)/2) / (x; x)_n,
and with the OEIS data.
"""

TERMS = 400
A292042_DATA = [1, 0, 0, -1, -1, -2, -2, -3, -3, -4, -3, -4, -3, -3, -1, -1,
                2, 3, 7, 9, 14, 16, 23, 26, 33, 37, 45, 48, 57, 60, 68, 70]
A292043_DATA = [0, -1, -1, -1, -1, -1, 0, 0, 1, 2, 3, 4, 6, 7, 9, 10, 12, 13,
                15, 15, 16, 16, 16, 14, 13, 9, 6, 0, -5, -14, -22, -34, -45,
                -60, -74]


def main():
    # Product over k >= 1 of (1 - i x^k), as separate real and imaginary parts.
    re = [0] * TERMS
    im = [0] * TERMS
    re[0] = 1
    for k in range(1, TERMS):
        for n in range(TERMS - 1, k - 1, -1):
            # (re + i im) * (1 - i x^k): new[n] = old[n] - i * old[n - k]
            re[n], im[n] = re[n] + im[n - k], im[n] - re[n - k]
    assert re[:len(A292042_DATA)] == A292042_DATA
    assert im[:len(A292043_DATA)] == A292043_DATA

    two_a = [0] * TERMS
    two_b = [0] * TERMS
    inv = [1] + [0] * (TERMS - 1)   # 1 / (x; x)_n, updated as n grows
    n = 0
    while n * (n - 1) // 2 < TERMS:
        if n >= 1:
            for j in range(n, TERMS):   # divide by (1 - x^n)
                inv[j] += inv[j - n]
        e = n * (n - 1) // 2
        sign_a = -1 if e % 2 else 1
        sign_b = -1 if (n * (n + 1) // 2) % 2 else 1
        for j in range(TERMS - e):
            two_a[e + j] += sign_a * inv[j]
            two_b[e + j] += sign_b * inv[j]
        n += 1
    assert two_a == [2 * c for c in re]
    assert two_b == [2 * c for c in im]
    print(f"both formulas agree with the product to {TERMS} terms")


if __name__ == "__main__":
    main()
