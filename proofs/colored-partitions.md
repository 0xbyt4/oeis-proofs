# Colored partitions by color sum: A389343, A390208, A390217, A387957, A392002

## Statement

Fix $m \ge 1$. A partition of n with parts colored by $\{0, 1, \dots, m-1\}$
is a multiset of pairs (part, color) whose parts sum to n. Its color sum is
the sum of its colors. Let $N_{m,r}(n)$ be the number of such partitions of n
with color sum congruent to r modulo m, and let
$P(x) = \prod_{j \ge 1} 1/(1 - x^j)$ be the partition generating function.

Five OEIS entries, dated October to December 2025, carry conjectured generating functions of
this type. Status on 2026-11-26: all marked "Conjectured g.f.".

| Entry | m | r | Conjectured generating function |
| --- | --- | --- | --- |
| [A392002](https://oeis.org/A392002) | 2 | 1 | $(P(x)^2 - P(x^2))/2$ |
| [A389343](https://oeis.org/A389343) | 3 | 0 | $(P(x)^3 + 2P(x^3))/3$ |
| [A390208](https://oeis.org/A390208) | 3 | 1 or 2 | $(P(x)^3 - P(x^3))/3$ |
| [A390217](https://oeis.org/A390217) | 4 | 0 | $(P(x)^4 + P(x^2)^2 + 2P(x^4))/4$ |
| [A387957](https://oeis.org/A387957) | 4 | 1 or 3 | $(P(x)^4 - P(x^2)^2)/4$ |

**Theorem.** For all $m \ge 1$ and all integers r,

```math
\sum_{n \ge 0} N_{m,r}(n)\, x^n
  = \frac{1}{m} \sum_{d \mid m} c_d(r)\, P(x^d)^{m/d} ,
```

where $c_d(r)$ is the Ramanujan sum, the sum of $\xi^r$ over the primitive
d-th roots of unity $\xi$.

**Corollary.** The five conjectured generating functions in the table are
correct.

## Prior work

Checked on 2026-11-27. The five formulas are still marked "Conjectured g.f."
in the OEIS. A literature search found no proof and no statement of the
general theorem.

The method is standard: a roots-of-unity filter (series multisection) applied
to the two-variable generating function. For r = 0 the formula is also the
Burnside count of orbits of the cyclic group of order m acting on m-tuples of
partitions. Two special cases appear in the OEIS as comments without proof:
A281357 (m = 2, r = 0) and A109085 (colors 0 to n, color sum divisible by
n + 1). This note states and proves the general case and formalizes it.

The OEIS entries use the colors 0, 1, ..., m - 1, as this note does.

## Proof of the theorem

Let $p(n, s)$ be the number of colored partitions of n with color sum s. A
colored partition chooses a multiplicity for each pair (j, c), so

```math
F(x, y) = \sum_{n, s} p(n, s)\, x^n y^s
        = \prod_{j \ge 1} \prod_{c=0}^{m-1} \frac{1}{1 - y^c x^j} .
```

The coefficient of $x^n$ in F is a polynomial in y, so y may be specialized
to a complex number. Let $\omega = e^{2\pi i/m}$. Since
$\frac1m \sum_{k=0}^{m-1} \omega^{k(s-r)}$ is 1 if $s \equiv r \pmod m$ and 0
otherwise,

```math
\sum_{n \ge 0} N_{m,r}(n)\, x^n = \frac1m \sum_{k=0}^{m-1} \omega^{-kr}\, F(x, \omega^k) . \tag{1}
```

Fix k and let d be the order of $\zeta = \omega^k$, a divisor of m. As c runs
over $0, \dots, m-1$, the power $\zeta^c$ takes each d-th root of unity
exactly $m/d$ times, and $\prod_{\xi^d = 1} (1 - \xi X) = 1 - X^d$. Hence

```math
\prod_{c=0}^{m-1} (1 - \zeta^c X) = (1 - X^d)^{m/d},
\qquad
F(x, \omega^k) = \prod_{j \ge 1} (1 - x^{dj})^{-m/d} = P(x^d)^{m/d} .
```

Now group the terms of (1) by d. The numbers $\omega^k$ of order d are the
primitive d-th roots of unity, each occurring once, so the coefficient of
$P(x^d)^{m/d}$ is the sum of $\xi^{-r}$ over primitive d-th roots $\xi$.
Inversion $\xi \mapsto \xi^{-1}$ permutes them, so this sum equals $c_d(r)$.
$\blacksquare$

## Proof of the corollary

The Ramanujan sums needed are

| d | $c_d(r)$ |
| --- | --- |
| 1 | 1 |
| 2 | 1 if r is even, -1 if r is odd |
| 3 | 2 if 3 divides r, -1 otherwise |
| 4 | 2 if $r \equiv 0$, -2 if $r \equiv 2$, 0 if r is odd (mod 4) |

Substituting into the theorem:

- m = 2, r = 1: $(P(x)^2 - P(x^2))/2$.
- m = 3, r = 0: $(P(x)^3 + 2P(x^3))/3$.
- m = 3, r = 1 or 2: $(P(x)^3 - P(x^3))/3$.
- m = 4, r = 0: $(P(x)^4 + P(x^2)^2 + 2P(x^4))/4$.
- m = 4, r = 1 or 3: $(P(x)^4 - P(x^2)^2)/4$.

These are the entries of the table. $\blacksquare$

## Remarks

1. The Ramanujan sum $c_d(r)$ depends only on $\gcd(d, r)$. For a divisor d
   of m, $\gcd(d, r) = \gcd(d, \gcd(m, r))$. So the right side of the
   theorem, and hence the count $N_{m,r}(n)$, depends on r only through
   $\gcd(m, r)$. This explains the comments in A390208 and A387957 that
   different residues give the same sequence.
2. The theorem also gives the cases not listed above, for example
   m = 2, r = 0: $(P(x)^2 + P(x^2))/2$, and
   m = 4, r = 2: $(P(x)^4 + P(x^2)^2 - 2P(x^4))/4$.

## Verification

`verify/colored_partitions.py` counts the colored partitions directly for
all $m \le 8$ and all residues r, compares the result with the theorem, and
checks the five sequences against the OEIS data. The Ramanujan sums are
computed by the Mobius divisor formula and cross-checked against their
definition as sums over primitive roots of unity.

## Formalization

`OeisProofs/ColoredPartitions.lean` contains a complete Lean 4 proof of the
general theorem and of the five corollaries.

**Definitions.** A colored partition of n is a multiset of pairs
(part, color) with color in `Fin m`, positive parts, and parts summing to n,
exactly as in the statement above:

```lean
def coloredPartitions (m n : Nat) : Set (Multiset (Nat * Fin m)) :=
  {s | (forall x, x in s -> 0 < x.1) /\ (s.map Prod.fst).sum = n}
```

(shown in ASCII pseudo-notation; see the file for the exact text). `N m r n`
is the number of those with color sum congruent to r modulo m, and `T m n` is
the number of all of them. `coloredPartitions_finite` proves that the set is
finite, so these counts are meaningful.

**Main theorem.** `main` states, for every `m > 0` and all r and n, the
integer identity

```math
m \cdot N_{m,r}(n) = \sum_{d \mid m,\ d \mid n} c_d(r)\, T_{m/d}(n/d) ,
```

which is the theorem above read coefficient by coefficient, since the
coefficient of $x^n$ in $P(x^d)^{m/d}$ is $T_{m/d}(n/d)$ when d divides n and
0 otherwise. `main_powerSeries` is the same identity as an equation of power
series over the complex numbers.

**Links with the informal statement.**

- `T_one`: `T 1 k` is the number of partitions of k.
- `mk_T`: the generating function of `T c` is the c-th power of the partition
  generating function.
- `sum_primitiveRoots_pow`: the Ramanujan sum, defined in the file by the
  Mobius divisor formula, equals the sum of r-th powers of the primitive d-th
  roots of unity.
- `N_eq_of_gcd_eq`: `N m r n` depends on r only through `gcd(m, r)`
  (Remark 1).

**Corollaries.** The theorems `A392002`, `A389343`, `A390208`, `A390217` and
`A387957` are the five OEIS statements in the same coefficient form, for
example `2 * N 2 1 n = T 2 n - (if 2 | n then T 1 (n / 2) else 0)`.

**Check against the data.** `N` is defined as the cardinality of a set and is
not directly computable. The file defines a computable `Ncomp` and proves
`N_eq_card : N m r n = Ncomp m r n`; evaluating `Ncomp` reproduces the first
terms of the five OEIS sequences. That evaluation is a compiled computation,
not a kernel-checked proof.

The proofs depend only on the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

## References

1. OEIS Foundation Inc., *The On-Line Encyclopedia of Integer Sequences*,
   https://oeis.org. Entries A389343, A390208, A390217, A387957, A392002, A281357,
   A109085.
