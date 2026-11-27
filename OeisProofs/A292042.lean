import Mathlib

/-!
# OEIS A292042 and A292043

Let `P(x) = prod_{k >= 1} (1 - i x^k) = A(x) + i B(x)`, a power series with
Gaussian integer coefficients. A292042 is the coefficient sequence of `A` and
A292043 is the coefficient sequence of `B`.

Main results (the first one is the conjecture in the formula section of
A292042, the second one is its companion for A292043):

  `2 A(x) = sum_{n >= 0} (-1)^(n(n-1)/2) x^(n(n-1)/2) / ((1-x)(1-x^2)...(1-x^n))`,
  `2 B(x) = sum_{n >= 0} (-1)^(n(n+1)/2) x^(n(n-1)/2) / ((1-x)(1-x^2)...(1-x^n))`.

See `proofs/A292042.md` for the informal proof.

## How the statement is formalized

No infinite product and no infinite sum is used.

* The coefficient of `x^m` in `P` only depends on the factors with `k <= m`.
  The sequences are defined through the truncated product `P m`, and
  `coeff_P_of_le` shows that every longer truncation has the same
  coefficient of `x^m`.
* The `n`-th summand on the right starts in degree `n(n-1)/2`, so only
  `n <= m + 1` contributes to the coefficient of `x^m`. The theorems
  `two_mul_a` and `two_mul_b` are stated for the coefficient of
  `x^m` of the partial sum over `n < m + 2`, with the inverse taken in
  `PowerSeries ℚ`. The variants `two_mul_a_of_le` and
  `two_mul_b_of_le` show that every longer partial sum gives the same
  coefficient.
* `two_mul_a_int` and `two_mul_b_int` are the same statements
  over `ℤ`, with the explicit inverse `invQ n` of `(1-x)...(1-x^n)`
  (see `invQ_mul_prod`).

## Proof

The proof goes through the finite form of Euler's identity (`finite_euler`):

  `prod_{k < M} (1 - z x^k)
    = sum_{n <= M} (-z)^n x^(n(n-1)/2) prod_{j < n} (1 - x^(M-j)) / ((1-x)...(1-x^n))`,

proved by induction on `M`. The numerator `prod_{j < n} (1 - x^(M-j))` is `1`
modulo `x^(M+1-n)`, and `n(n-1)/2 + M + 1 - n >= M`, so the numerator can be
dropped modulo `x^M` (`coeff_euler`). Setting `z = i` and comparing real and
imaginary parts gives the result.
-/

namespace OeisProofs.A292042

open PowerSeries Finset

/-! ### The sequences -/

/-- The truncated product `prod_{k = 1}^{N} (1 - i x^k)`, a power series with
Gaussian integer coefficients. Here `⟨0, 1⟩` is the imaginary unit. -/
noncomputable def P (N : ℕ) : GaussianInt⟦X⟧ :=
  ∏ k ∈ Finset.Icc 1 N, (1 - C (⟨0, 1⟩ : GaussianInt) * X ^ k)

/-- A292042: real part of the coefficient of `x^m` in `prod_{k >= 1} (1 - i x^k)`.
Only the factors with `k <= m` matter, see `coeff_P_of_le`. -/
noncomputable def a (m : ℕ) : ℤ := (coeff m (P m)).re

/-- A292043: imaginary part of the coefficient of `x^m` in
`prod_{k >= 1} (1 - i x^k)`. -/
noncomputable def b (m : ℕ) : ℤ := (coeff m (P m)).im

/-- An explicit inverse of `(1 - x)(1 - x^2)...(1 - x^n)` over the integers. -/
noncomputable def invQ (n : ℕ) : ℤ⟦X⟧ :=
  invOfUnit (∏ k ∈ Finset.Icc 1 n, (1 - X ^ k)) 1

/-! ### Results for a general coefficient ring -/

section General

variable {R : Type*} [CommRing R]

theorem le_triangle_add_one (n : ℕ) : n ≤ n * (n - 1) / 2 + 1 := by
  cases n with
  | zero => simp
  | succ k => rw [Nat.triangle_succ]; omega

/-- The coefficient of `x^m` in `prod_{k = 1}^{N} (1 - z x^k)` does not depend
on `N` as soon as `N >= m`. -/
theorem coeff_prod_Icc_of_le (z : R) {m N : ℕ} (h : m ≤ N) :
    coeff m (∏ k ∈ Icc 1 N, (1 - C z * X ^ k)) =
      coeff m (∏ k ∈ Icc 1 m, (1 - C z * X ^ k)) := by
  induction N, h using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    have e : (∏ k ∈ Icc 1 N, (1 - C z * X ^ k)) * (1 - C z * X ^ (N + 1)) =
        (∏ k ∈ Icc 1 N, (1 - C z * X ^ k)) -
          X ^ (N + 1) * (C z * ∏ k ∈ Icc 1 N, (1 - C z * X ^ k)) := by ring
    rw [prod_Icc_succ_top (by omega), e, map_sub, ih, coeff_X_pow_mul',
      ite_eq_right (by omega), sub_zero]

theorem prod_range_shift (f : ℕ → R⟦X⟧) (m : ℕ) :
    ∏ k ∈ range m, f (k + 1) = ∏ k ∈ Icc 1 m, f k := by
  induction m with
  | zero => simp
  | succ m ih => rw [prod_range_succ, prod_Icc_succ_top (by omega), ih]

variable (R) in
/-- The numerator `prod_{j < n} (1 - x^(M-j))` of the Gaussian binomial
coefficient `[M choose n]`. It vanishes for `n > M`. -/
noncomputable def num (M n : ℕ) : R⟦X⟧ := ∏ j ∈ range n, (1 - X ^ (M - j))

theorem num_succ (M n : ℕ) : num R M (n + 1) = num R M n * (1 - X ^ (M - n)) :=
  prod_range_succ _ _

theorem num_succ_succ (M n : ℕ) :
    num R (M + 1) (n + 1) = (1 - X ^ (M + 1)) * num R M n := by
  unfold num
  rw [prod_range_succ']
  simp [mul_comm]

theorem num_eq_zero {M n : ℕ} (h : M < n) : num R M n = 0 :=
  prod_eq_zero (mem_range.2 h) (by simp)

theorem X_pow_dvd_num_sub_one {M n : ℕ} (h : n ≤ M) :
    (X : R⟦X⟧) ^ (M + 1 - n) ∣ num R M n - 1 := by
  induction n with
  | zero => simp [num]
  | succ n ih =>
    have h1 := ih (by omega)
    have e : num R M (n + 1) - 1 =
        (num R M n - 1) - X ^ (M + 1 - (n + 1)) * num R M n := by
      rw [num_succ, show M + 1 - (n + 1) = M - n by omega]; ring
    rw [e]
    exact dvd_sub ((pow_dvd_pow _ (by omega)).trans h1) (dvd_mul_right _ _)

/-- The `n`-th term of the finite Euler identity. -/
noncomputable def term (z : R) (Qi : ℕ → R⟦X⟧) (M n : ℕ) : R⟦X⟧ :=
  (-C z) ^ n * X ^ (n * (n - 1) / 2) * num R M n * Qi n

theorem one_sub_mul_inv {Qi : ℕ → R⟦X⟧}
    (hQ : ∀ n, (∏ k ∈ Icc 1 n, (1 - (X : R⟦X⟧) ^ k)) * Qi n = 1) (n : ℕ) :
    (1 - X ^ (n + 1)) * Qi (n + 1) = Qi n := by
  have h1 := hQ (n + 1)
  rw [prod_Icc_succ_top (by omega)] at h1
  calc (1 - X ^ (n + 1)) * Qi (n + 1)
      = ((∏ k ∈ Icc 1 n, (1 - (X : R⟦X⟧) ^ k)) * Qi n) *
          ((1 - X ^ (n + 1)) * Qi (n + 1)) := by rw [hQ, one_mul]
    _ = Qi n * ((∏ k ∈ Icc 1 n, (1 - (X : R⟦X⟧) ^ k)) * (1 - X ^ (n + 1)) *
          Qi (n + 1)) := by ring
    _ = Qi n := by rw [h1, mul_one]

/-- The q-Pascal rule, in the form needed for the induction. -/
theorem term_succ_succ (z : R) {Qi : ℕ → R⟦X⟧}
    (hQ : ∀ n, (∏ k ∈ Icc 1 n, (1 - (X : R⟦X⟧) ^ k)) * Qi n = 1) {M n : ℕ}
    (h : n ≤ M) :
    term z Qi (M + 1) (n + 1) =
      term z Qi M (n + 1) + (-C z * X ^ M) * term z Qi M n := by
  have h1 := one_sub_mul_inv hQ n
  have h2 : (X : R⟦X⟧) ^ ((n + 1) * (n + 1 - 1) / 2) * X ^ (M - n) =
      X ^ (n * (n - 1) / 2) * X ^ M := by
    rw [← pow_add, ← pow_add, Nat.triangle_succ]
    congr 1
    omega
  have h3 : (X : R⟦X⟧) ^ (M + 1) = X ^ (M - n) * X ^ (n + 1) := by
    rw [← pow_add]
    congr 1
    omega
  unfold term
  rw [num_succ_succ, num_succ, h3]
  calc (-C z) ^ (n + 1) * X ^ ((n + 1) * (n + 1 - 1) / 2) *
        ((1 - X ^ (M - n) * X ^ (n + 1)) * num R M n) * Qi (n + 1)
      = (-C z) ^ (n + 1) * X ^ ((n + 1) * (n + 1 - 1) / 2) *
          (num R M n * (1 - X ^ (M - n))) * Qi (n + 1) +
        (-C z) ^ (n + 1) * (X ^ ((n + 1) * (n + 1 - 1) / 2) * X ^ (M - n)) *
          num R M n * ((1 - X ^ (n + 1)) * Qi (n + 1)) := by ring
    _ = _ := by rw [h1, h2]; ring

/-- Finite form of Euler's identity (a case of the q-binomial theorem):
`prod_{k < M} (1 - z x^k) = sum_{n <= M} (-z)^n x^(n(n-1)/2) [M choose n]`,
where the Gaussian binomial coefficient is written as `num R M n * Qi n` and
`Qi n` is any inverse of `(1 - x)...(1 - x^n)`. -/
theorem finite_euler (z : R) {Qi : ℕ → R⟦X⟧}
    (hQ : ∀ n, (∏ k ∈ Icc 1 n, (1 - (X : R⟦X⟧) ^ k)) * Qi n = 1) (M : ℕ) :
    ∏ k ∈ range M, (1 - C z * X ^ k) = ∑ n ∈ range (M + 1), term z Qi M n := by
  induction M with
  | zero =>
    have := hQ 0
    simp only [Icc_eq_empty_of_lt Nat.zero_lt_one, prod_empty, one_mul] at this
    simp [term, num, this]
  | succ M ih =>
    rw [prod_range_succ, ih, sum_range_succ' _ (M + 1)]
    have step : ∀ n ∈ range (M + 1), term z Qi (M + 1) (n + 1) =
        term z Qi M (n + 1) + (-C z * X ^ M) * term z Qi M n := fun n hn =>
      term_succ_succ z hQ (Nat.lt_succ_iff.1 (mem_range.1 hn))
    have h0 : term z Qi (M + 1) 0 = term z Qi M 0 := by simp [term, num]
    have hlast : ∑ n ∈ range (M + 1), term z Qi M (n + 1) + term z Qi M 0 =
        ∑ n ∈ range (M + 1), term z Qi M n := by
      rw [← sum_range_succ' (fun n => term z Qi M n) (M + 1), sum_range_succ]
      simp [term, num_eq_zero (lt_add_one M)]
    rw [sum_congr rfl step, sum_add_distrib, ← mul_sum, h0]
    linear_combination (-1 : R⟦X⟧) * hlast

theorem coeff_term (z : R) (Qi : ℕ → R⟦X⟧) {m M n : ℕ} (hm : m < M) (hn : n ≤ M) :
    coeff m (term z Qi M n) =
      coeff m ((-C z) ^ n * X ^ (n * (n - 1) / 2) * Qi n) := by
  obtain ⟨w, hw⟩ := X_pow_dvd_num_sub_one (R := R) hn
  have hnum : num R M n = 1 + X ^ (M + 1 - n) * w := by rw [← hw]; ring
  have e : term z Qi M n = (-C z) ^ n * X ^ (n * (n - 1) / 2) * Qi n +
      X ^ (n * (n - 1) / 2 + (M + 1 - n)) * ((-C z) ^ n * w * Qi n) := by
    unfold term
    rw [hnum, pow_add]
    ring
  rw [e, map_add, coeff_X_pow_mul', ite_eq_right, add_zero]
  have := le_triangle_add_one n
  omega

/-- Euler's identity modulo `x^(m+1)`:
`(1 - z) prod_{k = 1}^{m} (1 - z x^k)` and
`sum_{n < m + 2} (-z)^n x^(n(n-1)/2) / ((1 - x)...(1 - x^n))` have the same
coefficient of `x^m`. -/
theorem coeff_euler (z : R) {Qi : ℕ → R⟦X⟧}
    (hQ : ∀ n, (∏ k ∈ Icc 1 n, (1 - (X : R⟦X⟧) ^ k)) * Qi n = 1) (m : ℕ) :
    coeff m ((1 - C z) * ∏ k ∈ Icc 1 m, (1 - C z * X ^ k)) =
      coeff m (∑ n ∈ range (m + 2), (-C z) ^ n * X ^ (n * (n - 1) / 2) * Qi n) := by
  have hprod : ∏ k ∈ range (m + 1), (1 - C z * X ^ k) =
      (1 - C z) * ∏ k ∈ Icc 1 m, (1 - C z * X ^ k) := by
    rw [prod_range_succ', pow_zero, mul_one, mul_comm,
      prod_range_shift (fun k => 1 - C z * X ^ k)]
  rw [← hprod, finite_euler z hQ (m + 1), map_sum, map_sum]
  exact sum_congr rfl fun n hn =>
    coeff_term z Qi (lt_add_one m) (Nat.lt_succ_iff.1 (mem_range.1 hn))

/-- A series divisible by `x^(n(n-1)/2)` has no coefficient of `x^m` when
`n >= m + 2`. -/
theorem coeff_triangle_mul_eq_zero {m n : ℕ} (h : m + 2 ≤ n) (φ : R⟦X⟧) :
    coeff m (X ^ (n * (n - 1) / 2) * φ) = 0 := by
  rw [coeff_X_pow_mul', ite_eq_right]
  have := le_triangle_add_one n
  omega

theorem coeff_neg_one_pow_mul (m k : ℕ) (φ : R⟦X⟧) :
    coeff m ((-1) ^ k * φ) = (-1) ^ k * coeff m φ := by
  have : ((-1 : R⟦X⟧)) ^ k = C ((-1) ^ k) := by simp
  rw [this, coeff_C_mul]

end General

/-! ### Truncation independence -/

/-- The coefficient of `x^m` in `prod_{k = 1}^{N} (1 - i x^k)` is the same for
all `N >= m`. So `coeff m (P m)` is the coefficient of `x^m` in the infinite
product `prod_{k >= 1} (1 - i x^k)`. -/
theorem coeff_P_of_le {m N : ℕ} (h : m ≤ N) : coeff m (P N) = coeff m (P m) :=
  coeff_prod_Icc_of_le _ h

theorem a_eq_of_le {m N : ℕ} (h : m ≤ N) : a m = (coeff m (P N)).re := by
  rw [coeff_P_of_le h, a]

theorem b_eq_of_le {m N : ℕ} (h : m ≤ N) : b m = (coeff m (P N)).im := by
  rw [coeff_P_of_le h, b]

/-! ### The inverse of `(1 - x)...(1 - x^n)` -/

theorem constantCoeff_prod_one_sub_X_pow {R : Type*} [CommRing R] (n : ℕ) :
    constantCoeff (∏ k ∈ Icc 1 n, (1 - (X : R⟦X⟧) ^ k)) = 1 := by
  rw [map_prod]
  refine prod_eq_one fun k hk => ?_
  have hk0 : k ≠ 0 := by have := (mem_Icc.1 hk).1; omega
  simp [hk0]

/-- `invQ n` is the inverse of `(1 - x)(1 - x^2)...(1 - x^n)`. -/
theorem invQ_mul_prod (n : ℕ) : invQ n * ∏ k ∈ Icc 1 n, (1 - X ^ k) = 1 :=
  invOfUnit_mul _ _ (by rw [constantCoeff_prod_one_sub_X_pow, Units.val_one])

theorem map_prod_one_sub_X_pow {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) :
    PowerSeries.map f (∏ k ∈ Icc 1 n, (1 - (X : R⟦X⟧) ^ k)) =
      ∏ k ∈ Icc 1 n, (1 - (X : S⟦X⟧) ^ k) := by
  simp [map_prod]

/-- Over the rationals `invQ n` becomes the usual inverse. -/
theorem map_invQ (n : ℕ) :
    PowerSeries.map (Int.castRingHom ℚ) (invQ n) =
      (∏ k ∈ Icc 1 n, (1 - (X : ℚ⟦X⟧) ^ k))⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one
      (by rw [constantCoeff_prod_one_sub_X_pow]; exact one_ne_zero),
    ← map_prod_one_sub_X_pow (Int.castRingHom ℚ), ← map_mul, invQ_mul_prod, map_one]

/-! ### Real and imaginary parts -/

theorem re_sum (s : Finset ℕ) (f : ℕ → GaussianInt) :
    (∑ n ∈ s, f n).re = ∑ n ∈ s, (f n).re := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, Zsqrtd.re_add, ih]

theorem im_sum (s : Finset ℕ) (f : ℕ → GaussianInt) :
    (∑ n ∈ s, f n).im = ∑ n ∈ s, (f n).im := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, Zsqrtd.im_add, ih]

/-- `Re((-i)^n) - Im((-i)^n) = (-1)^(n(n-1)/2)` and
`Re((-i)^n) + Im((-i)^n) = (-1)^(n(n+1)/2)`. -/
theorem neg_I_pow (n : ℕ) :
    ((-(⟨0, 1⟩ : GaussianInt)) ^ n).re - ((-(⟨0, 1⟩ : GaussianInt)) ^ n).im =
        (-1) ^ (n * (n - 1) / 2) ∧
      ((-(⟨0, 1⟩ : GaussianInt)) ^ n).re + ((-(⟨0, 1⟩ : GaussianInt)) ^ n).im =
        (-1) ^ (n * (n + 1) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have t1 := Nat.triangle_succ (n + 1)
    have t2 := Nat.triangle_succ n
    simp only [Nat.add_sub_cancel] at t1 t2
    have e1 : (n + 1) * (n + 1 - 1) / 2 = n * (n + 1) / 2 := by
      rw [Nat.add_sub_cancel, mul_comm]
    have e2 : (n + 1) * (n + 1 + 1) / 2 = n * (n - 1) / 2 + (n + n) + 1 := by
      rw [mul_comm, t1, t2]; ring
    rw [pow_succ, e1, e2]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_neg, Zsqrtd.im_neg]
    constructor
    · linear_combination h2
    · rw [pow_succ, pow_add, Even.neg_one_pow ⟨n, rfl⟩]
      linear_combination -h1

/-- Euler's identity at `z = i`, coefficient of `x^m`. -/
theorem one_sub_I_mul_coeff_P (m : ℕ) :
    (1 - (⟨0, 1⟩ : GaussianInt)) * coeff m (P m) =
      ∑ n ∈ range (m + 2), (-(⟨0, 1⟩ : GaussianInt)) ^ n *
        ((coeff m (X ^ (n * (n - 1) / 2) * invQ n) : ℤ) : GaussianInt) := by
  have hQ : ∀ n, (∏ k ∈ Icc 1 n, (1 - (X : GaussianInt⟦X⟧) ^ k)) *
      PowerSeries.map (Int.castRingHom GaussianInt) (invQ n) = 1 := by
    intro n
    rw [← map_prod_one_sub_X_pow (Int.castRingHom GaussianInt), ← map_mul, mul_comm,
      invQ_mul_prod, map_one]
  have h := coeff_euler (⟨0, 1⟩ : GaussianInt) hQ m
  have e1 : (1 - C (⟨0, 1⟩ : GaussianInt) : GaussianInt⟦X⟧) =
      C (1 - (⟨0, 1⟩ : GaussianInt)) := by simp
  have e2 : ∀ n, (-C (⟨0, 1⟩ : GaussianInt)) ^ n * X ^ (n * (n - 1) / 2) *
      PowerSeries.map (Int.castRingHom GaussianInt) (invQ n) =
      C ((-(⟨0, 1⟩ : GaussianInt)) ^ n) *
        PowerSeries.map (Int.castRingHom GaussianInt) (X ^ (n * (n - 1) / 2) * invQ n) := by
    intro n
    simp [mul_assoc]
  rw [e1, coeff_C_mul, map_sum] at h
  rw [P, h]
  refine sum_congr rfl fun n _ => ?_
  rw [e2, coeff_C_mul, coeff_map, eq_intCast]

theorem a_add_b (m : ℕ) :
    a m + b m =
      ∑ n ∈ range (m + 2), ((-(⟨0, 1⟩ : GaussianInt)) ^ n).re *
        coeff m (X ^ (n * (n - 1) / 2) * invQ n) := by
  have h := congrArg Zsqrtd.re (one_sub_I_mul_coeff_P m)
  rw [re_sum] at h
  simp only [Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, mul_zero, add_zero] at h
  rw [← h, a, b]
  simp

theorem b_sub_a (m : ℕ) :
    b m - a m =
      ∑ n ∈ range (m + 2), ((-(⟨0, 1⟩ : GaussianInt)) ^ n).im *
        coeff m (X ^ (n * (n - 1) / 2) * invQ n) := by
  have h := congrArg Zsqrtd.im (one_sub_I_mul_coeff_P m)
  rw [im_sum] at h
  simp only [Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, mul_zero, zero_add] at h
  rw [← h, a, b]
  simp
  ring

/-! ### Main theorems over the integers -/

/-- The OEIS conjecture for A292042, over `ℤ`: `2 * a m` is the
coefficient of `x^m` in
`sum_{n < m + 2} (-1)^(n(n-1)/2) x^(n(n-1)/2) / ((1 - x)...(1 - x^n))`,
where `invQ n` is the inverse of `(1 - x)...(1 - x^n)` (`invQ_mul_prod`). -/
theorem two_mul_a_int (m : ℕ) :
    2 * a m =
      coeff m (∑ n ∈ Finset.range (m + 2),
        (-1 : ℤ⟦X⟧) ^ (n * (n - 1) / 2) * X ^ (n * (n - 1) / 2) * invQ n) := by
  have h1 := a_add_b m
  have h2 := b_sub_a m
  have h3 : 2 * a m = ∑ n ∈ range (m + 2), (-1) ^ (n * (n - 1) / 2) *
      coeff m (X ^ (n * (n - 1) / 2) * invQ n) := by
    have : 2 * a m = (a m + b m) - (b m - a m) := by ring
    rw [this, h1, h2, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [← (neg_I_pow n).1]
    ring
  rw [h3, map_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [mul_assoc, coeff_neg_one_pow_mul]

/-- The companion formula for A292043, over `ℤ`. -/
theorem two_mul_b_int (m : ℕ) :
    2 * b m =
      coeff m (∑ n ∈ Finset.range (m + 2),
        (-1 : ℤ⟦X⟧) ^ (n * (n + 1) / 2) * X ^ (n * (n - 1) / 2) * invQ n) := by
  have h1 := a_add_b m
  have h2 := b_sub_a m
  have h3 : 2 * b m = ∑ n ∈ range (m + 2), (-1) ^ (n * (n + 1) / 2) *
      coeff m (X ^ (n * (n - 1) / 2) * invQ n) := by
    have : 2 * b m = (a m + b m) + (b m - a m) := by ring
    rw [this, h1, h2, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [← (neg_I_pow n).2]
    ring
  rw [h3, map_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [mul_assoc, coeff_neg_one_pow_mul]

/-! ### Main theorems over the rationals -/

theorem map_summand (e n : ℕ) :
    PowerSeries.map (Int.castRingHom ℚ)
        ((-1 : ℤ⟦X⟧) ^ e * X ^ (n * (n - 1) / 2) * invQ n) =
      (-1 : ℚ⟦X⟧) ^ e * X ^ (n * (n - 1) / 2) *
        (∏ k ∈ Finset.Icc 1 n, (1 - X ^ k))⁻¹ := by
  rw [map_mul, map_invQ]
  simp

/-- **OEIS conjecture for A292042.** For every `m`, `2 * a m` is the
coefficient of `x^m` in
`sum_{n < m + 2} (-1)^(n(n-1)/2) x^(n(n-1)/2) / ((1 - x)(1 - x^2)...(1 - x^n))`.
The summands with `n >= m + 2` do not contribute to this coefficient, see
`two_mul_a_of_le`. -/
theorem two_mul_a (m : ℕ) :
    (2 * a m : ℚ) =
      coeff m (∑ n ∈ Finset.range (m + 2),
        (-1 : ℚ⟦X⟧) ^ (n * (n - 1) / 2) * X ^ (n * (n - 1) / 2) *
          (∏ k ∈ Finset.Icc 1 n, (1 - X ^ k))⁻¹) := by
  have h := congrArg (Int.castRingHom ℚ) (two_mul_a_int m)
  rw [← coeff_map, map_sum] at h
  simp only [map_summand] at h
  rw [← h]
  simp

/-- **Companion formula for A292043.** For every `m`, `2 * b m` is the
coefficient of `x^m` in
`sum_{n < m + 2} (-1)^(n(n+1)/2) x^(n(n-1)/2) / ((1 - x)(1 - x^2)...(1 - x^n))`. -/
theorem two_mul_b (m : ℕ) :
    (2 * b m : ℚ) =
      coeff m (∑ n ∈ Finset.range (m + 2),
        (-1 : ℚ⟦X⟧) ^ (n * (n + 1) / 2) * X ^ (n * (n - 1) / 2) *
          (∏ k ∈ Finset.Icc 1 n, (1 - X ^ k))⁻¹) := by
  have h := congrArg (Int.castRingHom ℚ) (two_mul_b_int m)
  rw [← coeff_map, map_sum] at h
  simp only [map_summand] at h
  rw [← h]
  simp

/-- The coefficient of `x^m` of the partial sums over `n < L` is the same for
all `L >= m + 2`. -/
theorem coeff_sum_range_of_le (e : ℕ → ℕ) {m L : ℕ} (hL : m + 2 ≤ L) :
    coeff m (∑ n ∈ Finset.range L,
        (-1 : ℚ⟦X⟧) ^ e n * X ^ (n * (n - 1) / 2) *
          (∏ k ∈ Finset.Icc 1 n, (1 - X ^ k))⁻¹) =
      coeff m (∑ n ∈ Finset.range (m + 2),
        (-1 : ℚ⟦X⟧) ^ e n * X ^ (n * (n - 1) / 2) *
          (∏ k ∈ Finset.Icc 1 n, (1 - X ^ k))⁻¹) := by
  rw [map_sum, map_sum]
  refine (sum_subset (range_subset_range.2 hL) fun n _ hn => ?_).symm
  have hn' : m + 2 ≤ n := by simpa using hn
  rw [mul_assoc, mul_left_comm, coeff_triangle_mul_eq_zero hn']

/-- The formula for A292042 with an arbitrary long partial sum. -/
theorem two_mul_a_of_le {m L : ℕ} (hL : m + 2 ≤ L) :
    (2 * a m : ℚ) =
      coeff m (∑ n ∈ Finset.range L,
        (-1 : ℚ⟦X⟧) ^ (n * (n - 1) / 2) * X ^ (n * (n - 1) / 2) *
          (∏ k ∈ Finset.Icc 1 n, (1 - X ^ k))⁻¹) := by
  rw [coeff_sum_range_of_le (fun n => n * (n - 1) / 2) hL, two_mul_a]

/-- The formula for A292043 with an arbitrary long partial sum. -/
theorem two_mul_b_of_le {m L : ℕ} (hL : m + 2 ≤ L) :
    (2 * b m : ℚ) =
      coeff m (∑ n ∈ Finset.range L,
        (-1 : ℚ⟦X⟧) ^ (n * (n + 1) / 2) * X ^ (n * (n - 1) / 2) *
          (∏ k ∈ Finset.Icc 1 n, (1 - X ^ k))⁻¹) := by
  rw [coeff_sum_range_of_le (fun n => n * (n + 1) / 2) hL, two_mul_b]

/-! ### Sanity check against the OEIS data -/

/-- A computable twin of the coefficients of `P N`: `coeffP N m` is the pair
(real part, imaginary part) of the coefficient of `x^m` in
`prod_{k = 1}^{N} (1 - i x^k)`, computed with the recurrence
`P (N + 1) = P N - i x^(N + 1) P N`. -/
def coeffP : ℕ → ℕ → ℤ × ℤ
  | 0, m => if m = 0 then (1, 0) else (0, 0)
  | N + 1, m =>
    if N + 1 ≤ m then
      ((coeffP N m).1 + (coeffP N (m - (N + 1))).2,
        (coeffP N m).2 - (coeffP N (m - (N + 1))).1)
    else coeffP N m

theorem coeff_P (N m : ℕ) : coeff m (P N) = ⟨(coeffP N m).1, (coeffP N m).2⟩ := by
  induction N generalizing m with
  | zero =>
    simp only [P, Icc_eq_empty_of_lt Nat.zero_lt_one, prod_empty, coeff_one, coeffP]
    split_ifs <;> rfl
  | succ N ih =>
    have e : P (N + 1) = P N - X ^ (N + 1) * (C (⟨0, 1⟩ : GaussianInt) * P N) := by
      rw [P, prod_Icc_succ_top (by omega), ← P]; ring
    rw [e, map_sub, coeff_X_pow_mul', coeffP]
    split_ifs with h
    · rw [coeff_C_mul, ih, ih]
      ext <;> simp
    · rw [sub_zero, ih]

theorem a_eq (m : ℕ) : a m = (coeffP m m).1 := by
  rw [a, coeff_P]

theorem b_eq (m : ℕ) : b m = (coeffP m m).2 := by
  rw [b, coeff_P]

/-- The first 20 terms of A292042, as listed in the OEIS. -/
theorem a_data :
    (List.range 20).map a =
      [1, 0, 0, -1, -1, -2, -2, -3, -3, -4, -3, -4, -3, -3, -1, -1, 2, 3, 7, 9] := by
  rw [show a = fun m => (coeffP m m).1 from funext a_eq]
  decide

/-- The first 16 terms of A292043, as listed in the OEIS. -/
theorem b_data :
    (List.range 16).map b =
      [0, -1, -1, -1, -1, -1, 0, 0, 1, 2, 3, 4, 6, 7, 9, 10] := by
  rw [show b = fun m => (coeffP m m).2 from funext b_eq]
  decide

end OeisProofs.A292042
