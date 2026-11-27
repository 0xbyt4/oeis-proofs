import Mathlib

/-!
# OEIS A352446, A341309, A204217 and A352269

Total number of parts in the partitions of `n` into an even (A352446) or odd (A341309)
number of consecutive parts, the total over all numbers of parts (A204217), and the
row sums of the triangle A352269.

A partition of `n` into `k` consecutive parts starting at `a` is a pair `(k, a)` with
`k ≥ 1`, `a ≥ 1` and `a + (a + 1) + ... + (a + k - 1) = n`. Such a pair always has
`k ≤ n` and `a ≤ n`, so `runs n` below enumerates all of them.

Main results:
* `oddTotal_eq`: the odd total is the sum of the odd divisors `d` of `n` with
  `d (d + 1) / 2 ≤ n`, which is the definition of A341309.
* `evenTotal_eq`: the even total is the coefficient of `x^n` in
  `sum_{h ≥ 1} 2 h x^(h (2 h + 1)) / (1 - x^(2 h))`.
* `oddTotal_eq_A003056`: Statement 2 in the OEIS wording, with `d ≤ A003056 n`.
* `allTotal_eq`, `allTotal_eq_evenTotal_add_oddTotal` and
  `evenTotal_eq_A204217_sub_A341309`: Statement 3, A352446 = A204217 - A341309.
* `sum_T_eq_A341309`: Statement 4, the row sums of A352269 give A341309.
* `coeff_evenGF_of_le`: Statement 1 as an identity of power series over `ℚ`, for the
  partial sums over `h ≤ N` with `N ≥ n`.

See `proofs/A352446.md` for the informal proof.
-/

namespace OeisProofs.A352446

open Finset

/-- Subtraction-free closed form for the sum of `k` consecutive integers starting at `a`. -/
theorem two_mul_sum_run (k a : ℕ) : 2 * ∑ i ∈ range k, (a + i) + k = k * (2 * a + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have h : (k + 1) * (2 * a + (k + 1)) = k * (2 * a + k) + 2 * a + 2 * k + 1 := by ring
    linarith

theorem sum_run_eq_iff (n k a : ℕ) :
    ∑ i ∈ range k, (a + i) = n ↔ 2 * n + k = k * (2 * a + k) := by
  have h := two_mul_sum_run k a
  constructor
  · intro h1; rw [← h1]; exact h
  · intro h1; omega

/-- The pairs `(k, a)`: `k` consecutive parts starting at `a`, with sum `n`. -/
def runs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 n) ×ˢ (Icc 1 n)).filter fun x => ∑ i ∈ range x.1, (x.2 + i) = n

theorem mem_runs {n k a : ℕ} :
    (k, a) ∈ runs n ↔ (1 ≤ k ∧ k ≤ n) ∧ (1 ≤ a ∧ a ≤ n) ∧ 2 * n + k = k * (2 * a + k) := by
  simp [runs, sum_run_eq_iff, and_assoc]

/-- Total number of parts over all partitions of `n` into an odd number of consecutive
parts. -/
def oddTotal (n : ℕ) : ℕ := ∑ x ∈ (runs n).filter (fun x => Odd x.1), x.1

/-- Total number of parts over all partitions of `n` into an even number of consecutive
parts (A352446). -/
def evenTotal (n : ℕ) : ℕ := ∑ x ∈ (runs n).filter (fun x => Even x.1), x.1

/-- **Statement 2.** The odd total equals the sum of the odd divisors `d` of `n` with
`d (d + 1) ≤ 2 n` (A341309). -/
theorem oddTotal_eq (n : ℕ) :
    oddTotal n = ∑ d ∈ n.divisors.filter (fun d => Odd d ∧ d * (d + 1) ≤ 2 * n), d := by
  unfold oddTotal
  refine sum_nbij' (fun x => x.1) (fun d => (d, n / d - d / 2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨k, a⟩ hx
    simp only [mem_filter, mem_runs] at hx
    obtain ⟨⟨⟨hk1, hkn⟩, ⟨ha1, han⟩, hE⟩, ⟨c, rfl⟩⟩ := hx
    have hn : n = (2 * c + 1) * (a + c) := by nlinarith [hE]
    simp only [mem_filter, Nat.mem_divisors]
    refine ⟨⟨⟨a + c, hn⟩, by omega⟩, ⟨c, rfl⟩, ?_⟩
    nlinarith [hn, ha1]
  · intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨⟨m, rfl⟩, hn0⟩, ⟨c, rfl⟩, hle⟩ := hd
    have hm : c + 1 ≤ m := by nlinarith [hle]
    have hdiv : (2 * c + 1) * m / (2 * c + 1) = m := Nat.mul_div_cancel_left m (by omega)
    have hhalf : (2 * c + 1) / 2 = c := by omega
    simp only [mem_filter, mem_runs, hdiv, hhalf]
    refine ⟨⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ?_⟩, ⟨c, rfl⟩⟩
    · nlinarith [hm]
    · have : m ≤ (2 * c + 1) * m := Nat.le_mul_of_pos_left m (by omega)
      omega
    · obtain ⟨u, rfl⟩ : ∃ u, m = c + 1 + u := ⟨m - (c + 1), by omega⟩
      have : c + 1 + u - c = u + 1 := by omega
      rw [this]; ring
  · rintro ⟨k, a⟩ hx
    simp only [mem_filter, mem_runs] at hx
    obtain ⟨⟨⟨hk1, hkn⟩, ⟨ha1, han⟩, hE⟩, ⟨c, rfl⟩⟩ := hx
    have hn : n = (2 * c + 1) * (a + c) := by nlinarith [hE]
    have hdiv : n / (2 * c + 1) = a + c := by
      rw [hn]; exact Nat.mul_div_cancel_left _ (by omega)
    have hhalf : (2 * c + 1) / 2 = c := by omega
    simp only [hdiv, hhalf, Prod.mk.injEq, true_and]
    omega
  · intro d _; rfl
  · intro x _; rfl

/-- **Statement 1.** The even total is the coefficient of `x^n` in
`sum_{h ≥ 1} 2 h x^(h (2 h + 1)) / (1 - x^(2 h))`: the `h`-th summand contributes `2 h`
exactly when `n - h (2 h + 1)` is a nonnegative multiple of `2 h`. -/
theorem evenTotal_eq (n : ℕ) :
    evenTotal n = ∑ h ∈ (Icc 1 n).filter
      (fun h => h * (2 * h + 1) ≤ n ∧ 2 * h ∣ n - h * (2 * h + 1)), 2 * h := by
  unfold evenTotal
  refine sum_nbij' (fun x => x.1 / 2)
    (fun h => (2 * h, (n - h * (2 * h + 1)) / (2 * h) + 1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨k, a⟩ hx
    simp only [mem_filter, mem_runs] at hx
    obtain ⟨⟨⟨hk1, hkn⟩, ⟨ha1, han⟩, hE⟩, ⟨h, rfl⟩⟩ := hx
    obtain ⟨t, rfl⟩ : ∃ t, a = t + 1 := ⟨a - 1, by omega⟩
    have hn : n = h * (2 * h + 1) + 2 * h * t := by nlinarith [hE]
    have hhalf : (h + h) / 2 = h := by omega
    simp only [mem_filter, mem_Icc, hhalf]
    refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
    exact ⟨t, by omega⟩
  · intro h hh
    simp only [mem_filter, mem_Icc] at hh
    obtain ⟨⟨hh1, hhn⟩, hle, ⟨t, ht⟩⟩ := hh
    have hn : n = h * (2 * h + 1) + 2 * h * t := by omega
    have hdiv : (n - h * (2 * h + 1)) / (2 * h) = t := by
      rw [ht]; exact Nat.mul_div_cancel_left t (by omega)
    simp only [mem_filter, mem_runs, hdiv]
    refine ⟨⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ?_⟩, ⟨h, by ring⟩⟩
    · nlinarith [hn, hh1]
    · nlinarith [hn, hh1]
    · rw [hn]; ring
  · rintro ⟨k, a⟩ hx
    simp only [mem_filter, mem_runs] at hx
    obtain ⟨⟨⟨hk1, hkn⟩, ⟨ha1, han⟩, hE⟩, ⟨h, rfl⟩⟩ := hx
    obtain ⟨t, rfl⟩ : ∃ t, a = t + 1 := ⟨a - 1, by omega⟩
    have hn : n = h * (2 * h + 1) + 2 * h * t := by nlinarith [hE]
    have hhalf : (h + h) / 2 = h := by omega
    have hdiv : (n - h * (2 * h + 1)) / (2 * h) = t := by
      have : n - h * (2 * h + 1) = 2 * h * t := by omega
      rw [this]; exact Nat.mul_div_cancel_left t (by omega)
    simp only [hhalf, hdiv, Prod.mk.injEq, and_true]
    omega
  · intro h hh
    simp only [mem_filter, mem_Icc] at hh
    show 2 * h / 2 = h
    omega
  · rintro ⟨k, a⟩ hx
    simp only [mem_filter, mem_runs] at hx
    obtain ⟨_, ⟨h, rfl⟩⟩ := hx
    show h + h = 2 * ((h + h) / 2)
    omega

/-- `evenTotal` reproduces the first 12 terms of A352446 listed in the OEIS
(kernel-checked). -/
theorem evenTotal_data : (List.range 12).map (fun i => evenTotal (i + 1)) =
    [0, 0, 2, 0, 2, 0, 2, 0, 2, 4, 2, 0] := by decide

/-- `oddTotal` reproduces the first 12 terms of A341309 listed in the OEIS
(kernel-checked). -/
theorem oddTotal_data : (List.range 12).map (fun i => oddTotal (i + 1)) =
    [1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4] := by decide


/-! ### Statement 3 -/

/-- Total number of parts over all partitions of `n` into consecutive parts. -/
def allTotal (n : ℕ) : ℕ := ∑ x ∈ runs n, x.1

theorem allTotal_eq_evenTotal_add_oddTotal (n : ℕ) :
    allTotal n = evenTotal n + oddTotal n := by
  unfold allTotal evenTotal oddTotal
  rw [← sum_filter_add_sum_filter_not (runs n) (fun x => Even x.1)]
  simp only [Nat.not_even_iff_odd]

theorem two_mul_triangle (k : ℕ) : 2 * (k * (k + 1) / 2) = k * (k + 1) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self k)

/-- The total over all `k` is the coefficient of `x^n` in
`sum_{k ≥ 1} k x^(k (k + 1) / 2) / (1 - x^k)`: the `k`-th summand contributes `k`
exactly when `n - k (k + 1) / 2` is a nonnegative multiple of `k`. -/
theorem allTotal_eq (n : ℕ) :
    allTotal n = ∑ k ∈ (Icc 1 n).filter
      (fun k => k * (k + 1) / 2 ≤ n ∧ k ∣ n - k * (k + 1) / 2), k := by
  unfold allTotal
  refine sum_nbij' (fun x => x.1) (fun k => (k, (n - k * (k + 1) / 2) / k + 1))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨k, a⟩ hx
    simp only [mem_runs] at hx
    obtain ⟨⟨hk1, hkn⟩, ⟨ha1, han⟩, hE⟩ := hx
    obtain ⟨t, rfl⟩ : ∃ t, a = t + 1 := ⟨a - 1, by omega⟩
    have hT := two_mul_triangle k
    generalize k * (k + 1) / 2 = T at hT ⊢
    have hn : n = T + k * t := by nlinarith [hE]
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨hk1, hkn⟩, by omega, ⟨t, by omega⟩⟩
  · intro k hk
    simp only [mem_filter, mem_Icc] at hk
    obtain ⟨⟨hk1, hkn⟩, hle, ⟨t, ht⟩⟩ := hk
    have hdiv : (n - k * (k + 1) / 2) / k = t := by
      rw [ht]; exact Nat.mul_div_cancel_left t (by omega)
    have hT := two_mul_triangle k
    generalize k * (k + 1) / 2 = T at hT hle ht hdiv
    have hn : n = T + k * t := by omega
    simp only [mem_runs, hdiv]
    refine ⟨⟨hk1, hkn⟩, ⟨by omega, ?_⟩, ?_⟩
    · nlinarith [hn, hT, hk1]
    · nlinarith [hn, hT]
  · rintro ⟨k, a⟩ hx
    simp only [mem_runs] at hx
    obtain ⟨⟨hk1, hkn⟩, ⟨ha1, han⟩, hE⟩ := hx
    obtain ⟨t, rfl⟩ : ∃ t, a = t + 1 := ⟨a - 1, by omega⟩
    have hT := two_mul_triangle k
    generalize k * (k + 1) / 2 = T at hT ⊢
    have hn : n = T + k * t := by nlinarith [hE]
    have hdiv : (n - T) / k = t := by
      have : n - T = k * t := by omega
      rw [this]; exact Nat.mul_div_cancel_left t (by omega)
    simp only [hdiv]
  · intro k _; rfl
  · intro x _; rfl

/-! ### The A003056 link -/

/-- A003056: the largest `k` with `k (k + 1) / 2 ≤ n` (OEIS formula). -/
def A003056 (n : ℕ) : ℕ := (Nat.sqrt (8 * n + 1) - 1) / 2

theorem two_mul_add_one_le_sqrt_iff (n d : ℕ) :
    2 * d + 1 ≤ Nat.sqrt (8 * n + 1) ↔ d * (d + 1) ≤ 2 * n := by
  rw [Nat.le_sqrt]
  constructor <;> intro h <;> nlinarith

theorem le_A003056_iff (n d : ℕ) : d * (d + 1) ≤ 2 * n ↔ d ≤ A003056 n := by
  unfold A003056
  have hs : 1 ≤ Nat.sqrt (8 * n + 1) := Nat.le_sqrt.mpr (by omega)
  rw [← two_mul_add_one_le_sqrt_iff]
  omega

/-- **Statement 2, OEIS wording.** The odd total is the sum of the odd divisors `d` of
`n` with `d ≤ A003056 n`. -/
theorem oddTotal_eq_A003056 (n : ℕ) :
    oddTotal n = ∑ d ∈ n.divisors.filter (fun d => Odd d ∧ d ≤ A003056 n), d := by
  rw [oddTotal_eq]
  congr 1
  exact filter_congr fun d _ => by rw [le_A003056_iff]

/-- A341309 as defined in the OEIS: the sum of the odd divisors of `n` that are at most
`A003056 n`. -/
def A341309 (n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter (fun d => Odd d ∧ d ≤ A003056 n), d

/-- A204217 as defined in the OEIS: the coefficient of `x^n` in
`sum_{k ≥ 1} k x^(k (k + 1) / 2) / (1 - x^k)`. -/
def A204217 (n : ℕ) : ℕ :=
  ∑ k ∈ (Icc 1 n).filter (fun k => k * (k + 1) / 2 ≤ n ∧ k ∣ n - k * (k + 1) / 2), k

theorem oddTotal_eq_A341309 (n : ℕ) : oddTotal n = A341309 n := oddTotal_eq_A003056 n

theorem allTotal_eq_A204217 (n : ℕ) : allTotal n = A204217 n := allTotal_eq n

/-- **Statement 3.** A204217(n) = A352446(n) + A341309(n). -/
theorem A204217_eq_evenTotal_add_A341309 (n : ℕ) :
    A204217 n = evenTotal n + A341309 n := by
  rw [← allTotal_eq_A204217, ← oddTotal_eq_A341309, allTotal_eq_evenTotal_add_oddTotal]

/-- **Statement 3, OEIS form.** A352446(n) = A204217(n) - A341309(n). -/
theorem evenTotal_eq_A204217_sub_A341309 (n : ℕ) :
    evenTotal n = A204217 n - A341309 n := by
  rw [A204217_eq_evenTotal_add_A341309]; omega

/-! ### Statement 4 -/

/-- `n` has a partition into `k` consecutive parts. -/
def HasRun (n k : ℕ) : Prop := ∃ a, 1 ≤ a ∧ ∑ i ∈ range k, (a + i) = n

theorem hasRun_odd_iff {n k : ℕ} (hk : Odd k) :
    HasRun n k ↔ k ∣ n ∧ k * (k + 1) ≤ 2 * n := by
  obtain ⟨c, rfl⟩ := hk
  constructor
  · rintro ⟨a, ha, hs⟩
    rw [sum_run_eq_iff] at hs
    have hn : n = (2 * c + 1) * (a + c) := by nlinarith [hs]
    exact ⟨⟨a + c, hn⟩, by nlinarith [hn, ha]⟩
  · rintro ⟨⟨m, rfl⟩, hle⟩
    have hm : c + 1 ≤ m := by nlinarith [hle]
    refine ⟨m - c, by omega, ?_⟩
    rw [sum_run_eq_iff]
    obtain ⟨u, rfl⟩ : ∃ u, m = c + 1 + u := ⟨m - (c + 1), by omega⟩
    have : c + 1 + u - c = u + 1 := by omega
    rw [this]; ring

open Classical in
/-- The triangle A352269: `T n k = 2 k - 1` if `n` has a partition into `2 k - 1`
consecutive parts, and `0` otherwise. -/
noncomputable def T (n k : ℕ) : ℕ := if HasRun n (2 * k - 1) then 2 * k - 1 else 0

/-- The length of row `n` of A352269: `floor((sqrt(8 n + 1) + 1) / 4)`. -/
def rowLength (n : ℕ) : ℕ := (Nat.sqrt (8 * n + 1) + 1) / 4

/-- **Statement 4.** The row sums of A352269 give A341309. -/
theorem sum_T_eq_A341309 (n : ℕ) : ∑ k ∈ Icc 1 (rowLength n), T n k = A341309 n := by
  classical
  rw [← oddTotal_eq_A341309, oddTotal_eq]
  unfold T
  rw [← sum_filter]
  refine sum_nbij' (fun k => 2 * k - 1) (fun d => (d + 1) / 2) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_filter, mem_Icc] at hk
    obtain ⟨⟨hk1, _⟩, hr⟩ := hk
    have hodd : Odd (2 * k - 1) := ⟨k - 1, by omega⟩
    obtain ⟨hdvd, hle⟩ := (hasRun_odd_iff hodd).1 hr
    have hpos := Nat.mul_le_mul (show 1 ≤ 2 * k - 1 by omega)
      (show 1 ≤ 2 * k - 1 + 1 by omega)
    simp only [mem_filter, Nat.mem_divisors]
    exact ⟨⟨hdvd, by omega⟩, hodd, hle⟩
  · intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, ⟨c, rfl⟩, hle⟩ := hd
    have hs := (two_mul_add_one_le_sqrt_iff n _).2 hle
    have he : 2 * ((2 * c + 1 + 1) / 2) - 1 = 2 * c + 1 := by omega
    simp only [mem_filter, mem_Icc, he, rowLength]
    exact ⟨⟨by omega, by omega⟩, (hasRun_odd_iff ⟨c, rfl⟩).2 ⟨hdvd, hle⟩⟩
  · intro k hk
    simp only [mem_filter, mem_Icc] at hk
    omega
  · intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    obtain ⟨_, ⟨c, rfl⟩, _⟩ := hd
    omega
  · intro k _; rfl

/-! ### Statement 1 as a power series identity -/

open PowerSeries

/-- The geometric series `1 / (1 - x^m)`. -/
theorem inv_one_sub_X_pow {m : ℕ} (hm : 1 ≤ m) :
    (1 - X ^ m : ℚ⟦X⟧)⁻¹ = mk fun n => if m ∣ n then 1 else 0 := by
  rw [eq_comm, PowerSeries.eq_inv_iff_mul_eq_one (by
    rw [map_sub, map_one, map_pow, constantCoeff_X, zero_pow (by omega), sub_zero]
    exact one_ne_zero)]
  ext n
  rw [mul_sub, mul_one, map_sub, mul_comm, coeff_X_pow_mul', coeff_mk, coeff_mk, coeff_one]
  have h1 : m ∣ n → m ≤ n → m ∣ n - m := fun h hmn => Nat.dvd_sub h (dvd_refl m)
  have h2 : m ∣ n - m → m ≤ n → m ∣ n := fun h hmn => by
    have := Nat.dvd_add h (dvd_refl m)
    rwa [Nat.sub_add_cancel hmn] at this
  have h3 : m ∣ n → n ≠ 0 → m ≤ n := fun h hn => Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h
  by_cases hA : m ∣ n <;> by_cases hB : m ≤ n <;> by_cases hD : n = 0 <;>
    simp_all

/-- Partial sum over `h ≤ N` of `sum_{h ≥ 1} 2 h x^(h (2 h + 1)) / (1 - x^(2 h))`. -/
noncomputable def evenGF (N : ℕ) : ℚ⟦X⟧ :=
  ∑ h ∈ Icc 1 N, C (2 * h : ℚ) * X ^ (h * (2 * h + 1)) * (1 - X ^ (2 * h))⁻¹

theorem coeff_evenGF (n N : ℕ) :
    coeff n (evenGF N) = ∑ h ∈ (Icc 1 N).filter
      (fun h => h * (2 * h + 1) ≤ n ∧ 2 * h ∣ n - h * (2 * h + 1)), (2 * h : ℚ) := by
  unfold evenGF
  rw [map_sum, sum_filter]
  refine sum_congr rfl fun h hh => ?_
  rw [mem_Icc] at hh
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', inv_one_sub_X_pow (by omega)]
  by_cases h1 : h * (2 * h + 1) ≤ n
  · by_cases h2 : 2 * h ∣ n - h * (2 * h + 1) <;> simp [h1, h2]
  · simp [h1]

/-- **Statement 1, power series form.** For `N ≥ n`, the coefficient of `x^n` in the
partial sum over `h ≤ N` of `sum_{h ≥ 1} 2 h x^(h (2 h + 1)) / (1 - x^(2 h))` is
A352446(n). Summands with `h > n` do not contribute to the coefficient of `x^n`. -/
theorem coeff_evenGF_of_le {n N : ℕ} (hN : n ≤ N) :
    coeff n (evenGF N) = evenTotal n := by
  rw [coeff_evenGF, evenTotal_eq, Nat.cast_sum]
  push_cast
  congr 1
  ext h
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, hle, hd⟩
    exact ⟨⟨h1, by nlinarith⟩, hle, hd⟩
  · rintro ⟨⟨h1, hn⟩, hle, hd⟩
    exact ⟨⟨h1, by omega⟩, hle, hd⟩

theorem coeff_evenGF_self (n : ℕ) : coeff n (evenGF n) = evenTotal n :=
  coeff_evenGF_of_le le_rfl

/-- Longer partial sums give the same coefficient of `x^n`. -/
theorem coeff_evenGF_mono {n N M : ℕ} (hN : n ≤ N) (hM : N ≤ M) :
    coeff n (evenGF M) = coeff n (evenGF N) := by
  rw [coeff_evenGF_of_le hN, coeff_evenGF_of_le (hN.trans hM)]

end OeisProofs.A352446
