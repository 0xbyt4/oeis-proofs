import Mathlib

/-!
# OEIS A352446 and A341309

Total number of parts in the partitions of `n` into an even (A352446) or odd (A341309)
number of consecutive parts.

A partition of `n` into `k` consecutive parts starting at `a` is a pair `(k, a)` with
`k ≥ 1`, `a ≥ 1` and `a + (a + 1) + ... + (a + k - 1) = n`. Such a pair always has
`k ≤ n` and `a ≤ n`, so `runs n` below enumerates all of them.

Main results:
* `oddTotal_eq`: the odd total is the sum of the odd divisors `d` of `n` with
  `d (d + 1) / 2 ≤ n`, which is the definition of A341309.
* `evenTotal_eq`: the even total is the coefficient of `x^n` in
  `sum_{h ≥ 1} 2 h x^(h (2 h + 1)) / (1 - x^(2 h))`.

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

end OeisProofs.A352446
