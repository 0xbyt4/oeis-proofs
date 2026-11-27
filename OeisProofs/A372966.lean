import Mathlib

/-!
# OEIS A372966

`a(n) = sigma_8(n^2) / sigma_4(n^2)`.

Main result: for every `n ≥ 1` the quotient is an integer congruent to `1` modulo `240`.
See `proofs/A372966.md` for the informal proof.
-/

namespace OeisProofs.A372966

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Lemma 1 of the informal proof: `240 ∣ x^4 (x^4 - 1)` for every integer `x`. -/
theorem key (x : ℤ) : (240 : ℤ) ∣ x ^ 4 * (x ^ 4 - 1) := by
  have h16 : (16 : ℤ) ∣ x ^ 4 * (x ^ 4 - 1) := by
    have h : ∀ y : ZMod 16, y ^ 4 * (y ^ 4 - 1) = 0 := by decide
    have hx := h (x : ZMod 16)
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mp (by push_cast; exact hx)
  have h3 : (3 : ℤ) ∣ x ^ 4 * (x ^ 4 - 1) := by
    have h : ∀ y : ZMod 3, y ^ 4 * (y ^ 4 - 1) = 0 := by decide
    have hx := h (x : ZMod 3)
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast; exact hx)
  have h5 : (5 : ℤ) ∣ x ^ 4 * (x ^ 4 - 1) := by
    have h : ∀ y : ZMod 5, y ^ 4 * (y ^ 4 - 1) = 0 := by decide
    have hx := h (x : ZMod 5)
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp (by push_cast; exact hx)
  omega

/-- The alternating geometric sum with an odd number of terms is `≡ 1 (mod 240)`
whenever `240 ∣ Y (Y - 1)`. -/
theorem alt_sum_modEq (Y : ℤ) (hY : (240 : ℤ) ∣ Y * (Y - 1)) (e : ℕ) :
    ∑ j ∈ Finset.range (2 * e + 1), (-Y) ^ j ≡ 1 [ZMOD 240] := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hidx : 2 * (e + 1) + 1 = (2 * e + 1) + 1 + 1 := by ring
    rw [hidx, Finset.sum_range_succ, Finset.sum_range_succ]
    have hodd : (-Y) ^ (2 * e + 1) = -(Y ^ (2 * e + 1)) := Odd.neg_pow ⟨e, rfl⟩ Y
    have heven : (-Y) ^ (2 * e + 1 + 1) = Y ^ (2 * e + 1 + 1) := Even.neg_pow ⟨e + 1, by ring⟩ Y
    have hsum : (-Y) ^ (2 * e + 1) + (-Y) ^ (2 * e + 1 + 1) = Y ^ (2 * e) * (Y * (Y - 1)) := by
      rw [hodd, heven]; ring
    have hd : (240 : ℤ) ∣ Y ^ (2 * e) * (Y * (Y - 1)) := Dvd.dvd.mul_left hY _
    rw [add_assoc, hsum]
    have := Int.ModEq.add ih (Int.modEq_zero_iff_dvd.mpr hd)
    simpa using this

/-- Lemma 2 of the informal proof, as an identity of integer geometric sums. -/
theorem factor (Y : ℤ) (hY : 2 ≤ Y) (e : ℕ) :
    ∑ j ∈ Finset.range (2 * e + 1), (Y ^ 2) ^ j
      = (∑ j ∈ Finset.range (2 * e + 1), Y ^ j) * ∑ j ∈ Finset.range (2 * e + 1), (-Y) ^ j := by
  have h1 := geom_sum_mul (Y ^ 2) (2 * e + 1)
  have h2 := geom_sum_mul Y (2 * e + 1)
  have h3 := geom_sum_mul (-Y) (2 * e + 1)
  have hodd : (-Y) ^ (2 * e + 1) = -(Y ^ (2 * e + 1)) := Odd.neg_pow ⟨e, rfl⟩ Y
  rw [hodd] at h3
  have hne : Y ^ 2 - 1 ≠ 0 := by nlinarith
  apply mul_right_cancel₀ hne
  rw [h1]
  have hre : (∑ j ∈ Finset.range (2 * e + 1), Y ^ j)
        * (∑ j ∈ Finset.range (2 * e + 1), (-Y) ^ j) * (Y ^ 2 - 1)
      = -(((∑ j ∈ Finset.range (2 * e + 1), Y ^ j) * (Y - 1))
        * ((∑ j ∈ Finset.range (2 * e + 1), (-Y) ^ j) * (-Y - 1))) := by ring
  rw [hre, h2, h3]
  ring

/-- The statement in a form suited to multiplicative induction. -/
def P (n : ℕ) : Prop :=
  ∃ b : ℤ, (σ 8 (n ^ 2) : ℤ) = (σ 4 (n ^ 2) : ℤ) * b ∧ b ≡ 1 [ZMOD 240]

theorem P_prime_pow (p e : ℕ) (hp : p.Prime) : P (p ^ e) := by
  have hY : (2 : ℤ) ≤ (p : ℤ) ^ 4 := by
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    nlinarith [pow_pos (by linarith : (0 : ℤ) < p) 2, pow_pos (by linarith : (0 : ℤ) < p) 3]
  refine ⟨∑ j ∈ Finset.range (2 * e + 1), (-((p : ℤ) ^ 4)) ^ j, ?_,
    alt_sum_modEq _ (key p) e⟩
  have hpow : (p ^ e) ^ 2 = p ^ (2 * e) := by rw [← pow_mul, mul_comm]
  rw [hpow, sigma_apply_prime_pow hp, sigma_apply_prime_pow hp]
  push_cast
  have e8 : ∀ j ∈ Finset.range (2 * e + 1), (p : ℤ) ^ (j * 8) = (((p : ℤ) ^ 4) ^ 2) ^ j := by
    intro j _; ring
  have e4 : ∀ j ∈ Finset.range (2 * e + 1), (p : ℤ) ^ (j * 4) = ((p : ℤ) ^ 4) ^ j := by
    intro j _; ring
  rw [Finset.sum_congr rfl e8, Finset.sum_congr rfl e4]
  exact factor _ hY e

theorem P_all (n : ℕ) : P n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp _ => exact P_prime_pow p e hp
  | zero => exact ⟨1, by simp, Int.ModEq.refl 1⟩
  | one => exact ⟨1, by simp, Int.ModEq.refl 1⟩
  | coprime a b _ _ hab ha hb =>
    obtain ⟨u, hu, hu1⟩ := ha
    obtain ⟨v, hv, hv1⟩ := hb
    have hcop : Nat.Coprime (a ^ 2) (b ^ 2) := Nat.Coprime.pow 2 2 hab
    refine ⟨u * v, ?_, by simpa using Int.ModEq.mul hu1 hv1⟩
    rw [mul_pow, isMultiplicative_sigma.map_mul_of_coprime hcop,
      isMultiplicative_sigma.map_mul_of_coprime hcop]
    push_cast
    rw [hu, hv]
    ring

/-- **Main theorem.** For `n ≥ 1`, `sigma_4(n^2)` divides `sigma_8(n^2)` and the quotient
is congruent to `1` modulo `240`. -/
theorem quotient_mod (n : ℕ) (hn : n ≠ 0) :
    σ 4 (n ^ 2) ∣ σ 8 (n ^ 2) ∧ σ 8 (n ^ 2) / σ 4 (n ^ 2) % 240 = 1 := by
  obtain ⟨b, hb, hb1⟩ := P_all n
  have h4 : 0 < σ 4 (n ^ 2) := sigma_pos 4 _ (pow_ne_zero 2 hn)
  have h8 : 0 < σ 8 (n ^ 2) := sigma_pos 8 _ (pow_ne_zero 2 hn)
  have hbpos : 0 < b := by
    have h4' : (0 : ℤ) < (σ 4 (n ^ 2) : ℤ) := by exact_mod_cast h4
    have h8' : (0 : ℤ) < (σ 8 (n ^ 2) : ℤ) := by exact_mod_cast h8
    rw [hb] at h8'
    by_contra hneg
    have := mul_nonpos_of_nonneg_of_nonpos h4'.le (not_lt.mp hneg)
    linarith
  obtain ⟨c, rfl⟩ : ∃ c : ℕ, b = c := ⟨b.toNat, by omega⟩
  have hc : σ 8 (n ^ 2) = σ 4 (n ^ 2) * c := by exact_mod_cast hb
  refine ⟨⟨c, hc⟩, ?_⟩
  rw [hc, Nat.mul_div_cancel_left c h4]
  have := hb1
  unfold Int.ModEq at this
  omega

/-- The term `a(2) = 241`. Together with `quotient_mod` it shows that `240` is the largest
modulus `M` with `a(n) ≡ 1 (mod M)` for all `n`, because `a(2) - 1 = 240`. -/
theorem quotient_two : σ 8 (2 ^ 2) / σ 4 (2 ^ 2) = 241 := by decide

end OeisProofs.A372966
