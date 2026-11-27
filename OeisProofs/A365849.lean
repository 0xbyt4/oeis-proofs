import Mathlib

/-!
# OEIS A365849

Triangular numbers that are the product of two distinct primes of the form `4k + 3`.

Main result: every such number other than `21` is congruent to `1` modulo `36`.
A triangular number `m (m + 1) / 2` equals `p * q` exactly when
`m * (m + 1) = 2 * (p * q)`, which is the form used here.
See `proofs/A365849.md` for the informal proof.
-/

namespace OeisProofs.A365849

/-- Arithmetic core: if `r` and `2 r + 1` are prime, `r ≡ 3 (mod 4)` and `r ≠ 3`,
then `r (2 r + 1) ≡ 1 (mod 36)`. -/
theorem core {r : ℕ} (hr : r.Prime) (hq : (2 * r + 1).Prime) (h4 : r % 4 = 3) (h3 : r ≠ 3) :
    r * (2 * r + 1) % 36 = 1 := by
  have hr3 : r % 3 = 2 := by
    have h0 : r % 3 ≠ 0 := by
      intro h
      have hd : 3 ∣ r := Nat.dvd_of_mod_eq_zero h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp hd
      omega
    have h1 : r % 3 ≠ 1 := by
      intro h
      have hd : 3 ∣ 2 * r + 1 := by omega
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp hd
      have := hr.two_le
      omega
    omega
  obtain ⟨s, rfl⟩ : ∃ s, r = 12 * s + 11 := ⟨r / 12, by omega⟩
  have h : (12 * s + 11) * (2 * (12 * s + 11) + 1) = 36 * (8 * s ^ 2 + 15 * s + 7) + 1 := by
    ring
  rw [h]
  omega

/-- `p * q` cannot divide `m` when `m (m + 1) = 2 p q` and `p q ≥ 9`. -/
theorem not_dvd_left {m N : ℕ} (hN : 9 ≤ N) (h : N ∣ m) (hT : m * (m + 1) = 2 * N) : False := by
  obtain ⟨t, rfl⟩ := h
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp at hT; omega
  · have h1 : N ≤ N * t := Nat.le_mul_of_pos_right N ht
    nlinarith [h1, hN, hT]

/-- `p * q` cannot divide `m + 1` when `m (m + 1) = 2 p q` and `p q ≥ 9`. -/
theorem not_dvd_right {m N : ℕ} (hN : 9 ≤ N) (h : N ∣ m + 1) (hT : m * (m + 1) = 2 * N) :
    False := by
  obtain ⟨t, ht⟩ := h
  rw [ht] at hT
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · omega
    · exact h
  have h1 : N ≤ N * t := Nat.le_mul_of_pos_right N ht0
  have h2 : m * t = 2 := by
    have : N * (m * t) = N * 2 := by nlinarith [hT]
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have h3 : m ≤ 2 := Nat.le_of_dvd (by omega) ⟨t, h2.symm⟩
  omega

/-- If `p ∣ m`, `q ∣ m + 1` and `p ≡ q ≡ 3 (mod 4)` then `q = 2 p + 1`. -/
theorem split {m p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hp4 : p % 4 = 3) (hq4 : q % 4 = 3)
    (h1 : p ∣ m) (h2 : q ∣ m + 1) (hT : m * (m + 1) = 2 * (p * q)) : q = 2 * p + 1 := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  have hst : s * t = 2 := by
    rw [ht, hs] at hT
    have hpq : 0 < p * q := Nat.mul_pos (by omega) (by omega)
    have : p * q * (s * t) = p * q * 2 := by nlinarith [hT]
    exact Nat.eq_of_mul_eq_mul_left hpq this
  have hs2 : s = 1 ∨ s = 2 := (Nat.dvd_prime Nat.prime_two).mp ⟨t, hst.symm⟩
  rcases hs2 with rfl | rfl
  · -- m = p and m + 1 = 2 q, impossible modulo 4
    have ht2 : t = 2 := by omega
    subst ht2
    omega
  · have ht1 : t = 1 := by omega
    subst ht1
    omega

/-- **Main theorem.** If the triangular number `m (m + 1) / 2` equals `p * q` for distinct
primes `p ≡ q ≡ 3 (mod 4)` and is not `21`, then it is congruent to `1` modulo `36`. -/
theorem modEq_one {m p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp4 : p % 4 = 3) (hq4 : q % 4 = 3) (hT : m * (m + 1) = 2 * (p * q)) (h21 : p * q ≠ 21) :
    p * q % 36 = 1 := by
  have hp3 : 3 ≤ p := by omega
  have hq3 : 3 ≤ q := by omega
  have hN : 9 ≤ p * q := by nlinarith
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hpd : p ∣ m * (m + 1) := ⟨2 * q, by rw [hT]; ring⟩
  have hqd : q ∣ m * (m + 1) := ⟨2 * p, by rw [hT]; ring⟩
  rcases (Nat.Prime.dvd_mul hp).mp hpd with hpm | hpm <;>
    rcases (Nat.Prime.dvd_mul hq).mp hqd with hqm | hqm
  · exact (not_dvd_left hN (hcop.mul_dvd_of_dvd_of_dvd hpm hqm) hT).elim
  · -- p ∣ m and q ∣ m + 1
    have hq' : q = 2 * p + 1 := split hp3 hq3 hp4 hq4 hpm hqm hT
    subst hq'
    exact core hp hq hp4 (by rintro rfl; exact h21 rfl)
  · -- q ∣ m and p ∣ m + 1
    have hp' : p = 2 * q + 1 := split hq3 hp3 hq4 hp4 hqm hpm (by rw [hT]; ring)
    subst hp'
    rw [Nat.mul_comm]
    exact core hq hp hq4 (by rintro rfl; exact h21 rfl)
  · exact (not_dvd_right hN (hcop.mul_dvd_of_dvd_of_dvd hpm hqm) hT).elim

end OeisProofs.A365849
