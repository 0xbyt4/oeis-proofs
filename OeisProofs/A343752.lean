import Mathlib

/-!
# OEIS A343752

`a(1) = 1`; for `n > 1`, `a(n) = n` if `n` divides `a(n-1)`, otherwise
`a(n) = a(n-1) + n`.

Main result: for `n >= 1`, `a(n) = n` if and only if `n` is a triangular number.
See `proofs/A343752.md` for the informal proof.
-/

namespace OeisProofs.A343752

/-- The sequence A343752. The value at index `0` is a placeholder. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => if (n + 2) ∣ a (n + 1) then n + 2 else a (n + 1) + (n + 2)

/-- Triangular numbers, defined by recursion. -/
def T : ℕ → ℕ
  | 0 => 0
  | (k + 1) => T k + (k + 1)

theorem two_mul_T (k : ℕ) : 2 * T k = k * (k + 1) := by
  induction k with
  | zero => simp [T]
  | succ k ih => simp only [T]; rw [Nat.mul_add, ih]; ring

theorem T_eq (k : ℕ) : T k = k * (k + 1) / 2 := by
  have h := two_mul_T k
  generalize k * (k + 1) = m at h
  omega

theorem T_pos {k : ℕ} (hk : 1 ≤ k) : 1 ≤ T k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [T]; omega

theorem T_mono {i k : ℕ} (h : i ≤ k) : T i ≤ T k := by
  induction k with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · exact le_rfl
    · have := ih (by omega); simp only [T]; omega

/-- The defining recurrence, for all `n >= 1`. -/
theorem a_succ {n : ℕ} (hn : 1 ≤ n) :
    a (n + 1) = if (n + 1) ∣ a n then n + 1 else a n + (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

/-- Between two consecutive triangular numbers the sequence has a closed form. -/
theorem a_block {k : ℕ} (hk : 1 ≤ k) (h0 : a (T k) = T k) :
    ∀ j, j ≤ k → a (T k + j) = (j + 1) * T k + T j := by
  intro j
  induction j with
  | zero => intro _; simp [T, h0]
  | succ j ih =>
    intro hj
    have ihj := ih (by omega)
    have hTk := T_pos hk
    have hmono : T (j + 1) ≤ T k := T_mono hj
    have hTj1 : T (j + 1) = T j + (j + 1) := rfl
    have hTj1pos : 1 ≤ T (j + 1) := T_pos (by omega)
    -- key identity: a(T k + j) + T (j+1) = (j+1) * (T k + j + 1)
    have key : (j + 1) * T k + T j + T (j + 1) = (j + 1) * (T k + j + 1) := by
      have h2 := two_mul_T j
      rw [hTj1]
      nlinarith [h2]
    have hnd : ¬ (T k + j + 1) ∣ a (T k + j) := by
      intro hd
      rw [ihj] at hd
      have hd2 : (T k + j + 1) ∣ (j + 1) * T k + T j + T (j + 1) := by
        rw [key]; exact Dvd.intro_left _ rfl
      have hd3 : (T k + j + 1) ∣ T (j + 1) := (Nat.dvd_add_right hd).mp hd2
      have := Nat.le_of_dvd (by omega) hd3
      omega
    have hstep : a (T k + j + 1) = a (T k + j) + (T k + j + 1) := by
      rw [a_succ (by omega)]; simp [hnd]
    rw [← Nat.add_assoc, hstep, ihj, hTj1]
    ring

/-- The sequence returns to `n` at every triangular number. -/
theorem a_T {k : ℕ} (hk : 1 ≤ k) : a (T k) = T k := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have hblock := a_block hk ih k le_rfl
    have h2 := two_mul_T k
    have hT : T (k + 1) = T k + k + 1 := by simp only [T]; omega
    have hd : (T k + k + 1) ∣ a (T k + k) := by
      rw [hblock]
      refine ⟨k, ?_⟩
      nlinarith [h2]
    rw [hT, a_succ (by have := T_pos hk; omega)]; simp [hd]

/-- Every `n >= 1` lies in a unique block `T k <= n < T (k+1)`. -/
theorem exists_block {n : ℕ} (hn : 1 ≤ n) : ∃ k j, 1 ≤ k ∧ j ≤ k ∧ n = T k + j := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨1, 0, le_rfl, by omega, rfl⟩
  | succ n hn ih =>
    obtain ⟨k, j, hk, hj, rfl⟩ := ih
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · exact ⟨j + 1, 0, by omega, by omega, by simp only [T]; omega⟩
    · exact ⟨k, j + 1, hk, by omega, by omega⟩

/-- **Main theorem.** For `n >= 1`, `a n = n` iff `n` is triangular. -/
theorem a_eq_self_iff {n : ℕ} (hn : 1 ≤ n) : a n = n ↔ ∃ k, n = k * (k + 1) / 2 := by
  constructor
  · intro h
    obtain ⟨k, j, hk, hj, rfl⟩ := exists_block hn
    have hblock := a_block hk (a_T hk) j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact ⟨k, by rw [← T_eq]; rfl⟩
    · exfalso
      have hTk := T_pos hk
      have hTj := T_pos hjpos
      rw [hblock] at h
      nlinarith [h, hTk, hTj]
  · rintro ⟨k, rfl⟩
    rw [← T_eq] at hn ⊢
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp [T] at hn
      · exact h
    exact a_T hk

/-- The definition reproduces the first 16 terms listed in the OEIS (kernel-checked). -/
theorem a_data : (List.range 16).map (fun i => a (i + 1)) =
    [1, 3, 3, 7, 12, 6, 13, 21, 30, 10, 21, 33, 46, 60, 15, 31] := by decide

end OeisProofs.A343752
