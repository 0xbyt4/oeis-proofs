import Mathlib

/-!
# OEIS A306598

`a(n)` is the determinant of the circulant matrix whose first column is the list of
divisors of `n` in increasing order.

Main results:

* `det_circulant_pos_of_odd`, `det_circulant_neg_of_even`: for a strictly increasing
  positive real vector `c : Fin t -> Real`, the determinant of `Matrix.circulant c` is
  positive if `t` is odd and negative if `t` is even and nonzero.
* `a_pos_iff`: `0 < a n` if and only if `n` is a square.
* `a_neg_of_not_isSquare`: `a n < 0` if `n` is not a square.

See `proofs/A306598.md` for the informal proof. The formal proof follows its steps 1 and 2
(eigenvalues of a circulant matrix, no zero of the generating polynomial on the unit
circle) and replaces step 3 (pairing of conjugate eigenvalues) by a continuity argument:
the segment from `c` to the last standard basis vector consists of vectors with nonzero
circulant determinant, and at the end point the circulant matrix is the permutation
matrix of a cyclic shift.
-/

namespace OeisProofs.A306598

open Matrix Finset

/-! ## No zero on the unit circle -/

/-- Summation by parts for `(1 - z) * f(z)`. -/
theorem one_sub_mul_sum (c : ℕ → ℝ) (z : ℂ) (k : ℕ) :
    (1 - z) * ∑ m ∈ range (k + 1), (c m : ℂ) * z ^ m =
      c 0 + ∑ m ∈ range k, ((c (m + 1) - c m : ℝ) : ℂ) * z ^ (m + 1) - c k * z ^ (k + 1) := by
  induction k with
  | zero => simp; ring
  | succ k ih =>
    rw [sum_range_succ, mul_add, ih, sum_range_succ]
    push_cast
    ring

/-- A complex number of norm one and real part one is one. -/
theorem eq_one_of_norm_eq_one_of_re_eq_one {w : ℂ} (hw : ‖w‖ = 1) (hre : w.re = 1) : w = 1 := by
  have h := Complex.sq_norm w
  rw [hw, Complex.normSq_apply, hre] at h
  have him : w.im = 0 := by nlinarith
  exact Complex.ext hre him

/-- Strict Enestrom-Kakeya on the unit circle: a polynomial with strictly increasing positive
coefficients has no zero of absolute value one. -/
theorem sum_mul_pow_ne_zero (c : ℕ → ℝ) (k : ℕ) (h0 : 0 < c 0)
    (hc : ∀ m, m < k → c m < c (m + 1)) (z : ℂ) (hz : ‖z‖ = 1) :
    ∑ m ∈ range (k + 1), (c m : ℂ) * z ^ m ≠ 0 := by
  intro hS
  have hpos : ∀ m, m ≤ k → 0 < c m := by
    intro m
    induction m with
    | zero => exact fun _ => h0
    | succ m ih => exact fun hm => (ih (by omega)).trans (hc m (by omega))
  -- the case `z = 1`
  by_cases hz1 : z = 1
  · subst hz1
    have h1 : (0 : ℝ) < ∑ m ∈ range (k + 1), c m :=
      sum_pos (fun m hm => hpos m (by have := mem_range.mp hm; omega)) (by simp)
    have h2 : ((∑ m ∈ range (k + 1), c m : ℝ) : ℂ) = 0 := by
      rw [← hS]; push_cast; simp
    exact h1.ne' (by exact_mod_cast h2)
  -- the case `k = 0`
  obtain _ | k := k
  · simp at hS
    exact h0.ne' hS
  -- the main case
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  set w : ℂ := z⁻¹ with hw
  have hzw : z * w = 1 := mul_inv_cancel₀ hz0
  have hwn : ‖w‖ = 1 := by rw [hw, norm_inv, hz, inv_one]
  have habel := one_sub_mul_sum c z (k + 1)
  rw [hS, mul_zero] at habel
  -- multiply by `w ^ (k + 2)` and take real parts
  have hmul : (c (k + 1) : ℂ) = c 0 * w ^ (k + 2) +
      ∑ m ∈ range (k + 1), ((c (m + 1) - c m : ℝ) : ℂ) * (z ^ (m + 1) * w ^ (k + 2)) := by
    have h3 : (c (k + 1) : ℂ) * z ^ (k + 2) * w ^ (k + 2) = c (k + 1) := by
      rw [mul_assoc, ← mul_pow, hzw, one_pow, mul_one]
    have h4 : (c (k + 1) : ℂ) * z ^ (k + 2) =
        c 0 + ∑ m ∈ range (k + 1), ((c (m + 1) - c m : ℝ) : ℂ) * z ^ (m + 1) := by
      linear_combination habel
    rw [← h3, h4, add_mul, sum_mul]
    congr 1
    exact sum_congr rfl fun m _ => by ring
  have hre := congrArg Complex.re hmul
  rw [Complex.ofReal_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_sum] at hre
  simp only [Complex.re_ofReal_mul] at hre
  have htel : c (k + 1) = c 0 + ∑ m ∈ range (k + 1), (c (m + 1) - c m) := by
    rw [sum_range_sub]; ring
  have hle : ∀ u : ℂ, ‖u‖ = 1 → u.re ≤ 1 := fun u hu => hu ▸ Complex.re_le_norm u
  have hu : ∀ m, ‖z ^ (m + 1) * w ^ (k + 2)‖ = 1 := fun m => by
    rw [norm_mul, norm_pow, norm_pow, hz, hwn, one_pow, one_pow, mul_one]
  have hsum :
      ∑ m ∈ range (k + 1), (c (m + 1) - c m) * (1 - (z ^ (m + 1) * w ^ (k + 2)).re) ≤ 0 := by
    have h5 : 0 ≤ c 0 * (1 - (w ^ (k + 2)).re) :=
      mul_nonneg h0.le (sub_nonneg.mpr (hle _ (by rw [norm_pow, hwn, one_pow])))
    have h6 : ∑ m ∈ range (k + 1), (c (m + 1) - c m) * (1 - (z ^ (m + 1) * w ^ (k + 2)).re) =
        ∑ m ∈ range (k + 1), (c (m + 1) - c m) -
          ∑ m ∈ range (k + 1), (c (m + 1) - c m) * (z ^ (m + 1) * w ^ (k + 2)).re := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun m _ => by ring
    rw [h6]
    linarith
  have hnonneg : ∀ m ∈ range (k + 1),
      0 ≤ (c (m + 1) - c m) * (1 - (z ^ (m + 1) * w ^ (k + 2)).re) := fun m hm =>
    mul_nonneg (sub_nonneg.mpr (hc m (mem_range.mp hm)).le) (sub_nonneg.mpr (hle _ (hu m)))
  have hzero := (sum_eq_zero_iff_of_nonneg hnonneg).mp (le_antisymm hsum (sum_nonneg hnonneg))
    k (mem_range.mpr (Nat.lt_succ_self k))
  have hwk : z ^ (k + 1) * w ^ (k + 2) = w := by
    rw [pow_succ w (k + 1), ← mul_assoc, ← mul_pow, hzw, one_pow, one_mul]
  rw [hwk] at hzero
  have hre1 : w.re = 1 := by
    rcases mul_eq_zero.mp hzero with h | h
    · linarith [hc k (Nat.lt_succ_self k)]
    · linarith
  have hw1 : w = 1 := eq_one_of_norm_eq_one_of_re_eq_one hwn hre1
  rw [hw1, mul_one] at hzw
  exact hz1 hzw

/-! ## Eigenvalues of a circulant matrix -/

/-- The determinant of a complex circulant matrix of size `k + 1` is the product of the values
of `f(x) = sum_m c_m x^m` at the `(k + 1)`-th roots of unity. -/
theorem det_circulant_eq_prod {k : ℕ} (c : Fin (k + 1) → ℂ) {zeta : ℂ}
    (hzeta : IsPrimitiveRoot zeta (k + 1)) :
    (circulant c).det =
      ∏ j : Fin (k + 1), ∑ m : Fin (k + 1), c m * (zeta ^ (j : ℕ)) ^ (m : ℕ) := by
  set W : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := vandermonde (fun j => zeta ^ (j : ℕ)) with hW
  have hWdet : W.det ≠ 0 :=
    det_vandermonde_ne_zero_iff.mpr fun i j h => Fin.ext (hzeta.pow_inj i.2 j.2 h)
  have key : W * circulant c =
      diagonal (fun j : Fin (k + 1) =>
        ∑ m : Fin (k + 1), c m * (zeta ^ (j : ℕ)) ^ (m : ℕ)) * W := by
    ext j i
    rw [Matrix.mul_apply, diagonal_mul]
    simp only [hW, vandermonde_apply, circulant_apply]
    rw [sum_mul, ← Equiv.sum_comp (Equiv.addRight i)]
    refine sum_congr rfl fun m _ => ?_
    have h1 : (zeta ^ (j : ℕ)) ^ (k + 1) = 1 := by
      rw [pow_right_comm, hzeta.pow_eq_one, one_pow]
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [Fin.val_add, ← pow_eq_pow_mod _ h1, pow_add]
    ring
  have hdet := congrArg det key
  rw [det_mul, det_mul, det_diagonal, mul_comm] at hdet
  exact mul_right_cancel₀ hWdet hdet

/-- A real circulant matrix with strictly increasing positive first column is invertible. -/
theorem det_circulant_ne_zero {k : ℕ} (c : Fin (k + 1) → ℝ) (hc : StrictMono c)
    (h0 : 0 < c 0) : (circulant c).det ≠ 0 := by
  intro h
  have h2 : (circulant fun i => (c i : ℂ)).det = 0 := by
    have h3 : (circulant fun i => (c i : ℂ)) = Complex.ofRealHom.mapMatrix (circulant c) := by
      ext i j
      simp
    rw [h3, ← RingHom.map_det, h, map_zero]
  rw [det_circulant_eq_prod _ (Complex.isPrimitiveRoot_exp (k + 1) (Nat.succ_ne_zero k))] at h2
  obtain ⟨j, -, hj⟩ := prod_eq_zero_iff.mp h2
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I / (k + 1 : ℕ)) ^ (j : ℕ) with hz
  have hzn : ‖z‖ = 1 := by
    have h4 : z ^ (k + 1) = 1 := by
      rw [hz, pow_right_comm,
        (Complex.isPrimitiveRoot_exp (k + 1) (Nat.succ_ne_zero k)).pow_eq_one, one_pow]
    exact Complex.norm_eq_one_of_pow_eq_one h4 (Nat.succ_ne_zero k)
  let c' : ℕ → ℝ := fun m => if h : m < k + 1 then c ⟨m, h⟩ else 0
  have hc'0 : 0 < c' 0 := by simpa [c'] using h0
  have hc' : ∀ m, m < k → c' m < c' (m + 1) := by
    intro m hm
    have h5 : m < k + 1 := by omega
    have h6 : m + 1 < k + 1 := by omega
    simp only [c', h5, h6, ↓reduceDIte]
    exact hc (Fin.mk_lt_mk.mpr (Nat.lt_succ_self m))
  refine sum_mul_pow_ne_zero c' k hc'0 hc' z hzn ?_
  rw [← Fin.sum_univ_eq_sum_range (fun m => (c' m : ℂ) * z ^ m) (k + 1), ← hj]
  refine sum_congr rfl fun m _ => ?_
  simp only [c', m.2, ↓reduceDIte]

/-! ## The sign of the determinant -/

/-- The circulant matrix of the last standard basis vector is the permutation matrix of the
cyclic shift, of determinant `(-1) ^ k`. -/
theorem det_circulant_single_last (k : ℕ) :
    (circulant (Pi.single (Fin.last k) (1 : ℝ))).det = (-1) ^ k := by
  have h : circulant (Pi.single (Fin.last k) (1 : ℝ)) = (finRotate (k + 1)).permMatrix ℝ := by
    ext i j
    have h1 : i - j = Fin.last k ↔ i + 1 = j := by
      constructor
      · intro h; rw [← Fin.neg_last, ← h]; abel
      · intro h; rw [← h, ← Fin.neg_last]; abel
    simp [Equiv.Perm.permMatrix, Pi.single_apply, h1]
  rw [h, det_permutation, sign_finRotate]
  simp

/-- Theorem 1 in sign-uniform form. -/
theorem neg_one_pow_mul_det_circulant_pos {k : ℕ} (c : Fin (k + 1) → ℝ) (hc : StrictMono c)
    (h0 : 0 < c 0) : 0 < (-1 : ℝ) ^ k * (circulant c).det := by
  set e : Fin (k + 1) → ℝ := Pi.single (Fin.last k) 1 with he
  set g : ℝ → ℝ := fun s => (-1) ^ k * (circulant fun i => (1 - s) * c i + s * e i).det with hg
  have hcont : Continuous g := by
    refine continuous_const.mul (Continuous.matrix_det (continuous_matrix fun i j => ?_))
    simp only [circulant_apply]
    fun_prop
  have hg1 : g 1 = 1 := by
    have h1 : (fun i => (1 - (1 : ℝ)) * c i + 1 * e i) = e := by
      funext i; ring
    show (-1) ^ k * (circulant fun i => (1 - (1 : ℝ)) * c i + 1 * e i).det = 1
    rw [h1, he, det_circulant_single_last, ← mul_pow]
    norm_num
  have hg0 : g 0 = (-1) ^ k * (circulant c).det := by
    have h1 : (fun i => (1 - (0 : ℝ)) * c i + 0 * e i) = c := by
      funext i; ring
    show (-1) ^ k * (circulant fun i => (1 - (0 : ℝ)) * c i + 0 * e i).det = _
    rw [h1]
  have hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, g s ≠ 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with rfl | hs1
    · rw [hg1]; exact one_ne_zero
    · have hpos : 0 < 1 - s := sub_pos.mpr hs1
      refine mul_ne_zero (pow_ne_zero _ (by norm_num)) (det_circulant_ne_zero _ ?_ ?_)
      · intro i j hij
        have hi : e i = 0 := by
          have hil : i ≠ Fin.last k := fun h => absurd (h ▸ hij) (not_lt.mpr (Fin.le_last j))
          simp [he, hil]
        have hj : 0 ≤ e j := by
          rw [he, Pi.single_apply]; split_ifs <;> norm_num
        have := mul_lt_mul_of_pos_left (hc hij) hpos
        have := mul_nonneg hs.1 hj
        simp only [hi]
        linarith
      · have h1 : 0 ≤ e 0 := by
          rw [he, Pi.single_apply]; split_ifs <;> norm_num
        have := mul_pos hpos h0
        have := mul_nonneg hs.1 h1
        linarith
  by_contra hneg
  rw [not_lt, ← hg0] at hneg
  have hmem : (0 : ℝ) ∈ Set.Icc (g 0) (g 1) := ⟨hneg, by rw [hg1]; exact zero_le_one⟩
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc zero_le_one hcont.continuousOn hmem
  exact hne s hs hs0

/-- **Theorem 1, odd size.** The circulant matrix of a strictly increasing positive real
vector of odd length has positive determinant. -/
theorem det_circulant_pos_of_odd {t : ℕ} (ht : Odd t) (c : Fin t → ℝ) (hc : StrictMono c)
    (hpos : ∀ i, 0 < c i) : 0 < (circulant c).det := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by have := ht.pos; omega⟩
  have hk : Even k := by
    rcases Nat.even_or_odd k with h | h
    · exact h
    · exact absurd ht (Nat.not_odd_iff_even.mpr h.add_one)
  have h := neg_one_pow_mul_det_circulant_pos c hc (hpos 0)
  rwa [hk.neg_one_pow, one_mul] at h

/-- **Theorem 1, even size.** The circulant matrix of a strictly increasing positive real
vector of even nonzero length has negative determinant. -/
theorem det_circulant_neg_of_even {t : ℕ} (ht : Even t) (ht0 : t ≠ 0) (c : Fin t → ℝ)
    (hc : StrictMono c) (hpos : ∀ i, 0 < c i) : (circulant c).det < 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have hk : Odd k := by
    rcases Nat.even_or_odd k with h | h
    · exact absurd ht (Nat.not_even_iff_odd.mpr h.add_one)
    · exact h
  have h := neg_one_pow_mul_det_circulant_pos c hc (hpos 0)
  rw [hk.neg_one_pow] at h
  linarith

/-! ## The number of divisors -/

theorem odd_prod_iff {S : Type*} (s : Finset S) (f : S → ℕ) :
    Odd (∏ i ∈ s, f i) ↔ ∀ i ∈ s, Odd (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [prod_insert hi, Nat.odd_mul, ih]

/-- The number of divisors of `n` is odd if and only if `n` is a nonzero square. -/
theorem odd_card_divisors_iff {n : ℕ} (hn : n ≠ 0) : Odd n.divisors.card ↔ IsSquare n := by
  rw [Nat.card_divisors hn, odd_prod_iff, Nat.isSquare_iff_even_factorization]
  constructor
  · intro h p hp
    by_cases hpn : p ∣ n
    · have := h p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩)
      exact (Nat.even_add_one.not_left.mp (Nat.not_even_iff_odd.mpr this))
    · simp [Nat.factorization_eq_zero_of_not_dvd hpn]
  · intro h p hp
    exact (h p (Nat.prime_of_mem_primeFactors hp)).add_one

/-! ## The sequence -/

/-- The divisors of `n` in increasing order. -/
def divisorList (n : ℕ) : List ℕ := n.divisors.sort (· ≤ ·)

/-- The sequence A306598: the determinant of the circulant matrix whose first column is the
list of divisors of `n` in increasing order. The value at `0` is `1`, the determinant of the
empty matrix. -/
def a (n : ℕ) : ℤ :=
  (circulant fun i : Fin (divisorList n).length => ((divisorList n)[i] : ℤ)).det

theorem length_divisorList (n : ℕ) : (divisorList n).length = n.divisors.card :=
  Finset.length_sort _

theorem strictMono_divisorList (n : ℕ) :
    StrictMono fun i : Fin (divisorList n).length => (((divisorList n)[i] : ℕ) : ℝ) := by
  intro i j hij
  exact Nat.cast_lt.mpr ((Finset.sortedLT_sort n.divisors).strictMono_get hij)

theorem divisorList_pos (n : ℕ) (i : Fin (divisorList n).length) :
    0 < (((divisorList n)[i] : ℕ) : ℝ) := by
  have h : (divisorList n)[i] ∈ n.divisors :=
    (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem _)
  exact Nat.cast_pos.mpr (Nat.pos_of_mem_divisors h)

theorem cast_a (n : ℕ) : ((a n : ℤ) : ℝ) =
    (circulant fun i : Fin (divisorList n).length => (((divisorList n)[i] : ℕ) : ℝ)).det := by
  have h : (circulant fun i : Fin (divisorList n).length => (((divisorList n)[i] : ℕ) : ℝ)) =
      (Int.castRingHom ℝ).mapMatrix
        (circulant fun i : Fin (divisorList n).length => ((divisorList n)[i] : ℤ)) := by
    ext i j
    simp
  rw [h, ← RingHom.map_det]
  rfl

/-- `a n` is positive when `n` is a square. -/
theorem a_pos_of_isSquare {n : ℕ} (h : IsSquare n) : 0 < a n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [a, divisorList]
  have hodd : Odd (divisorList n).length := by
    rw [length_divisorList]; exact (odd_card_divisors_iff hn).mpr h
  have := det_circulant_pos_of_odd hodd _ (strictMono_divisorList n) (divisorList_pos n)
  rw [← cast_a] at this
  exact_mod_cast this

/-- `a n` is negative when `n` is not a square. -/
theorem a_neg_of_not_isSquare {n : ℕ} (h : ¬IsSquare n) : a n < 0 := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact h ⟨0, rfl⟩
  have heven : Even (divisorList n).length := by
    rw [length_divisorList, ← Nat.not_odd_iff_even, odd_card_divisors_iff hn]; exact h
  have hne : (divisorList n).length ≠ 0 := by
    rw [length_divisorList]; simpa using hn
  have := det_circulant_neg_of_even heven hne _ (strictMono_divisorList n) (divisorList_pos n)
  rw [← cast_a] at this
  exact_mod_cast this

/-- **Main theorem (the conjecture in OEIS A306598).** `a(n) > 0` if and only if `n` is a
square. -/
theorem a_pos_iff (n : ℕ) : 0 < a n ↔ IsSquare n := by
  constructor
  · intro h
    by_contra hsq
    exact absurd (a_neg_of_not_isSquare hsq) (not_lt.mpr h.le)
  · exact a_pos_of_isSquare

/-- `a(n)` is never zero. -/
theorem a_ne_zero (n : ℕ) : a n ≠ 0 := by
  by_cases h : IsSquare n
  · exact (a_pos_of_isSquare h).ne'
  · exact (a_neg_of_not_isSquare h).ne

/-! ## Sanity checks against the OEIS data

`a` is computable (`#eval (List.range 9).map a` gives `[1, 1, -3, -8, 49, -24, -960, -48, -3375]`).
The first eight terms are also checked here by the kernel. -/

theorem a_eq_of_divisorList {n : ℕ} {l : List ℕ} (h : divisorList n = l) :
    a n = (circulant fun i : Fin l.length => (l[i] : ℤ)).det := by
  subst h
  rfl

theorem divisorList_eq {n : ℕ} {l : List ℕ} (hs : l.SortedLT) (h : n.divisors = l.toFinset) :
    divisorList n = l := by
  unfold divisorList
  rw [h]
  exact List.SortedLT.sort_toFinset hs

example : a 1 = 1 := by
  rw [a_eq_of_divisorList (l := [1]) (divisorList_eq (by decide) (by decide))]
  decide

example : a 2 = -3 := by
  rw [a_eq_of_divisorList (l := [1, 2]) (divisorList_eq (by decide) (by decide))]
  decide

example : a 3 = -8 := by
  rw [a_eq_of_divisorList (l := [1, 3]) (divisorList_eq (by decide) (by decide))]
  decide

example : a 4 = 49 := by
  rw [a_eq_of_divisorList (l := [1, 2, 4]) (divisorList_eq (by decide) (by decide))]
  decide

example : a 5 = -24 := by
  rw [a_eq_of_divisorList (l := [1, 5]) (divisorList_eq (by decide) (by decide))]
  decide

example : a 6 = -960 := by
  rw [a_eq_of_divisorList (l := [1, 2, 3, 6]) (divisorList_eq (by decide) (by decide))]
  decide

example : a 7 = -48 := by
  rw [a_eq_of_divisorList (l := [1, 7]) (divisorList_eq (by decide) (by decide))]
  decide

example : a 8 = -3375 := by
  rw [a_eq_of_divisorList (l := [1, 2, 4, 8]) (divisorList_eq (by decide) (by decide))]
  decide

end OeisProofs.A306598
