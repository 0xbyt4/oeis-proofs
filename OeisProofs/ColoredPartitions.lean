import Mathlib

/-!
# Colored partitions counted by color sum (OEIS A392002, A389343, A390208, A390217, A387957)

Fix `m >= 1`. A partition of `n` with parts colored by `{0, ..., m-1}` is a multiset of pairs
`(part, color)` with positive parts summing to `n`; its color sum is the sum of its colors.
`N m r n` is the number of such colored partitions of `n` whose color sum is congruent to `r`
modulo `m`, and `T m n` is the number of all of them.

With `P(x) = prod_{j >= 1} 1 / (1 - x^j)` the theorem proved here is

  `sum_n N_{m,r}(n) x^n = (1/m) * sum_{d | m} c_d(r) * P(x^d)^(m/d)`,

where `c_d(r)` is the Ramanujan sum. See `proofs/colored-partitions.md` for the informal proof.

## Definitions

* `coloredPartitions m n : Set (Multiset (ℕ × Fin m))`: the multisets `s` of pairs
  `(part, color)` with `0 < part` for every element and `(s.map Prod.fst).sum = n`.
* `colorSum s = (s.map fun x => (x.2 : ℕ)).sum`.
* `N m r n = Set.ncard {s | s ∈ coloredPartitions m n ∧ colorSum s ≡ r [MOD m]}`.
* `T m n = Set.ncard (coloredPartitions m n)`.
* `ramanujanSum d r : ℤ`, defined by the Moebius divisor formula
  `sum_{e | gcd(d, r)} mu(d / e) * e`.

The encoding is faithful because it is the informal definition verbatim: a colored partition
is a finite multiset of (part, color) pairs, a color is an element of `Fin m`, and the only
conditions are positivity of the parts and the value of the sum of the parts. `Set.ncard` is
the cardinality of a set and is only meaningful for finite sets; `coloredPartitions_finite`
proves that `coloredPartitions m n` is finite. The residue `r` is a natural number; since only
`r` modulo `m` matters this covers all integer residues.

## Main results

* `main`, `main_gcd`: for `0 < m`, as integers,
  `m * N m r n = sum_{d | gcd(m, n)} c_d(r) * T (m / d) (n / d)`.
  This is the theorem coefficientwise: the coefficient of `x^n` in `P(x^d)^(m/d)` is
  `T (m / d) (n / d)` if `d | n` and `0` otherwise.
* `main_powerSeries`: the same statement as an identity of power series over `ℂ`,
  `m * sum_n N m r n x^n = sum_{d | m} c_d(r) * P(x^d)^(m/d)`, where
  `P = partitionGF = sum_n #(partitions of n) x^n`.
* `partitionGF_mul_tprod`: `P(x) * prod_{j >= 1} (1 - x^j) = 1`.
* `T_one`: `T 1 k` is the number of partitions of `k`; `mk_T`: `sum_k T c k x^k = P(x)^c`.
* `sum_primitiveRoots_pow`: `c_d(r)` is the sum of `u^r` over the primitive `d`-th roots of
  unity `u` in `ℂ`.
* `A392002`, `A389343`, `A390208`, `A390217`, `A387957`: the five OEIS special cases.
* `N_eq_of_gcd_eq`: `N m r n` depends on `r` only through `gcd(m, r)`.

## Proof outline

A colored partition is split into the family of the multisets of its parts of each color
(`split`, `merge`). This identifies the sum of `z ^ colorSum s` over all colored partitions `s`
of `n` with the coefficient of `x^n` in `prod_{c < m} G (z^c)`, where
`G a = sum_n (sum_{p partition of n} a ^ #parts(p)) x^n = prod_{i >= 1} 1 / (1 - a x^i)`
(Mathlib's `Nat.Partition.hasProd_genFun`). If `z` is a primitive `d`-th root of unity with
`d | m`, then `prod_{c < m} (1 - z^c y) = (1 - y^d)^(m/d)`, hence
`prod_{c < m} G (z^c) = P(x^d)^(m/d)` (`prod_G`). The roots-of-unity filter
(`sum_nthRoots_pow`) and Moebius inversion (`sum_primitiveRoots_pow`) finish the proof.

## Numerical check

The theorems `A392002_data`, `A389343_data`, `A390208_data`, `A390217_data` and
`A387957_data` prove, as kernel-checked theorems about `N` itself, that `N m r n` for
`n = 0, ..., 9` is the OEIS data:

* `N 2 1`: 0, 1, 2, 5, 9, 18, 31, 55, 90, 150 (A392002)
* `N 3 0`: 1, 1, 3, 8, 17, 36, 75, 143, 270, 495 (A389343)
* `N 3 1`: 0, 1, 3, 7, 17, 36, 73, 143, 270, 492 (A390208)
* `N 4 0`: 1, 1, 4, 10, 28, 63, 146, 310, 651, 1295 (A390217)
* `N 4 1`: 0, 1, 3, 10, 25, 63, 141, 310, 640, 1295 (A387957)

The proofs do not evaluate `Ncomp` (the kernel cannot reduce it). They use the five
corollaries above, which express `N` through `T`. The partition numbers `p(0), ..., p(9)` come
from the Euler product of `P` truncated to nine factors, whose coefficients the kernel computes
with `decide +kernel` (`pp_nine`). Then `T c n` for `n < 10` is the `c`-fold convolution of
these numbers (`T_eq_Tv`). No `native_decide` is used.
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace OeisProofs.ColoredPartitions

/-! ### Definitions -/

/-- The set of partitions of `n` with parts colored by `Fin m`: finite multisets of pairs
`(part, color)` with all parts positive and parts summing to `n`. -/
def coloredPartitions (m n : ℕ) : Set (Multiset (ℕ × Fin m)) :=
  {s | (∀ x ∈ s, 0 < x.1) ∧ (s.map Prod.fst).sum = n}

/-- The color sum of a colored partition: the sum of the colors of its parts. -/
def colorSum {m : ℕ} (s : Multiset (ℕ × Fin m)) : ℕ := (s.map fun x => (x.2 : ℕ)).sum

/-- `N m r n`: the number of partitions of `n` with parts colored by `{0, ..., m-1}` whose color
sum is congruent to `r` modulo `m`. -/
noncomputable def N (m r n : ℕ) : ℕ :=
  Set.ncard {s : Multiset (ℕ × Fin m) | s ∈ coloredPartitions m n ∧ colorSum s ≡ r [MOD m]}

/-- `T m n`: the total number of partitions of `n` with parts colored by `{0, ..., m-1}`. -/
noncomputable def T (m n : ℕ) : ℕ := Set.ncard (coloredPartitions m n)

/-- The Ramanujan sum `c_d(r)`, defined by the Moebius divisor formula
`c_d(r) = sum_{e | gcd(d, r)} mu(d / e) * e`. It is the sum of the `r`-th powers of the
primitive `d`-th roots of unity, see `sum_primitiveRoots_pow`. -/
def ramanujanSum (d r : ℕ) : ℤ :=
  ∑ e ∈ (Nat.gcd d r).divisors, ArithmeticFunction.moebius (d / e) * (e : ℤ)

/-! ### The power series `G a = prod_{i >= 1} 1 / (1 - a x^i)` -/

/-- `G a = sum_n (sum_{p partition of n} a ^ (number of parts of p)) x^n`. -/
noncomputable def G (a : ℂ) : ℂ⟦X⟧ := Nat.Partition.genFun fun _ k => a ^ k

theorem coeff_G (a : ℂ) (n : ℕ) :
    coeff n (G a) = ∑ p : n.Partition, a ^ Multiset.card p.parts := by
  rw [G, Nat.Partition.coeff_genFun]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Multiset.toFinsupp_sum_eq]
  rfl

/-- The `i`-th Euler factor of `G a`, the geometric series `1 / (1 - a X^(i+1))`. -/
noncomputable def eulerFactor (a : ℂ) (i : ℕ) : ℂ⟦X⟧ :=
  1 + ∑' j : ℕ, a ^ (j + 1) • (X : ℂ⟦X⟧) ^ ((i + 1) * (j + 1))

theorem hasProd_G (a : ℂ) : HasProd (eulerFactor a) (G a) := by
  unfold G
  exact Nat.Partition.hasProd_genFun (fun _ k => a ^ k)

theorem eulerFactor_mul (a : ℂ) (i : ℕ) :
    eulerFactor a i * (1 - C a * X ^ (i + 1)) = 1 := by
  have hc : constantCoeff (C a * X ^ (i + 1) : ℂ⟦X⟧) = 0 := by simp
  have h : eulerFactor a i = ∑' j : ℕ, (C a * X ^ (i + 1) : ℂ⟦X⟧) ^ j := by
    rw [(WithPiTopology.summable_pow_of_constantCoeff_eq_zero hc).tsum_eq_zero_add]
    simp [eulerFactor, mul_pow, pow_mul, smul_eq_C_mul]
  rw [h, WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hc]

theorem continuous_expand (d : ℕ) (hd : d ≠ 0) :
    Continuous (expand d hd : ℂ⟦X⟧ → ℂ⟦X⟧) := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simp only [coeff_expand]
  split_ifs
  · exact (WithPiTopology.continuous_coeff ℂ _).continuousAt
  · exact tendsto_const_nhds

theorem prod_range_one_sub_mul {S : Type*} [CommRing S] [IsDomain S] {z : S} {d : ℕ}
    (hd : 0 < d) (hz : IsPrimitiveRoot z d) (q : ℕ) (y : S) :
    ∏ c ∈ range (d * q), (1 - z ^ c * y) = (1 - y ^ d) ^ q := by
  have base : ∏ c ∈ range d, (1 - z ^ c * y) = 1 - y ^ d := by
    have h := hz.pow_sub_pow_eq_prod_sub_mul 1 y hd
    rw [one_pow] at h
    rw [h]
    refine Finset.prod_bij (fun i _ => z ^ i) ?_ ?_ ?_ ?_
    · intro i _
      rw [Polynomial.mem_nthRootsFinset hd, ← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]
    · intro i hi j hj hij
      exact hz.pow_inj (mem_range.mp hi) (mem_range.mp hj) hij
    · intro u hu
      rw [Polynomial.mem_nthRootsFinset hd] at hu
      have : NeZero d := ⟨hd.ne'⟩
      obtain ⟨i, hi, rfl⟩ := hz.eq_pow_of_pow_eq_one hu
      exact ⟨i, mem_range.mpr hi, rfl⟩
    · intro i _; rfl
  induction q with
  | zero => simp
  | succ q ih =>
    rw [mul_add, mul_one, Finset.prod_range_add, ih, pow_succ]
    congr 1
    rw [← base]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [pow_add, pow_mul, hz.pow_eq_one, one_pow, one_mul]

theorem prod_G {d m : ℕ} (hd : 0 < d) (hdm : d ∣ m) {z : ℂ} (hz : IsPrimitiveRoot z d) :
    ∏ c ∈ range m, G (z ^ c) = (expand d hd.ne' (G 1)) ^ (m / d) := by
  have h1 : HasProd (fun i => ∏ c ∈ range m, eulerFactor (z ^ c) i) (∏ c ∈ range m, G (z ^ c)) :=
    hasProd_prod fun c _ => hasProd_G _
  have h2 : HasProd (fun i => (expand d hd.ne' (eulerFactor 1 i)) ^ (m / d))
      ((expand d hd.ne' (G 1)) ^ (m / d)) :=
    ((hasProd_G 1).map (expand d hd.ne') (continuous_expand d hd.ne')).pow _
  refine h1.unique (h2.congr_fun fun i => ?_)
  have hC : IsPrimitiveRoot (C z : ℂ⟦X⟧) d := hz.map_of_injective C_injective
  have hU : ∏ c ∈ range m, (1 - C (z ^ c) * X ^ (i + 1) : ℂ⟦X⟧) =
      (1 - (X ^ (i + 1)) ^ d) ^ (m / d) := by
    have := prod_range_one_sub_mul hd hC (m / d) (X ^ (i + 1) : ℂ⟦X⟧)
    rw [Nat.mul_div_cancel' hdm] at this
    simpa using this
  have hA : (∏ c ∈ range m, eulerFactor (z ^ c) i) *
      ∏ c ∈ range m, (1 - C (z ^ c) * X ^ (i + 1) : ℂ⟦X⟧) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun c _ => eulerFactor_mul _ _
  have hB : (expand d hd.ne' (eulerFactor 1 i)) ^ (m / d) *
      (1 - (X ^ (i + 1)) ^ d : ℂ⟦X⟧) ^ (m / d) = 1 := by
    rw [← mul_pow]
    have := congrArg (expand d hd.ne') (eulerFactor_mul 1 i)
    simp only [map_mul, map_sub, map_one, map_pow, expand_X, one_mul] at this
    rw [← pow_mul, mul_comm (i + 1) d, pow_mul]
    rw [this, one_pow]
  calc ∏ c ∈ range m, eulerFactor (z ^ c) i
      = (∏ c ∈ range m, eulerFactor (z ^ c) i) *
          ((expand d hd.ne' (eulerFactor 1 i)) ^ (m / d) *
            (1 - (X ^ (i + 1)) ^ d : ℂ⟦X⟧) ^ (m / d)) := by rw [hB, mul_one]
    _ = ((∏ c ∈ range m, eulerFactor (z ^ c) i) *
          ∏ c ∈ range m, (1 - C (z ^ c) * X ^ (i + 1) : ℂ⟦X⟧)) *
          (expand d hd.ne' (eulerFactor 1 i)) ^ (m / d) := by rw [hU]; ring
    _ = (expand d hd.ne' (eulerFactor 1 i)) ^ (m / d) := by rw [hA, one_mul]


/-! ### Colored partitions as multisets of (part, color) pairs -/

section Split

variable {m : ℕ}

/-- Merge a family of multisets of parts, one for each color, into one multiset of colored
parts. -/
def merge (g : Fin m → Multiset ℕ) : Multiset (ℕ × Fin m) :=
  ∑ c, (g c).map fun x => (x, c)

/-- The multiset of the parts of color `c`. -/
def split (s : Multiset (ℕ × Fin m)) (c : Fin m) : Multiset ℕ :=
  (s.filter fun x => x.2 = c).map Prod.fst

theorem multiset_map_finset_sum {A B I : Type*} (f : A → B) (S : Finset I) (h : I → Multiset A) :
    (∑ i ∈ S, h i).map f = ∑ i ∈ S, (h i).map f :=
  map_sum (Multiset.mapAddMonoidHom f) h S

theorem multiset_sum_finset_sum {I : Type*} (S : Finset I) (h : I → Multiset ℕ) :
    (∑ i ∈ S, h i).sum = ∑ i ∈ S, (h i).sum :=
  map_sum (Multiset.sumAddMonoidHom (M := ℕ)) h S

theorem merge_split (s : Multiset (ℕ × Fin m)) : merge (split s) = s := by
  unfold merge split
  have h1 : ∀ c : Fin m, ((s.filter fun x => x.2 = c).map Prod.fst).map (fun x => (x, c)) =
      s.filter fun x => x.2 = c := by
    intro c
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id (s.filter fun x => x.2 = c)]
    refine Multiset.map_congr rfl fun x hx => ?_
    have := (Multiset.mem_filter.mp hx).2
    simp [← this]
  simp_rw [h1]
  clear h1
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.filter_cons, Finset.sum_add_distrib, ih]
    simp

theorem split_merge (g : Fin m → Multiset ℕ) : split (merge g) = g := by
  funext c
  unfold merge split
  have key : ∀ S : Finset (Fin m),
      ((∑ c' ∈ S, (g c').map fun x => (x, c')).filter fun x => x.2 = c).map Prod.fst =
        if c ∈ S then g c else 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Multiset.filter_add, Multiset.map_add, ih, Multiset.filter_map,
        Multiset.map_map]
      by_cases hac : a = c
      · subst hac
        simp [ha]
      · have hca : c ≠ a := fun h => hac h.symm
        simp [hac, hca]
  simpa using key Finset.univ

theorem map_fst_merge (g : Fin m → Multiset ℕ) : (merge g).map Prod.fst = ∑ c, g c := by
  unfold merge
  rw [multiset_map_finset_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Multiset.map_map]
  exact Multiset.map_id _

theorem sum_parts_merge (g : Fin m → Multiset ℕ) :
    ((merge g).map Prod.fst).sum = ∑ c, (g c).sum := by
  rw [map_fst_merge, multiset_sum_finset_sum]

theorem colorSum_merge (g : Fin m → Multiset ℕ) :
    colorSum (merge g) = ∑ c : Fin m, (c : ℕ) * Multiset.card (g c) := by
  unfold colorSum merge
  rw [multiset_map_finset_sum, multiset_sum_finset_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Multiset.map_map]
  simp [mul_comm]

theorem mem_merge (g : Fin m → Multiset ℕ) (x : ℕ × Fin m) : x ∈ merge g ↔ x.1 ∈ g x.2 := by
  unfold merge
  rw [Multiset.mem_sum]
  constructor
  · rintro ⟨c, -, hx⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    exact hy
  · intro hx
    exact ⟨x.2, Finset.mem_univ _, Multiset.mem_map.mpr ⟨x.1, hx, rfl⟩⟩

theorem merge_injective : Function.Injective (merge (m := m)) :=
  Function.LeftInverse.injective split_merge

end Split

/-! ### The finite set of colored partitions -/

/-- The finite set of multisets of positive integers with sum `k` (the partitions of `k`). -/
def partsFinset (k : ℕ) : Finset (Multiset ℕ) :=
  (Finset.univ : Finset k.Partition).image fun p => p.parts

theorem mem_partsFinset {k : ℕ} {s : Multiset ℕ} :
    s ∈ partsFinset k ↔ (∀ x ∈ s, 0 < x) ∧ s.sum = k := by
  simp only [partsFinset, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨fun x hx => p.parts_pos hx, p.parts_sum⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨s, fun {x} hx => h1 x hx, h2⟩, rfl⟩

/-- The finite set of families `g : Fin m → Multiset ℕ` of multisets of positive integers with
total sum `n`. The family `g` encodes the colored partition `merge g`. -/
def famFinset (m n : ℕ) : Finset (Fin m → Multiset ℕ) :=
  (Finset.finsuppAntidiag (Finset.univ : Finset (Fin m)) n).biUnion fun l =>
    Fintype.piFinset fun c => partsFinset (l c)

theorem mem_famFinset {m n : ℕ} {g : Fin m → Multiset ℕ} :
    g ∈ famFinset m n ↔ (∀ c, ∀ x ∈ g c, 0 < x) ∧ ∑ c, (g c).sum = n := by
  simp only [famFinset, mem_biUnion, mem_finsuppAntidiag, Fintype.mem_piFinset, mem_partsFinset]
  constructor
  · rintro ⟨l, ⟨hl, -⟩, h⟩
    refine ⟨fun c => (h c).1, ?_⟩
    rw [← hl]
    exact Finset.sum_congr rfl fun c _ => (h c).2
  · rintro ⟨h1, h2⟩
    exact ⟨Finsupp.equivFunOnFinite.symm fun c => (g c).sum, ⟨by simpa using h2, by simp⟩,
      fun c => ⟨h1 c, by simp⟩⟩

theorem merge_mem_coloredPartitions {m n : ℕ} {g : Fin m → Multiset ℕ} :
    merge g ∈ coloredPartitions m n ↔ g ∈ famFinset m n := by
  rw [mem_famFinset, coloredPartitions, Set.mem_ofPred_eq, sum_parts_merge]
  refine and_congr_left fun _ => ?_
  constructor
  · intro h c x hx
    exact h (x, c) ((mem_merge g (x, c)).mpr hx)
  · intro h x hx
    exact h x.2 x.1 ((mem_merge g x).mp hx)

theorem coloredPartitions_eq_image (m n : ℕ) :
    coloredPartitions m n = merge '' (famFinset m n : Set (Fin m → Multiset ℕ)) := by
  ext s
  constructor
  · intro hs
    refine ⟨split s, ?_, merge_split s⟩
    rw [Finset.mem_coe, ← merge_mem_coloredPartitions, merge_split]
    exact hs
  · rintro ⟨g, hg, rfl⟩
    exact merge_mem_coloredPartitions.mpr hg

theorem coloredPartitions_finite (m n : ℕ) : (coloredPartitions m n).Finite := by
  rw [coloredPartitions_eq_image]
  exact (Finset.finite_toSet _).image _

theorem T_eq_card (m n : ℕ) : T m n = (famFinset m n).card := by
  rw [T, coloredPartitions_eq_image, Set.ncard_image_of_injective _ merge_injective,
    Set.ncard_coe_finset]

/-- A computable form of `N`, used for the proof and for numerical checks: the number of
families `g` in `famFinset m n` with `sum_c c * #(g c)` congruent to `r` modulo `m`. -/
def Ncomp (m r n : ℕ) : ℕ :=
  ((famFinset m n).filter fun g =>
    ∑ c : Fin m, (c : ℕ) * Multiset.card (g c) ≡ r [MOD m]).card

theorem N_eq_card (m r n : ℕ) : N m r n = Ncomp m r n := by
  unfold Ncomp
  have : {s : Multiset (ℕ × Fin m) | s ∈ coloredPartitions m n ∧ colorSum s ≡ r [MOD m]} =
      merge '' (((famFinset m n).filter fun g =>
        ∑ c : Fin m, (c : ℕ) * Multiset.card (g c) ≡ r [MOD m] : Finset _) :
          Set (Fin m → Multiset ℕ)) := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, Finset.mem_filter]
    constructor
    · rintro ⟨hs, hr⟩
      refine ⟨split s, ⟨?_, ?_⟩, merge_split s⟩
      · rw [← merge_mem_coloredPartitions, merge_split]
        exact hs
      · rw [← colorSum_merge, merge_split]
        exact hr
    · rintro ⟨g, ⟨hg, hr⟩, rfl⟩
      exact ⟨merge_mem_coloredPartitions.mpr hg, by rw [colorSum_merge]; exact hr⟩
  rw [N, this, Set.ncard_image_of_injective _ merge_injective, Set.ncard_coe_finset]

/-! ### The generating function of colored partitions -/

theorem coeff_prod_G (m n : ℕ) (a : Fin m → ℂ) :
    coeff n (∏ c : Fin m, G (a c)) =
      ∑ g ∈ famFinset m n, ∏ c, a c ^ Multiset.card (g c) := by
  rw [coeff_prod, famFinset, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.prod_univ_sum (fun c => partsFinset (l c))
      (fun c s => a c ^ Multiset.card s)]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [coeff_G, partsFinset, Finset.sum_image]
    intro p _ q _ h
    exact Nat.Partition.ext h
  · intro l _ l' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro g hg hg'
    apply hne
    ext c
    rw [Fintype.mem_piFinset] at hg hg'
    exact ((mem_partsFinset.mp (hg c)).2).symm.trans (mem_partsFinset.mp (hg' c)).2


/-! ### Roots of unity and Ramanujan sums -/

/-- The roots-of-unity filter. -/
theorem sum_nthRoots_pow {m : ℕ} (hm : 0 < m) (a b : ℕ) :
    ∑ u ∈ Polynomial.nthRootsFinset m (1 : ℂ), (u ^ b)⁻¹ * u ^ a =
      if a ≡ b [MOD m] then (m : ℂ) else 0 := by
  have hw : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / m)) m :=
    Complex.isPrimitiveRoot_exp m hm.ne'
  generalize Complex.exp (2 * Real.pi * Complex.I / m) = w at hw
  have : NeZero m := ⟨hm.ne'⟩
  have hbij : ∑ u ∈ Polynomial.nthRootsFinset m (1 : ℂ), (u ^ b)⁻¹ * u ^ a =
      ∑ k ∈ range m, ((w ^ b)⁻¹ * w ^ a) ^ k := by
    symm
    refine Finset.sum_bij (fun k _ => w ^ k) ?_ ?_ ?_ ?_
    · intro i _
      rw [Polynomial.mem_nthRootsFinset hm, ← pow_mul, mul_comm, pow_mul, hw.pow_eq_one, one_pow]
    · intro i hi j hj hij
      exact hw.pow_inj (mem_range.mp hi) (mem_range.mp hj) hij
    · intro u hu
      rw [Polynomial.mem_nthRootsFinset hm] at hu
      obtain ⟨i, hi, rfl⟩ := hw.eq_pow_of_pow_eq_one hu
      exact ⟨i, mem_range.mpr hi, rfl⟩
    · intro k _
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm b, mul_comm a]
  rw [hbij]
  have hne : w ^ b ≠ 0 := pow_ne_zero _ (hw.ne_zero hm.ne')
  have hx1 : (w ^ b)⁻¹ * w ^ a = 1 ↔ a ≡ b [MOD m] := by
    rw [inv_mul_eq_one₀ hne, (hw.isOfFinOrder hm.ne').pow_eq_pow_iff_modEq, ← hw.eq_orderOf]
    exact Nat.ModEq.comm
  split_ifs with h
  · rw [hx1.mpr h]
    simp
  · have hxm : ((w ^ b)⁻¹ * w ^ a) ^ m = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm b, mul_comm a, pow_mul, pow_mul,
        hw.pow_eq_one]
      simp
    rw [geom_sum_eq (fun h' => h (hx1.mp h')), hxm]
    simp

theorem sum_nthRoots_eq_sum_divisors (m : ℕ) (f : ℂ → ℂ) :
    ∑ u ∈ Polynomial.nthRootsFinset m (1 : ℂ), f u =
      ∑ d ∈ m.divisors, ∑ u ∈ primitiveRoots d ℂ, f u := by
  rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots, Finset.sum_biUnion]
  intro i _ j _ hij
  exact IsPrimitiveRoot.disjoint hij

/-- The Ramanujan sum is the sum of the `r`-th powers of the primitive `d`-th roots of unity. -/
theorem sum_primitiveRoots_pow {d : ℕ} (hd : 0 < d) (r : ℕ) :
    ∑ u ∈ primitiveRoots d ℂ, u ^ r = (ramanujanSum d r : ℂ) := by
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℂ)
    (f := fun d => ∑ u ∈ primitiveRoots d ℂ, u ^ r)
    (g := fun n => if n ∣ r then (n : ℂ) else 0)).mp ?_ d hd
  · rw [← key, Nat.sum_divisorsAntidiagonal'
      (f := fun x y => (ArithmeticFunction.moebius x : ℂ) * if y ∣ r then (y : ℂ) else 0)]
    have hfil : (Nat.gcd d r).divisors = d.divisors.filter (· ∣ r) := by
      ext e
      simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff, ne_eq,
        Nat.gcd_eq_zero_iff]
      have := hd.ne'
      tauto
    rw [ramanujanSum, hfil, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  · intro n hn
    rw [← sum_nthRoots_eq_sum_divisors]
    have := sum_nthRoots_pow hn r 0
    simpa [Nat.modEq_zero_iff_dvd] using this

theorem sum_primitiveRoots_inv_pow {d : ℕ} (hd : 0 < d) (r : ℕ) :
    ∑ u ∈ primitiveRoots d ℂ, (u ^ r)⁻¹ = (ramanujanSum d r : ℂ) := by
  rw [← sum_primitiveRoots_pow hd]
  refine Finset.sum_bij (fun u _ => u⁻¹) ?_ ?_ ?_ ?_
  · intro u hu
    rw [mem_primitiveRoots hd] at hu ⊢
    exact hu.inv
  · intro a _ b _ h
    exact inv_injective h
  · intro u hu
    refine ⟨u⁻¹, ?_, inv_inv u⟩
    rw [mem_primitiveRoots hd] at hu ⊢
    exact hu.inv
  · intro u _
    rw [inv_pow]

/-! ### The main theorem -/

theorem coeff_G_one_pow (q k : ℕ) : coeff k (G 1 ^ q) = (T q k : ℂ) := by
  have := coeff_prod_G q k (fun _ => 1)
  simpa [T_eq_card] using this

theorem weighted_count (m n : ℕ) (u : ℂ) :
    ∑ g ∈ famFinset m n, u ^ (∑ c : Fin m, (c : ℕ) * Multiset.card (g c)) =
      coeff n (∏ c ∈ range m, G (u ^ c)) := by
  rw [← Fin.prod_univ_eq_prod_range (fun c => G (u ^ c)) m, coeff_prod_G]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  simp [pow_mul]

theorem coeff_prod_G_of_isPrimitiveRoot {d m : ℕ} (hd : 0 < d) (hdm : d ∣ m) {u : ℂ}
    (hu : IsPrimitiveRoot u d) (n : ℕ) :
    coeff n (∏ c ∈ range m, G (u ^ c)) = if d ∣ n then (T (m / d) (n / d) : ℂ) else 0 := by
  rw [prod_G hd hdm hu, ← map_pow, coeff_expand, coeff_G_one_pow]

theorem main_complex {m : ℕ} (hm : 0 < m) (r n : ℕ) :
    (m : ℂ) * N m r n =
      ∑ d ∈ m.divisors, if d ∣ n then (ramanujanSum d r : ℂ) * T (m / d) (n / d) else 0 := by
  calc (m : ℂ) * N m r n
      = ∑ g ∈ famFinset m n,
          if ∑ c : Fin m, (c : ℕ) * Multiset.card (g c) ≡ r [MOD m] then (m : ℂ) else 0 := by
        rw [N_eq_card, Ncomp, Finset.card_filter]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        split_ifs <;> simp
    _ = ∑ g ∈ famFinset m n, ∑ u ∈ Polynomial.nthRootsFinset m (1 : ℂ),
          (u ^ r)⁻¹ * u ^ (∑ c : Fin m, (c : ℕ) * Multiset.card (g c)) :=
        Finset.sum_congr rfl fun g _ => (sum_nthRoots_pow hm _ _).symm
    _ = ∑ u ∈ Polynomial.nthRootsFinset m (1 : ℂ),
          (u ^ r)⁻¹ * coeff n (∏ c ∈ range m, G (u ^ c)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← weighted_count, Finset.mul_sum]
    _ = ∑ d ∈ m.divisors, ∑ u ∈ primitiveRoots d ℂ,
          (u ^ r)⁻¹ * coeff n (∏ c ∈ range m, G (u ^ c)) :=
        sum_nthRoots_eq_sum_divisors m _
    _ = ∑ d ∈ m.divisors,
          if d ∣ n then (ramanujanSum d r : ℂ) * T (m / d) (n / d) else 0 := by
        refine Finset.sum_congr rfl fun d hd => ?_
        have hdpos := Nat.pos_of_mem_divisors hd
        have hdm := Nat.dvd_of_mem_divisors hd
        have h : ∀ u ∈ primitiveRoots d ℂ, (u ^ r)⁻¹ * coeff n (∏ c ∈ range m, G (u ^ c)) =
            (u ^ r)⁻¹ * (if d ∣ n then (T (m / d) (n / d) : ℂ) else 0) := fun u hu => by
          rw [coeff_prod_G_of_isPrimitiveRoot hdpos hdm ((mem_primitiveRoots hdpos).mp hu)]
        rw [Finset.sum_congr rfl h, ← Finset.sum_mul, sum_primitiveRoots_inv_pow hdpos]
        split_ifs <;> simp

/-- **Main theorem**, coefficientwise, as an identity of integers. -/
theorem main {m : ℕ} (hm : 0 < m) (r n : ℕ) :
    (m : ℤ) * N m r n =
      ∑ d ∈ m.divisors, if d ∣ n then ramanujanSum d r * (T (m / d) (n / d) : ℤ) else 0 := by
  have h := main_complex hm r n
  exact_mod_cast h

/-- **Main theorem**, with the sum running over the common divisors of `m` and `n`. -/
theorem main_gcd {m : ℕ} (hm : 0 < m) (r n : ℕ) :
    (m : ℤ) * N m r n =
      ∑ d ∈ (Nat.gcd m n).divisors, ramanujanSum d r * (T (m / d) (n / d) : ℤ) := by
  have hfil : (Nat.gcd m n).divisors = m.divisors.filter (· ∣ n) := by
    ext e
    simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff, ne_eq, Nat.gcd_eq_zero_iff]
    have := hm.ne'
    tauto
  rw [main hm, hfil, Finset.sum_filter]

/-! ### Link with ordinary partitions and with `P(x) = prod_{j >= 1} 1 / (1 - x^j)` -/

/-- The generating function `P` of the partition numbers. -/
noncomputable def partitionGF : ℂ⟦X⟧ := PowerSeries.mk fun n => (Fintype.card n.Partition : ℂ)

theorem G_one : G 1 = partitionGF := by
  ext n
  rw [coeff_G, partitionGF, coeff_mk]
  simp

/-- `P(x) * prod_{j >= 1} (1 - x^j) = 1`. -/
theorem partitionGF_mul_tprod : partitionGF * ∏' i : ℕ, (1 - (X : ℂ⟦X⟧) ^ (i + 1)) = 1 := by
  have h1 := (hasProd_G 1).mul (WithPiTopology.multipliable_one_sub_X_pow (R := ℂ)).hasProd
  have h2 : (fun i => eulerFactor 1 i * (1 - (X : ℂ⟦X⟧) ^ (i + 1))) = fun _ => 1 := by
    funext i
    simpa using eulerFactor_mul 1 i
  rw [h2, G_one] at h1
  exact h1.unique hasProd_one

/-- With one color, colored partitions are ordinary partitions. -/
theorem T_one (k : ℕ) : T 1 k = Fintype.card k.Partition := by
  have h := coeff_G_one_pow 1 k
  rw [pow_one, G_one, partitionGF, coeff_mk] at h
  exact_mod_cast h.symm

/-- The generating function of `T c` is `P(x)^c`. -/
theorem mk_T (c : ℕ) : PowerSeries.mk (fun k => (T c k : ℂ)) = partitionGF ^ c := by
  ext k
  rw [coeff_mk, ← G_one, coeff_G_one_pow]

/-- **Main theorem**, as an identity of power series:
`m * sum_n N_{m,r}(n) x^n = sum_{d | m} c_d(r) P(x^d)^(m/d)`. -/
theorem main_powerSeries {m : ℕ} (hm : 0 < m) (r : ℕ) :
    (m : ℂ) • PowerSeries.mk (fun n => (N m r n : ℂ)) =
      ∑ d ∈ m.divisors, (ramanujanSum d r : ℂ) • (partitionGF.subst (X ^ d)) ^ (m / d) := by
  ext n
  rw [map_smul, coeff_mk, smul_eq_mul, main_complex hm r n, map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  rw [map_smul, smul_eq_mul, ← expand_apply d hd0, ← map_pow, coeff_expand, ← G_one,
    coeff_G_one_pow]
  split_ifs <;> simp


/-! ### Values of the Ramanujan sums needed for the corollaries -/

theorem ramanujanSum_one (r : ℕ) : ramanujanSum 1 r = 1 := by
  simp [ramanujanSum]

theorem ramanujanSum_two_zero : ramanujanSum 2 0 = 1 := by
  rw [ramanujanSum, show Nat.gcd 2 0 = 2 from rfl, Nat.Prime.divisors Nat.prime_two]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two]

theorem ramanujanSum_two_one : ramanujanSum 2 1 = -1 := by
  simp [ramanujanSum, ArithmeticFunction.moebius_apply_prime Nat.prime_two]

theorem ramanujanSum_three_zero : ramanujanSum 3 0 = 2 := by
  rw [ramanujanSum, show Nat.gcd 3 0 = 3 from rfl, Nat.Prime.divisors Nat.prime_three]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_three]

theorem ramanujanSum_three_one : ramanujanSum 3 1 = -1 := by
  simp [ramanujanSum, ArithmeticFunction.moebius_apply_prime Nat.prime_three]

theorem moebius_four : ArithmeticFunction.moebius 4 = 0 := by
  have h := ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (k := 2) (by norm_num)
  norm_num at h
  exact h

theorem divisors_four : Nat.divisors 4 = {1, 2, 4} := by decide

theorem ramanujanSum_four_zero : ramanujanSum 4 0 = 2 := by
  rw [ramanujanSum, show Nat.gcd 4 0 = 4 from rfl, divisors_four]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two, moebius_four]

theorem ramanujanSum_four_one : ramanujanSum 4 1 = 0 := by
  simp [ramanujanSum, moebius_four]

/-! ### The five OEIS sequences -/

/-- A392002 (`m = 2`, `r = 1`): generating function `(P(x)^2 - P(x^2)) / 2`. -/
theorem A392002 (n : ℕ) :
    (2 : ℤ) * N 2 1 n = T 2 n - (if 2 ∣ n then (T 1 (n / 2) : ℤ) else 0) := by
  have h := main (m := 2) (by norm_num) 1 n
  rw [Nat.Prime.divisors Nat.prime_two] at h
  simp [ramanujanSum_one, ramanujanSum_two_one] at h
  rw [h]
  split_ifs <;> ring

/-- A389343 (`m = 3`, `r = 0`): generating function `(P(x)^3 + 2 P(x^3)) / 3`. -/
theorem A389343 (n : ℕ) :
    (3 : ℤ) * N 3 0 n = T 3 n + 2 * (if 3 ∣ n then (T 1 (n / 3) : ℤ) else 0) := by
  have h := main (m := 3) (by norm_num) 0 n
  rw [Nat.Prime.divisors Nat.prime_three] at h
  simp [ramanujanSum_one, ramanujanSum_three_zero] at h
  rw [h]
  split_ifs <;> ring

/-- A390208 (`m = 3`, `r = 1`): generating function `(P(x)^3 - P(x^3)) / 3`. -/
theorem A390208 (n : ℕ) :
    (3 : ℤ) * N 3 1 n = T 3 n - (if 3 ∣ n then (T 1 (n / 3) : ℤ) else 0) := by
  have h := main (m := 3) (by norm_num) 1 n
  rw [Nat.Prime.divisors Nat.prime_three] at h
  simp [ramanujanSum_one, ramanujanSum_three_one] at h
  rw [h]
  split_ifs <;> ring

/-- A390217 (`m = 4`, `r = 0`): generating function `(P(x)^4 + P(x^2)^2 + 2 P(x^4)) / 4`. -/
theorem A390217 (n : ℕ) :
    (4 : ℤ) * N 4 0 n = T 4 n + (if 2 ∣ n then (T 2 (n / 2) : ℤ) else 0) +
      2 * (if 4 ∣ n then (T 1 (n / 4) : ℤ) else 0) := by
  have h := main (m := 4) (by norm_num) 0 n
  rw [divisors_four] at h
  simp [ramanujanSum_one, ramanujanSum_two_zero, ramanujanSum_four_zero] at h
  rw [h]
  split_ifs <;> ring

/-- A387957 (`m = 4`, `r = 1`): generating function `(P(x)^4 - P(x^2)^2) / 4`. -/
theorem A387957 (n : ℕ) :
    (4 : ℤ) * N 4 1 n = T 4 n - (if 2 ∣ n then (T 2 (n / 2) : ℤ) else 0) := by
  have h := main (m := 4) (by norm_num) 1 n
  rw [divisors_four] at h
  simp [ramanujanSum_one, ramanujanSum_two_one, ramanujanSum_four_one] at h
  rw [h]
  split_ifs <;> ring

/-! ### Dependence on `r` -/

theorem ramanujanSum_gcd {d m : ℕ} (hdm : d ∣ m) (r : ℕ) :
    ramanujanSum d (Nat.gcd m r) = ramanujanSum d r := by
  rw [ramanujanSum, ramanujanSum, ← Nat.gcd_assoc, Nat.gcd_eq_left hdm]

/-- `N m r n` depends on `r` only through `gcd(m, r)`. -/
theorem N_eq_of_gcd_eq {m : ℕ} (hm : 0 < m) {r r' : ℕ} (h : Nat.gcd m r = Nat.gcd m r')
    (n : ℕ) : N m r n = N m r' n := by
  have key : (m : ℤ) * N m r n = m * N m r' n := by
    rw [main hm r n, main hm r' n]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdm := Nat.dvd_of_mem_divisors hd
    rw [← ramanujanSum_gcd hdm r, ← ramanujanSum_gcd hdm r', h]
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  exact_mod_cast mul_left_cancel₀ hm' key

/-- A390208 is also the case `m = 3`, `r = 2`. -/
theorem N_three_two (n : ℕ) : N 3 2 n = N 3 1 n :=
  N_eq_of_gcd_eq (by norm_num) (by decide) n

/-- A387957 is also the case `m = 4`, `r = 3`. -/
theorem N_four_three (n : ℕ) : N 4 3 n = N 4 1 n :=
  N_eq_of_gcd_eq (by norm_num) (by decide) n

/-! ### Kernel-checked data

The partition numbers `p(0), ..., p(9)` are the coefficients of the finite product
`prod_{i < 9} 1 / (1 - x^(i+1))` up to `x^9` (`X_pow_dvd_G_one_sub`). The coefficients of that
product are computed by a structural recursion (`pp`) that the kernel evaluates (`pp_nine`).
Then `T c n = Tv c n` for `n < 10` (`T_eq_Tv`), where `Tv c` is the `c`-fold convolution power
of the table of `p`, and the five corollaries give the values of `N`. -/

/-- Convolution of coefficient sequences. -/
def conv (f g : ℕ → ℕ) (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), f k * g (n - k)

theorem mk_mul_mk (f g : ℕ → ℕ) :
    PowerSeries.mk (fun n => (f n : ℂ)) * PowerSeries.mk (fun n => (g n : ℂ)) =
      PowerSeries.mk (fun n => (conv f g n : ℂ)) := by
  ext n
  rw [coeff_mul, coeff_mk, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (PowerSeries.mk (fun n => (f n : ℂ))) *
      coeff j (PowerSeries.mk (fun n => (g n : ℂ))))]
  simp [conv]

/-- The `c`-fold convolution power of a coefficient sequence. -/
def cpow (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => fun n => if n = 0 then 1 else 0
  | c + 1 => conv f (cpow f c)

theorem mk_cpow (f : ℕ → ℕ) (c : ℕ) :
    PowerSeries.mk (fun n => (cpow f c n : ℂ)) = PowerSeries.mk (fun n => (f n : ℂ)) ^ c := by
  induction c with
  | zero =>
    ext n
    simp [cpow, coeff_one]
  | succ c ih => rw [pow_succ', ← ih, mk_mul_mk]; rfl

/-- The coefficients of the Euler factor `1 / (1 - x^(i+1))`. -/
def geo (i k : ℕ) : ℕ := if (i + 1) ∣ k then 1 else 0

theorem mk_geo_mul (i : ℕ) :
    PowerSeries.mk (fun k => (geo i k : ℂ)) * (1 - X ^ (i + 1)) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_mk, coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [geo]
  · simp only [hn.ne', ↓reduceIte]
    split_ifs with h
    · rw [coeff_mk]
      have : (i + 1 ∣ n - (i + 1)) ↔ (i + 1 ∣ n) := by
        rw [Nat.dvd_sub_self_right]
        exact ⟨fun h' => h'.elim id fun hle => by rw [le_antisymm hle h], Or.inl⟩
      simp [geo, this]
    · have : ¬ (i + 1 ∣ n) := fun hd => h (Nat.le_of_dvd hn hd)
      simp [geo, this]

theorem eulerFactor_one_eq (i : ℕ) :
    eulerFactor 1 i = PowerSeries.mk (fun k => (geo i k : ℂ)) := by
  have h1 := eulerFactor_mul 1 i
  rw [map_one, one_mul] at h1
  have h2 := mk_geo_mul i
  calc eulerFactor 1 i
      = eulerFactor 1 i * (PowerSeries.mk (fun k => (geo i k : ℂ)) * (1 - X ^ (i + 1))) := by
        rw [h2, mul_one]
    _ = (eulerFactor 1 i * (1 - X ^ (i + 1))) * PowerSeries.mk (fun k => (geo i k : ℂ)) := by
        ring
    _ = PowerSeries.mk (fun k => (geo i k : ℂ)) := by rw [h1, one_mul]

/-- The coefficients of `prod_{i < K} 1 / (1 - x^(i+1))`. -/
def pp : ℕ → ℕ → ℕ
  | 0 => fun n => if n = 0 then 1 else 0
  | K + 1 => conv (pp K) (geo K)

theorem prod_eulerFactor_eq (K : ℕ) :
    ∏ i ∈ range K, eulerFactor 1 i = PowerSeries.mk (fun n => (pp K n : ℂ)) := by
  induction K with
  | zero =>
    ext n
    simp [pp, coeff_one]
  | succ K ih => rw [prod_range_succ, ih, eulerFactor_one_eq, mk_mul_mk]; rfl

theorem X_pow_dvd_prod_sub_one {N : ℕ} (s : Finset ℕ) (f : ℕ → ℂ⟦X⟧)
    (h : ∀ i ∈ s, (X : ℂ⟦X⟧) ^ N ∣ f i - 1) : (X : ℂ⟦X⟧) ^ N ∣ (∏ i ∈ s, f i) - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha]
    have e : f a * ∏ i ∈ s, f i - 1 = (f a - 1) * ∏ i ∈ s, f i + ((∏ i ∈ s, f i) - 1) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left (h a (mem_insert_self a s)) _)
      (ih fun i hi => h i (mem_insert_of_mem hi))

theorem X_pow_dvd_eulerFactor_sub_one (i : ℕ) :
    (X : ℂ⟦X⟧) ^ (i + 1) ∣ eulerFactor 1 i - 1 := by
  have h1 := eulerFactor_mul 1 i
  rw [map_one, one_mul] at h1
  refine ⟨eulerFactor 1 i, ?_⟩
  linear_combination h1

/-- The first `K + 1` coefficients of `G 1` are those of `prod_{i < K} 1 / (1 - x^(i+1))`. -/
theorem X_pow_dvd_G_one_sub (K : ℕ) :
    (X : ℂ⟦X⟧) ^ (K + 1) ∣ G 1 - ∏ i ∈ range K, eulerFactor 1 i := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, sub_eq_zero]
  have ht := ((WithPiTopology.continuous_coeff ℂ m).tendsto _).comp (hasProd_G 1)
  have hev : (fun s : Finset ℕ => coeff m (∏ i ∈ s, eulerFactor 1 i)) =ᶠ[Filter.atTop]
      fun _ => coeff m (∏ i ∈ range K, eulerFactor 1 i) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨range K, fun s hs => ?_⟩
    have hd : (X : ℂ⟦X⟧) ^ (K + 1) ∣
        ∏ i ∈ s, eulerFactor 1 i - ∏ i ∈ range K, eulerFactor 1 i := by
      rw [← prod_sdiff hs]
      have e : (∏ i ∈ s \ range K, eulerFactor 1 i) * ∏ i ∈ range K, eulerFactor 1 i -
          ∏ i ∈ range K, eulerFactor 1 i =
          ((∏ i ∈ s \ range K, eulerFactor 1 i) - 1) * ∏ i ∈ range K, eulerFactor 1 i := by ring
      rw [e]
      refine dvd_mul_of_dvd_left (X_pow_dvd_prod_sub_one _ _ fun i hi => ?_) _
      have hi' : K ≤ i := by simpa using (mem_sdiff.mp hi).2
      exact (pow_dvd_pow X (by omega)).trans (X_pow_dvd_eulerFactor_sub_one i)
    have := (X_pow_dvd_iff.mp hd) m hm
    rw [map_sub, sub_eq_zero] at this
    exact this
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' hev.symm)

/-- The partition numbers `p(0), ..., p(9)`. -/
def pTable : List ℕ := [1, 1, 2, 3, 5, 7, 11, 15, 22, 30]

/-- The kernel computes the coefficients of `prod_{i < 9} 1 / (1 - x^(i+1))` up to `x^9`. -/
theorem pp_nine : ∀ n < 10, pp 9 n = pTable.getD n 0 := by decide +kernel

theorem X_pow_dvd_G_one_sub_pTable :
    (X : ℂ⟦X⟧) ^ 10 ∣ G 1 - PowerSeries.mk (fun n => (pTable.getD n 0 : ℂ)) := by
  have h := X_pow_dvd_G_one_sub 9
  rw [prod_eulerFactor_eq] at h
  rw [X_pow_dvd_iff] at h ⊢
  intro m hm
  rw [← h m hm, map_sub, map_sub, coeff_mk, coeff_mk, pp_nine m hm]

/-- `T c n` for `n < 10`, computed from the partition numbers `p(0), ..., p(9)`. -/
def Tv (c n : ℕ) : ℕ := cpow (fun k => pTable.getD k 0) c n

/-- For `n < 10`, `T c n` is the `c`-fold convolution of `p(0), ..., p(9)`. -/
theorem T_eq_Tv (c : ℕ) {n : ℕ} (hn : n < 10) : T c n = Tv c n := by
  have hd := X_pow_dvd_iff.mp
    (X_pow_dvd_G_one_sub_pTable.trans (sub_dvd_pow_sub_pow _ _ c)) n hn
  rw [map_sub, sub_eq_zero, coeff_G_one_pow, ← mk_cpow, coeff_mk] at hd
  exact_mod_cast hd

theorem N_two_one_eq {n : ℕ} (hn : n < 10) :
    N 2 1 n = (Tv 2 n - if 2 ∣ n then Tv 1 (n / 2) else 0) / 2 := by
  have h := A392002 n
  rw [T_eq_Tv 2 hn, T_eq_Tv 1 (by omega : n / 2 < 10)] at h
  split_ifs at h ⊢ <;> omega

theorem N_three_zero_eq {n : ℕ} (hn : n < 10) :
    N 3 0 n = (Tv 3 n + 2 * if 3 ∣ n then Tv 1 (n / 3) else 0) / 3 := by
  have h := A389343 n
  rw [T_eq_Tv 3 hn, T_eq_Tv 1 (by omega : n / 3 < 10)] at h
  split_ifs at h ⊢ <;> omega

theorem N_three_one_eq {n : ℕ} (hn : n < 10) :
    N 3 1 n = (Tv 3 n - if 3 ∣ n then Tv 1 (n / 3) else 0) / 3 := by
  have h := A390208 n
  rw [T_eq_Tv 3 hn, T_eq_Tv 1 (by omega : n / 3 < 10)] at h
  split_ifs at h ⊢ <;> omega

theorem N_four_zero_eq {n : ℕ} (hn : n < 10) :
    N 4 0 n = (Tv 4 n + (if 2 ∣ n then Tv 2 (n / 2) else 0) +
      2 * if 4 ∣ n then Tv 1 (n / 4) else 0) / 4 := by
  have h := A390217 n
  rw [T_eq_Tv 4 hn, T_eq_Tv 2 (by omega : n / 2 < 10), T_eq_Tv 1 (by omega : n / 4 < 10)] at h
  split_ifs at h ⊢ <;> omega

theorem N_four_one_eq {n : ℕ} (hn : n < 10) :
    N 4 1 n = (Tv 4 n - if 2 ∣ n then Tv 2 (n / 2) else 0) / 4 := by
  have h := A387957 n
  rw [T_eq_Tv 4 hn, T_eq_Tv 2 (by omega : n / 2 < 10)] at h
  split_ifs at h ⊢ <;> omega

/-- The first ten terms of A392002, kernel-checked. -/
theorem A392002_data :
    (List.range 10).map (N 2 1) = [0, 1, 2, 5, 9, 18, 31, 55, 90, 150] := by
  rw [List.map_congr_left fun n hn => N_two_one_eq (List.mem_range.mp hn)]
  decide +kernel

/-- The first ten terms of A389343, kernel-checked. -/
theorem A389343_data :
    (List.range 10).map (N 3 0) = [1, 1, 3, 8, 17, 36, 75, 143, 270, 495] := by
  rw [List.map_congr_left fun n hn => N_three_zero_eq (List.mem_range.mp hn)]
  decide +kernel

/-- The first ten terms of A390208, kernel-checked. -/
theorem A390208_data :
    (List.range 10).map (N 3 1) = [0, 1, 3, 7, 17, 36, 73, 143, 270, 492] := by
  rw [List.map_congr_left fun n hn => N_three_one_eq (List.mem_range.mp hn)]
  decide +kernel

/-- The first ten terms of A390217, kernel-checked. -/
theorem A390217_data :
    (List.range 10).map (N 4 0) = [1, 1, 4, 10, 28, 63, 146, 310, 651, 1295] := by
  rw [List.map_congr_left fun n hn => N_four_zero_eq (List.mem_range.mp hn)]
  decide +kernel

/-- The first ten terms of A387957, kernel-checked. -/
theorem A387957_data :
    (List.range 10).map (N 4 1) = [0, 1, 3, 10, 25, 63, 141, 310, 640, 1295] := by
  rw [List.map_congr_left fun n hn => N_four_one_eq (List.mem_range.mp hn)]
  decide +kernel

end OeisProofs.ColoredPartitions
