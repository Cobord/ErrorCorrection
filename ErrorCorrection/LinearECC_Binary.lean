/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import ErrorCorrection.LinearECC
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

/-!
# Linear Error Correcting Codes specifically over F2

- Hadammard
- Hamming

-/


section Binary

variable {n k : ℕ}
public abbrev F2 := ZMod 2

public abbrev BitString n := Fqn (n:=n) (Fq:=F2)

public abbrev BinaryLinearCode := LinearECC (n:=n) (k:=k) (Fq:=F2)

public def hammingWeightBinary := hammingWeightLinear (n:=n) (Fq:=F2)

private lemma f2vec_add_self {r : ℕ} (v : Fin r → F2) : v + v = 0 := by
  rw [(two_smul F2 v).symm, zmod2_two_eq_zero, zero_smul]

private lemma f2vec_eq_of_add_eq_zero {r : ℕ} {u v : Fin r → F2} (h : u + v = 0) : u = v :=
  add_right_cancel (h.trans (f2vec_add_self v).symm)

section HadammardCode

open Matrix

private lemma dot_apply {n : ℕ} (x y : Fqn (n:=n) (Fq:=F2)) :
    dot x y = ∑ i, x i * y i := by
  simp [dot, Matrix.toBilin'_apply', Matrix.one_mulVec, dotProduct]

private lemma dot_add_left {n : ℕ} (v w x : Fqn (n:=n) (Fq:=F2)) :
    dot (v + w) x = dot v x + dot w x := by
  simp only [dot_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma dot_add_right {n : ℕ} (v x y : Fqn (n:=n) (Fq:=F2)) :
    dot v (x + y) = dot v x + dot v y := by
  simp only [dot_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma dot_indicator {n : ℕ} (v : Fqn (n:=n) (Fq:=F2)) (i : Fin n) :
    dot v (indicator i) = v i := by
  rw [dot_apply]
  unfold indicator
  simp

/-- The sign character `F2 → ℤ`: `0 ↦ 1`, `1 ↦ -1`.
This is a group homomorphism from
`(F2, +)` to `(ℤ, *)`,
The Sylvester-type Hadamard matrices have entries
in `± 1` of the image. -/
private def sign (a : F2) : ℤ := if a = 0 then 1 else -1

private lemma sign_add (a b : F2) : sign (a + b) = sign a * sign b := by
  revert a b; decide

private lemma sign_mem_unitary (a : F2) : sign a ∈ unitary ℤ := by
  rw [Unitary.mem_iff_eq_one_or_eq_neg_one]
  unfold sign
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Convert an integer Hadamard-matrix entry
to its `F2` bit: `1 ↦ 0`, `-1 ↦ 1`. -/
public def hadamardBit (x : ℤ) : F2 := if x = 1 then 0 else 1

private lemma hadamardBit_sign (a : F2) : hadamardBit (sign a) = a := by
  rcases zmod2_eq_zero_or_one a with h | h <;> simp [hadamardBit, sign, h]

/-- The row of `A` at index `i`
converted to its `F2` bit pattern. -/
public def hadamardRow {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (i : Fin m) :
    BitString m := fun j => hadamardBit (A i j)

/-
/-- Any integer Hadamard matrix `A`
gives a binary linear code.
The `F2`-span of the bit patterns of its rows.
`Submodule.span` is automatically a submodule, so this is a
`LinearECC` for *any* `A` satisfying `A.IsHadamard`, with `k` simply defined as the
dimension of the resulting span.
The actual `A` will have to be of Sylvester type, but not yet.
The rank is whatever it turns out to be. Could be the full
space and so the code does not correct anything!
-/
public noncomputable def HadamardCode {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (_hA : A.IsHadamard) :
    LinearECC (n:=m)
      (k := Module.finrank F2 (Submodule.span F2 (Set.range (hadamardRow A))))
      (Fq:=F2) where
  subspace := Submodule.span F2 (Set.range (hadamardRow A))
  rank_k := rfl
-/

/-- The identification of
`Fin (2^r)` with `F2`-vectors of length `r`
used to index the `2^r` dimensional Sylvester-type Hadamard matrix
by characters of `F2 ^ r`. -/
private noncomputable def finEquivF2Pow (r : ℕ) : Fin (2^r) ≃ (Fin r → F2) :=
  (Fintype.equivFinOfCardEq (α := Fin r → F2) (by simp)).symm

/-- Translation by a fixed `F2`-vector `c`
It is an involutive equivalence since `c + c = 0`. -/
private def shiftEquiv {r : ℕ} (c : Fin r → F2) : (Fin r → F2) ≃ (Fin r → F2) where
  toFun x := x + c
  invFun x := x + c
  left_inv x := by simp; rw [add_assoc, f2vec_add_self, add_zero]
  right_inv x := by simp; rw [add_assoc, f2vec_add_self, add_zero]

/-- The Sylvester-type Hadamard matrix of order `2^r`
Its `(v, x)` entry is the value
`(-1)^⟨v,x⟩` of the additive `F2`-character `x ↦ ⟨v,x⟩`
transported to `Fin (2^r)` indices via `finEquivF2Pow`. -/
public noncomputable def SylvesterType (r : ℕ) : Matrix (Fin (2^r)) (Fin (2^r)) ℤ :=
  fun i j => sign (dot (finEquivF2Pow r i) (finEquivF2Pow r j))

/-- The sum of a nontrivial `F2`-character over
all of `F2 ^ r` vanishes
The sum of the trivial character is `2^r`. -/
private lemma sum_sign_dot {r : ℕ} (u : Fin r → F2) :
    ∑ x : Fin r → F2, sign (dot u x) = if u = 0 then (2:ℤ) ^ r else 0 := by
  by_cases hu : u = 0
  · have hzero : ∀ x : Fin r → F2, dot u x = 0 := by
      intro x; rw [hu, dot_apply]; simp
    have hcard : Fintype.card (Fin r → F2) = 2 ^ r := by simp
    simp only [sign, hu, ite_true]
    simp
  · obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (funext h)
    have hui : u i = 1 := (zmod2_eq_zero_or_one (u i)).resolve_left hi
    have hexpand : ∀ x : Fin r → F2, sign (dot u (shiftEquiv (indicator i) x))
        = -sign (dot u x) := by
      intro x
      have hshiftx : shiftEquiv (indicator i) x = x + indicator i := rfl
      rw [hshiftx, dot_add_right, sign_add, dot_indicator, hui]
      unfold sign
      split <;> ring_nf <;> simp
    have hshift : ∑ x : Fin r → F2, sign (dot u x)
        = ∑ x : Fin r → F2, -sign (dot u x) := by
      calc ∑ x : Fin r → F2, sign (dot u x)
          = ∑ x : Fin r → F2, sign (dot u (shiftEquiv (indicator i) x)) :=
            (Equiv.sum_comp (shiftEquiv (indicator i)) (fun x => sign (dot u x))).symm
        _ = ∑ x : Fin r → F2, -sign (dot u x) := by simp only [hexpand]
    rw [Finset.sum_neg_distrib] at hshift
    have hzero : (∑ x : Fin r → F2, sign (dot u x)) = 0 := by omega
    rw [ite_eq_right hu]
    exact hzero

/-- The Sylvester-type Hadamard matrix
satisfies Mathlib's `Matrix.IsHadamard`.
Its entries are `±1` and its rows are pairwise orthogonal -/
public lemma SylvesterType_isHadamard (r : ℕ) : (SylvesterType r).IsHadamard := by
  have hsymm : (SylvesterType r)ᴴ = SylvesterType r := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, SylvesterType]
    rw [dot_symm]
  have hmain : SylvesterType r * SylvesterType r
      = (Fintype.card (Fin (2^r)) : ℤ) • (1 : Matrix (Fin (2^r)) (Fin (2^r)) ℤ) := by
    ext i k
    simp only [Matrix.mul_apply, SylvesterType, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    have hstep : ∀ j : Fin (2^r),
        sign (dot (finEquivF2Pow r i) (finEquivF2Pow r j))
          * sign (dot (finEquivF2Pow r j) (finEquivF2Pow r k))
        = sign (dot (finEquivF2Pow r i + finEquivF2Pow r k) (finEquivF2Pow r j)) := by
      intro j
      rw [dot_symm (finEquivF2Pow r j) (finEquivF2Pow r k), dot_add_left, sign_add]
    simp only [hstep]
    rw [Equiv.sum_comp (finEquivF2Pow r)
      (fun x => sign (dot (finEquivF2Pow r i + finEquivF2Pow r k) x)), sum_sign_dot,
      Fintype.card_fin]
    by_cases hik : i = k
    · subst hik
      simp [f2vec_add_self]
    · have hne0 : finEquivF2Pow r i + finEquivF2Pow r k ≠ 0 := fun h =>
        hik ((finEquivF2Pow r).injective (f2vec_eq_of_add_eq_zero h))
      simp [hne0, hik]
  refine ⟨fun i j => sign_mem_unitary _, ?_, ?_⟩
  · rw [hsymm]; exact hmain
  · rw [hsymm]; exact hmain

/--
The linear map `v ↦ (x ↦ ⟨v,x⟩)`
sending an `F2`-linear functional on `F2 ^ r`  to
its truth table indexed by `Fin (2^r)` via `finEquivF2Pow`.
Its range is exactly the span of the bit-rows of `SylvesterType r`.
It is injective which together give both the rank (`SylvesterType_HadamardCode_finrank`)
and the minimum distance (`hadamardΦ_weight`) of the resulting Hadamard code. -/
private noncomputable def hadamardΦ (r : ℕ) : (Fin r → F2) →ₗ[F2] Fqn (n:=2^r) (Fq:=F2) :=
  { toFun := fun v => fun j => dot v (finEquivF2Pow r j)
    map_add' := fun v w => funext fun j => dot_add_left v w _
    map_smul' := fun c v => funext fun j => by simp }

private lemma hadamardΦ_apply (r : ℕ) (v : Fin r → F2) (j : Fin (2^r)) :
    hadamardΦ r v j = dot v (finEquivF2Pow r j) := rfl

private lemma hadamardRow_eq_range (r : ℕ) :
    Submodule.span F2 (Set.range (hadamardRow (SylvesterType r))) = LinearMap.range (hadamardΦ r) := by
  have hrow : ∀ i : Fin (2^r), hadamardRow (SylvesterType r) i
      = fun j => dot (finEquivF2Pow r i) (finEquivF2Pow r j) := by
    intro i
    funext j
    exact hadamardBit_sign _
  have hset : Set.range (hadamardRow (SylvesterType r)) = Set.range (hadamardΦ r) := by
    apply Set.eq_of_subset_of_subset
    · rintro _ ⟨i, rfl⟩
      exact ⟨finEquivF2Pow r i, (hrow i).symm⟩
    · rintro _ ⟨v, rfl⟩
      refine ⟨(finEquivF2Pow r).symm v, ?_⟩
      rw [hrow]
      funext j
      rw [hadamardΦ_apply, Equiv.apply_symm_apply]
  rw [hset]
  exact Submodule.span_eq (LinearMap.range (hadamardΦ r))

private lemma hadamardΦ_injective (r : ℕ) : Function.Injective (hadamardΦ r) := by
  intro v w hvw
  funext i
  have hv : dot v (indicator i) = dot w (indicator i) := by
    have h := congrFun hvw ((finEquivF2Pow r).symm (indicator i))
    rw [hadamardΦ_apply, hadamardΦ_apply, Equiv.apply_symm_apply] at h
    exact h
  rwa [dot_indicator, dot_indicator] at hv

/-- The `HadamardCode` of the Sylvester-type matrix
has dimension exactly `r` -/
public lemma SylvesterType_HadamardCode_finrank (r : ℕ) :
    Module.finrank F2 (Submodule.span F2 (Set.range (hadamardRow (SylvesterType r)))) = r := by
  rw [hadamardRow_eq_range]
  have := (LinearEquiv.ofInjective (hadamardΦ r) (hadamardΦ_injective r)).finrank_eq
  have hdom : Module.finrank F2 (Fin r → F2) = r := by simp
  rw [hdom] at this
  exact this.symm

/--The Hadamard codespace is an `r` dimensional subspace of the `F2^(2^r)` -/
public noncomputable def HadammardCode (r : ℕ) : LinearECC (n:=2^r) (k:=r) (Fq:=F2) where
  subspace := Submodule.span F2 (Set.range (hadamardRow (SylvesterType r)))
  rank_k := by
    exact SylvesterType_HadamardCode_finrank r

private lemma HadammardCode_subspace_eq_range (r : ℕ) :
    (HadammardCode r).subspace = LinearMap.range (hadamardΦ r) :=
  hadamardRow_eq_range r

private lemma r_pos_of_v_ne_zero {r : ℕ} {v : Fin r → F2} (hv : v ≠ 0) : 0 < r := by
  by_contra h
  push Not at h
  have hr0 : r = 0 := Nat.le_zero.mp h
  subst hr0
  exact hv (funext fun i => i.elim0)

/-- Every nonzero codeword of the Hadamard code
has the same weight `2 ^ (r-1)`. -/
private lemma hadamardΦ_weight (r : ℕ) {v : Fin r → F2} (hv : v ≠ 0) :
    hammingWeightFqn (hadamardΦ r v) = 2 ^ (r - 1) := by
  have hr := r_pos_of_v_ne_zero hv
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hvi : v i = 1 := (zmod2_eq_zero_or_one (v i)).resolve_left hi
  have hflip : ∀ x : Fin r → F2,
      dot v x = 0 ↔ dot v (shiftEquiv (indicator i) x) ≠ 0 := by
    intro x
    have hstep : dot v (shiftEquiv (indicator i) x) = dot v x + 1 := by
      have hshiftx : shiftEquiv (indicator i) x = x + indicator i := rfl
      rw [hshiftx, dot_add_right, dot_indicator, hvi]
    rw [hstep]
    rcases zmod2_eq_zero_or_one (dot v x) with h | h <;> rw [h] <;> decide
  have hcardEq : Fintype.card {x : Fin r → F2 // dot v x = 0}
      = Fintype.card {x : Fin r → F2 // dot v x ≠ 0} :=
    Fintype.card_congr (Equiv.subtypeEquiv (shiftEquiv (indicator i)) hflip)
  have htot : Fintype.card {x : Fin r → F2 // dot v x = 0}
      + Fintype.card {x : Fin r → F2 // dot v x ≠ 0} = 2 ^ r := by
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter_add_card_filter_not,
      Finset.card_univ]
    simp
  have h2r : (2 : ℕ) ^ r = 2 * 2 ^ (r - 1) := by
    cases r with
    | zero => exact absurd hr (lt_irrefl 0)
    | succ m => rw [Nat.succ_sub_one, pow_succ, mul_comm]
  have hweight : Fintype.card {x : Fin r → F2 // dot v x ≠ 0} = 2 ^ (r - 1) := by omega
  have hreindex : Fintype.card {j : Fin (2^r) // hadamardΦ r v j ≠ 0}
      = Fintype.card {x : Fin r → F2 // dot v x ≠ 0} :=
    Fintype.card_congr (Equiv.subtypeEquiv (finEquivF2Pow r)
      (fun j => by rw [hadamardΦ_apply]))
  calc hammingWeightFqn (hadamardΦ r v)
      = (Finset.univ.filter (fun j : Fin (2^r) => hadamardΦ r v j ≠ 0)).card := rfl
    _ = Fintype.card {j : Fin (2^r) // hadamardΦ r v j ≠ 0} := (Fintype.card_subtype _).symm
    _ = Fintype.card {x : Fin r → F2 // dot v x ≠ 0} := hreindex
    _ = 2 ^ (r - 1) := hweight

/-- The Hadamard code,
bundled with a proof that its minimum distance
is at least `2 ^ (r-1)` -/
public noncomputable def HadammardCodenk_weakd (r : ℕ) (_hr : 0 < r) :
    LinearECCnk_weakd (n:=2^r) (k:=r) (Fq:=F2) (2 ^ (r - 1)) where
  toLinearECC := HadammardCode r
  distance_d := by
    intro x hx hx0
    rw [HadammardCode_subspace_eq_range] at hx
    obtain ⟨v, rfl⟩ := hx
    have hv : v ≠ 0 := fun h => hx0 (by rw [h, map_zero])
    exact (hadamardΦ_weight r hv).ge

/-- The Hadamard code,
bundled with a proof that its minimum distance
is exactly `2 ^ (r-1)` -/
public noncomputable def HadammardCodenkd (r : ℕ) (hr : 0 < r) :
    LinearECCnkd (n:=2^r) (k:=r) (Fq:=F2) (2 ^ (r - 1)) where
  toLinearECCnk_weakd := HadammardCodenk_weakd r hr
  distance_d_strict := by
    show sInf ((fun x => hammingDistFqn x 0) '' {x ∈ (HadammardCode r).subspace | x ≠ 0})
      = 2 ^ (r - 1)
    have himg : (fun x => hammingDistFqn x 0) '' {x ∈ (HadammardCode r).subspace | x ≠ 0}
        = {2 ^ (r - 1)} := by
      apply Set.eq_singleton_iff_unique_mem.mpr
      constructor
      · obtain ⟨i⟩ : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
        have hv : (indicator i : Fin r → F2) ≠ 0 := by
          intro h
          have := congrFun h i
          simp [indicator] at this
        refine ⟨hadamardΦ r (indicator i), ⟨?_, ?_⟩, ?_⟩
        · rw [HadammardCode_subspace_eq_range]
          exact ⟨indicator i, rfl⟩
        · exact fun h0 => hv (hadamardΦ_injective r (h0.trans (map_zero (hadamardΦ r)).symm))
        · exact hadamardΦ_weight r hv
      · rintro y ⟨x, ⟨hxmem, hx0⟩, hxeq⟩
        rw [HadammardCode_subspace_eq_range] at hxmem
        obtain ⟨v, rfl⟩ := hxmem
        have hv : v ≠ 0 := fun h => hx0 (by rw [h, map_zero])
        rw [← hxeq]
        exact hadamardΦ_weight r hv
    rw [himg]
    exact csInf_singleton _

end HadammardCode

section HammingCode

/-- Nonzero vectors of `Fin r → F2`
are in bijection with `Fin (2^r - 1)` -/
noncomputable def parityIndex (r : ℕ) :
  Fin (2^r - 1) ≃ {v : Fin r → F2 // v ≠ 0} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_subtype_compl (fun v : Fin r → F2 => v = 0),
      Fintype.card_subtype_eq, Fintype.card_fun, ZMod.card, Fintype.card_fin])

/-- The parity check map of the Hamming code.
It sends a codeword to the sum of the
(nonzero) syndrome vectors at its support,
indexed via `parityIndex`. -/
noncomputable def parityCheck (r : ℕ) :
  Fqn (n:=2^r-1) (Fq:=F2) →ₗ[F2] (Fin r → F2) :=
  Fintype.linearCombination F2 (fun i => (parityIndex r i).val)

/-- The Hamming code `[2^r - 1, 2^r - r - 1, 3]_2`
given as the kernel of the
parity check map whose columns
run over all nonzero vectors of `Fin r → F2`.
The `3` distance is not present yet. -/
public noncomputable def HammingCode (r : ℕ) : LinearECC (n:=2^r-1) (k:=2^r-r-1) (Fq:=F2) where
  subspace := LinearMap.ker (parityCheck r)
  rank_k := by
    have hspan : Submodule.span F2 (Set.range (fun i => (parityIndex r i).val))
        = (⊤ : Submodule F2 (Fin r → F2)) := by
      apply Submodule.eq_top_iff'.mpr
      intro v
      by_cases hv : v = 0
      · simp [hv]
      · exact Submodule.subset_span ⟨(parityIndex r).symm ⟨v, hv⟩, by simp⟩
    have hrange : LinearMap.range (parityCheck r) = ⊤ := by
      unfold parityCheck
      rw [Fintype.range_linearCombination]
      exact hspan
    have hd : Module.finrank F2 (Fqn (n:=2^r-1) (Fq:=F2)) = 2^r - 1 := by
      simp
    have hrr : Module.finrank F2 (Fin r → F2) = r := by
      simp
    have hrn := LinearMap.finrank_range_add_finrank_ker (parityCheck r)
    rw [hrange, finrank_top, hrr, hd] at hrn
    have := r.lt_two_pow_self
    omega

private lemma parityCheck_apply_indicator (r : ℕ) (i : Fin (2^r-1)) :
    parityCheck r (indicator i) = (parityIndex r i).val := by
  unfold parityCheck indicator
  rw [Fintype.linearCombination_apply]
  simp

private lemma parityCheck_apply_support (r : ℕ) (x : Fqn (n:=2^r-1) (Fq:=F2)) :
    parityCheck r x
      = ∑ i ∈ Finset.univ.filter (fun i => x i ≠ 0), (parityIndex r i).val := by
  unfold parityCheck
  rw [Fintype.linearCombination_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rcases zmod2_eq_zero_or_one (x i) with h0 | h1
  · simp [h0]
  · simp [h1]

/-- No nonzero codeword of the Hamming code
has weight `< 3` -/
private lemma HammingCode_weight_ge_three (r : ℕ)
    (x : Fqn (n:=2^r-1) (Fq:=F2)) (hx : x ∈ (HammingCode r).subspace) (hx0 : x ≠ 0) :
    3 ≤ hammingWeightFqn x := by
  have hxker : parityCheck r x = 0 := LinearMap.mem_ker.mp hx
  rw [parityCheck_apply_support] at hxker
  set S := Finset.univ.filter (fun i => x i ≠ 0) with hS
  have hcard : hammingWeightFqn x = S.card := rfl
  rw [hcard]
  have htri : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ 3 ≤ S.card := by omega
  rcases htri with hc | hc | hc | hc
  · exact absurd (funext fun i => by
      have : i ∉ S := by rw [Finset.card_eq_zero.mp hc]; exact Finset.notMem_empty i
      simpa [hS] using this) hx0
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    rw [ha, Finset.sum_singleton] at hxker
    exact absurd hxker (parityIndex r a).2
  · obtain ⟨a, b, hab, hS2⟩ := Finset.card_eq_two.mp hc
    rw [hS2, Finset.sum_pair hab] at hxker
    exact absurd ((parityIndex r).injective
      (Subtype.ext (f2vec_eq_of_add_eq_zero hxker))) hab
  · exact hc

/-- The Hamming code `[2^r - 1, 2^r - r - 1, 3]_2`
The `3` distance is not as an exact distance yet.
It is merely a lower bound for the moment. -/
public noncomputable def HammingCodenk_weakd (r : ℕ) :
  LinearECCnk_weakd (n:=2^r-1) (k:=2^r-r-1) (Fq:=F2) 3 where
  toLinearECC := HammingCode r
  distance_d := HammingCode_weight_ge_three r

end HammingCode

end Binary
