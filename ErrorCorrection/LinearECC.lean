/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Linear Error Correcting Codes

Linear Error Correcting Codes are given
as `k` dimensional subspaces of `F_q^n`.
They are denoted `[n,k,d]_q` for the
- dimension of the ambient subspace
- dimension of the code subspace
- minimal Hamming distance between two codewords

-/

@[expose] public section

open Finset Function

section Utilities

/-- Every element of `ZMod 2` is `0` or `1`. -/
public lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

/-- `2 = 0` in `ZMod 2`. -/
public lemma zmod2_two_eq_zero : (2 : ZMod 2) = 0 := by decide

end Utilities

section CodeWords

variable {n k : ℕ}
variable {Fq : Type*} [Field Fq] [DecidableEq Fq]

public abbrev Fqn := ∀ (_i : Fin n), Fq

public def indicator (i : Fin n) : Fqn (n:=n) (Fq:=Fq) :=
  fun j => if i=j then 1 else 0

/-- The identification of `Fqn` with its own dual.
It is induced by the standard basis. -/
public noncomputable def dualEquiv : Fqn (n:=n) (Fq:=Fq) ≃ₗ[Fq] Module.Dual Fq (Fqn (n:=n) (Fq:=Fq)) :=
  (Pi.basisFun Fq (Fin n)).toDualEquiv

/-- The Hamming distance function on `F_q^n`. -/
public def hammingDistFqn
  (x y : Fqn (n:=n) (Fq:=Fq)) : ℕ := hammingDist x y

/-- The Hamming weight function on `F_q^n`. -/
public def hammingWeightFqn
  (x : Fqn (n:=n) (Fq:=Fq)) : ℕ := hammingDist x 0

/--
Because the alphabet has the structure of a ring in
this case, subtraction is possible
unlike the general set case.
`hammingDist(x,y) = hammingDist(0,y-x)`-/
public lemma hammingDistFqnLinear
  (x y : Fqn (n:=n) (Fq:=Fq)) :
  hammingDist x y = hammingDist 0 (y-x) := by
  simp
  unfold hammingNorm
  have diff_eq0 (i : Fin n) : (y-x) i = 0 <-> x i = y i := by
    rw [Pi.sub_apply]
    apply Iff.intro
    · intro diff
      have key := sub_eq_zero.mp diff
      exact key.symm
    · intro xyeq
      rw [xyeq]
      abel
  have diff_neq0 (i : Fin n) : (y-x) i ≠ 0 <-> x i ≠ y i := by
    apply Iff.intro
    · contrapose
      exact (diff_eq0 i).mpr
    · contrapose
      exact (diff_eq0 i).mp
  simp_rw [diff_neq0]
  unfold hammingDist
  rfl

/-- The Hamming weight of the indicator vector is 1. -/
public lemma hammingWeightIndicator (i : Fin n) :
  hammingWeightFqn (indicator i : Fqn (n:=n) (Fq:=Fq)) = 1 := by
  unfold hammingWeightFqn
  rw [hammingDist_zero_right]
  unfold hammingNorm
  rw [Finset.card_eq_one_iff_existsUnique]
  refine ⟨i, ?i_inset, ?noti_notinset⟩
  · simp [indicator]
  · intro j hj
    simp only [indicator] at hj
    by_contra hji
    simp at hj
    exact hji hj.symm

/-- In the case that `Fq ≅ ℤ/2ℤ`,
the residue of the hamming weight
as the composite `(ℤ/2ℤ)^n -> ℕ → ℤ/2ℤ`
is a `ℤ/2ℤ`-linear map. -/
public def hammingWeightLinear
  (hq : Fq ≃+* ZMod 2) :
  Fqn (n:=n) (Fq:=Fq) →ₗ[Fq] Fq :=
  have hsum : ∀ z : Fqn (n:=n) (Fq:=Fq), (↑(hammingWeightFqn z) : Fq) = ∑ i, z i := by
    intro z
    unfold hammingWeightFqn
    rw [hammingDist_zero_right]
    unfold hammingNorm
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    have ha : ∀ a : Fq, a = 0 ∨ a = 1 := by
      intro a
      rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) (hq a) with h | h
      · exact Or.inl (hq.injective (by rw [h, map_zero]))
      · exact Or.inr (hq.injective (by rw [h, map_one]))
    rcases ha (z i) with hz | hz <;> simp [hz]
  {
    toFun := fun x => hammingWeightFqn x
    map_add' := fun x y => by
      repeat rw [hsum]
      simp [Finset.sum_add_distrib]
    map_smul' := fun c x => by
      repeat rw [hsum]
      simp [Finset.mul_sum]
  }


/-- The dot product of two code words,
valued in `Fq`. -/
public def dot : LinearMap.BilinForm Fq (Fqn (n:=n) (Fq:=Fq)) :=
  Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) Fq)

omit [DecidableEq Fq] in
/-- That dot product is symmetric in it's arguments. -/
public lemma dot_symm
  (x y : Fqn (n:=n) (Fq:=Fq)) :
  dot x y = dot y x := by
  unfold dot
  repeat rw [Matrix.toBilin'_apply]
  congr 1
  ext i
  congr 1
  ext j
  rw [Matrix.one_apply]
  by_cases hij : i=j
  · simp [hij]
    rw [mul_comm]
  · simp [hij]

omit [DecidableEq Fq] in
/-- If the dot product is 0, then
the second argument is in the kernel of the
linear map `dot(x,-)` which is the `dualEquiv`
of `x`. -/
public lemma dot_kernel (x y : Fqn (n:=n) (Fq:=Fq)) :
  dot x y = 0 <->
    y ∈ ((dualEquiv (n:=n) (Fq:=Fq)) x).ker := by
  conv_rhs =>
    rw [LinearMap.mem_ker]
    unfold dualEquiv
    simp [Module.Basis.toDualEquiv_apply]
    simp [Module.Basis.toDual, Pi.basisFun]
  conv_lhs =>
    simp [dot, Matrix.toBilin'_apply']
    change (∑ i : Fin n, x i * y i) = 0

omit [DecidableEq Fq] in
public lemma dot_eq :
  dot = (Pi.basisFun Fq (Fin n)).toDual := by
  apply (Pi.basisFun Fq (Fin n)).ext
  intro i
  apply (Pi.basisFun Fq (Fin n)).ext
  intro j
  rw [Module.Basis.toDual_apply]
  rw [Pi.basisFun_apply _ _ i]
  rw [Pi.basisFun_apply _ _ j]
  simp [dot]
  by_cases hij : i=j
  · rw [hij]
    simp
  · simp [hij]

omit [DecidableEq Fq] in
/-- The pairing of a subspace `sub` and
its orthogonal complement always gives 0.
The orthogonal complement is obtained
by taking the annihilator of `sub`
as a subspace of `Fqn^∨` and then
identifying that with a subspace
of `Fqn`. -/
public lemma dualDot
  {sub : Submodule Fq (Fqn (n:=n) (Fq:=Fq))}
  (x : sub)
  (y : sub.dualAnnihilator.map (dualEquiv (n:=n) (Fq:=Fq)).symm.toLinearMap) :
  dot y.val x.val = (0 : Fq) := by
  let b := Pi.basisFun Fq (Fin n)
  rcases y.2 with ⟨φ, hφ1, hφ2⟩
  have hφx : φ x = 0 :=
    (Submodule.mem_dualAnnihilator φ).1 hφ1 x.1 x.2
  rw [dot_eq]
  have key : ((Pi.basisFun Fq (Fin n)).toDual ↑y) = φ := by
    rw [<-hφ2]
    unfold dualEquiv
    simp
    rw [← Module.Basis.toDualEquiv_apply, LinearEquiv.apply_symm_apply]
  rw [key]
  exact hφx

omit [DecidableEq Fq] in
/-- The pairing of a subspace `sub` and
its orthogonal complement always gives 0.
The orthogonal complement is obtained
by taking the annihilator of `sub`
as a subspace of `Fqn^∨` and then
identifying that with a subspace
of `Fqn`. -/
public lemma dualDot_rev
  {sub : Submodule Fq (Fqn (n:=n) (Fq:=Fq))}
  (x : sub)
  (y : sub.dualAnnihilator.map (dualEquiv (n:=n) (Fq:=Fq)).symm.toLinearMap) :
  dot x.val y.val = (0 : Fq) := by
  rw [dot_symm]
  exact dualDot (n:=n) x y

end CodeWords

section GeneralDefinition

variable {n k : ℕ}
variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-- A linear error correcting code `L`
is described by a subspace of code words. -/
public structure LinearECC where
  subspace : Submodule Fq (Fqn (n:=n) (Fq:=Fq))
  rank_k : Module.finrank Fq subspace = k

namespace LinearECC

variable (l : LinearECC (n:=n) (k:=k) (Fq:=Fq))

/-- `L` is *even*:
every codeword has weight divisible by `2`. -/
public def IsEven : Prop :=
  ∀ v ∈ l.subspace, 2 ∣ hammingWeightFqn v

/-- `L` is *doubly even*:
every codeword has weight divisible by `4`. -/
public def IsDoublyEven : Prop :=
  ∀ v ∈ l.subspace, 4 ∣ hammingWeightFqn v

omit [Fintype Fq] in
/-- Doubly Even implies Even -/
public lemma IsDoublyEven.isEven (h : l.IsDoublyEven) : l.IsEven :=
  fun v hv => (by norm_num : (2 : ℕ) ∣ 4).trans (h v hv)

/-- The distance of a code is the minimal
hamming distance between any two codewords. -/
public noncomputable def distance : ℕ :=
  sInf ((fun x => hammingDistFqn x 0) '' {x ∈ l.subspace | x ≠ 0})

/-- The dual code,
i.e. the orthogonal complement of `l.subspace`
under the standard bilinear form `⟨x, y⟩ = ∑ i, x i * y i`.
It is obtained by transporting the
`dualAnnihilator` of `l.subspace` back along the equivalence `Fqn ≃ Dual Fq Fqn`
induced by the standard basis. -/
public noncomputable def dualCode : LinearECC (n:=n) (k:=n-k) (Fq:=Fq) where
  subspace :=
    l.subspace.dualAnnihilator.map (dualEquiv (n:=n) (Fq:=Fq)).symm.toLinearMap
  rank_k := by
    have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq l.subspace
    have h2 := LinearEquiv.finrank_map_eq
      (dualEquiv (n:=n) (Fq:=Fq)).symm l.subspace.dualAnnihilator
    have h3 : Module.finrank Fq (Fqn (n:=n) (Fq:=Fq)) = n := by
      simp [Module.finrank_pi Fq (ι := Fin n)]
    rw [l.rank_k] at h1
    omega

omit [Fintype Fq] [DecidableEq Fq] in
/-- The dot product between anything in `L` and it's dual code
is always 0. -/
public lemma dualCodeDot
  (x : l.subspace)
  (y : l.dualCode.subspace) :
  dot y.val x.val = (0 : Fq) := by
  exact dualDot (sub:=l.subspace) x y

/-- Appends a parity-check coordinate to a codeword
equal to minus the sum of the other entries.
This makes the sum of all `n+1` entries is `0`.
It is given as a linear map to one more dimension. -/
noncomputable def extendMap :
  Fqn (n:=n) (Fq:=Fq) →ₗ[Fq] Fqn (n:=n+1) (Fq:=Fq) :=
  LinearMap.pi (Fin.snoc (fun i => LinearMap.proj i) (-∑ i, LinearMap.proj i))

omit [Fintype Fq] [DecidableEq Fq] in
/-- The first `n` entries after `extendMap` are the same
as the previous entries. -/
private lemma extendMap_apply_castSucc (x : Fqn (n:=n) (Fq:=Fq)) (i : Fin n) :
    extendMap x i.castSucc = x i := by
  simp [extendMap, LinearMap.pi_apply]

omit [Fintype Fq] [DecidableEq Fq] in
/-- The linear `extendMap` is injective.
That is clear from preserving the
input in it's first `n` entries. -/
private lemma extendMap_injective : Function.Injective (extendMap (n:=n) (Fq:=Fq)) := by
  intro x y h
  funext i
  rw [← extendMap_apply_castSucc x i, ← extendMap_apply_castSucc y i, h]

omit [Fintype Fq] in
/-- Extending never decreases weight:
the first `n` coordinates of `extendMap x` are
exactly `x`, so its support is at least as large. -/
private lemma hammingWeightFqn_extendMap_ge (x : Fqn (n:=n) (Fq:=Fq)) :
    hammingWeightFqn x ≤ hammingWeightFqn (extendMap x) := by
  unfold hammingWeightFqn
  rw [hammingDist_zero_right, hammingDist_zero_right]
  unfold hammingNorm
  apply Finset.card_le_card_of_injOn (fun i => i.castSucc)
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rwa [extendMap_apply_castSucc]
  · intro i _ j _ hij
    exact Fin.castSucc_injective n hij

/-- The extended code:
adjoin to each codeword the
negative sum of its entries as an extra
coordinate.
This is injective, so the rank is unchanged. -/
public noncomputable def extended : LinearECC (n := n+1) (k:=k) (Fq:=Fq) where
  subspace := l.subspace.map extendMap
  rank_k := by
    have h := (Submodule.equivMapOfInjective extendMap extendMap_injective l.subspace).finrank_eq
    rw [l.rank_k] at h
    exact h.symm

end LinearECC

/-- An error correcting code with a proof that
it's distance is at least `d`. -/
public structure LinearECCnk_weakd (d : ℕ)
  extends LinearECC (n:=n) (k:=k) (Fq:=Fq) where
  distance_d : ∀ x ∈ subspace, x ≠ 0 → hammingWeightFqn x ≥ d

namespace LinearECCnk_weakd

variable {d : ℕ} (l : LinearECCnk_weakd (n:=n) (k:=k) (Fq:=Fq) d)

/-- Extending a code with weak distance bound `d`
gives another code with the same
weak distance bound `d`.
extending never decreases weight. -/
public noncomputable def extended : LinearECCnk_weakd (n:=n+1) (k:=k) (Fq:=Fq) d where
  toLinearECC := l.toLinearECC.extended
  distance_d := by
    intro y hy hy0
    obtain ⟨x, hx, hxy⟩ := hy
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hy0 (by rw [← hxy, map_zero])
    calc d ≤ hammingWeightFqn x := l.distance_d x hx hx0
      _ ≤ hammingWeightFqn (LinearECC.extendMap x) := LinearECC.hammingWeightFqn_extendMap_ge x
      _ = hammingWeightFqn y := by rw [hxy]

end LinearECCnk_weakd

/-- An error correcting code with a proof that
it's distance is exactly `d`. -/
public structure LinearECCnkd (d : ℕ)
  extends LinearECCnk_weakd (n:=n) (k:=k) (Fq:=Fq) (d:=d) where
  distance_d_strict : toLinearECC.distance = d

end GeneralDefinition

section Quotient

variable {n k : ℕ}
variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq Fq]
variable (shift_scale : Units Fq)

namespace LinearECC

variable (l : LinearECC (n:=n) (k:=k) (Fq:=Fq))

/-- The quotient vector space  -/
public abbrev quotientByCode :=
  Fqn (n:=n) (Fq:=Fq) ⧸ l.subspace

/-- On the `quotientByCode` as a set
we have `x → x + shift_scale*indicator i`.
These are translations and they
have order the characteristic of `Fq`. -/
public def qi (i : Fin n) (x : l.quotientByCode) : l.quotientByCode :=
  x + Submodule.Quotient.mk ((shift_scale.1 : Fq) • indicator i)

omit [Fintype Fq] [DecidableEq Fq] in
/-- In the case of characteristic `2`
the translations square to the identity
as permutations of `quotientByCode` -/
public lemma qi_square
  (h2 : (2 : Fq) = (0 : Fq))
  (i : Fin n) (x : l.quotientByCode) :
  l.qi shift_scale i (l.qi shift_scale i x) = x := by
  unfold qi
  rw [add_assoc, ← Submodule.Quotient.mk_add]
  have hzero : indicator i + indicator i = (0 : Fqn (n:=n) (Fq:=Fq)) := by
    funext j
    simp only [indicator, Pi.add_apply, Pi.zero_apply]
    by_cases hij : i = j
    · rw [ite_eq_left hij, one_add_one_eq_two, h2]
    · simp [hij]
  rw [<-smul_add]
  rw [hzero, smul_zero, Submodule.Quotient.mk_zero, add_zero]

omit [Fintype Fq] [DecidableEq Fq] in
/-- The different translations commute. -/
public lemma qij_comm
  (i j : Fin n) (x : l.quotientByCode) :
  l.qi shift_scale j (l.qi shift_scale i x) = l.qi shift_scale i (l.qi shift_scale j x) := by
  unfold qi
  abel

end LinearECC

end Quotient
