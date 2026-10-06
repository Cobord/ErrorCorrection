/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import QuantumErrorCorrection.PointedConeAlgCat
public import QuantumErrorCorrection.RegionCat
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Stoquastic matrices on a region of qudits

A matrix indexed by the classical configurations `S.carrier → Fin d` of `d`-level qudits on a
finite region `S : RegionCat X` is *stoquastic* when all of its off-diagonal entries are
non-positive; equivalently `-A` has non-negative off-diagonal entries, so `exp (-t A)` has
non-negative entries and the associated quantum Monte Carlo sampling is sign-problem free.

Being an entrywise condition, stoquasticity is stable under conic combinations: sums and
non-negative (in particular positive) rescalings of stoquastic matrices are stoquastic
(`isStoquastic_add`, `isStoquastic_smul`, `isStoquastic_sum_smul`), so the stoquastic matrices
on a fixed region form a convex cone and a Hamiltonian assembled from stoquastic local terms is
stoquastic.

The main construction here is `extendAlongRegion`: a morphism `f : S ⟶ T` of `RegionCat X`
(i.e. a witness of `S.carrier ⊆ T.carrier`) lets one view a Hamiltonian supported on `S` as a
Hamiltonian on the larger region `T`, by acting as the identity on the qudits of `T \ S`. On
entries this is
`(A ⊗ 1) v w = A (v|_S) (w|_S) * δ (v|_{T \ S}) (w|_{T \ S})`,
i.e. `A ⊗ 1` under the identification
`(T.carrier → Fin d) ≃ (S.carrier → Fin d) × (↥(T.carrier \ S.carrier) → Fin d)`.

`isStoquastic_extendAlongRegion` records that stoquasticity survives this extension: a new
off-diagonal entry either differs already on `S` (so it is an old off-diagonal entry of `A`) or
differs only off `S` (so the Kronecker delta kills it and the entry is `0`).

The two halves assemble into `stoquasticFunctor : RegionCat X ⥤ PointedConeAlgCat R`, the net of
stoquastic cones: each region carries the matrix algebra on its configurations together with the
cone `stoquasticCone` of stoquastic matrices in it, and each region inclusion acts by
`A ↦ A ⊗ 1`, which preserves that cone. Over a commutative `R` that map is an algebra
homomorphism (`extendAlongRegionₐ`) and not merely linear (`extendAlongRegionₗ`): `1 ⊗ 1 = 1`
and `(A ⊗ 1) (B ⊗ 1) = (A B) ⊗ 1`, the latter because an intermediate configuration contributing
to the product must agree with both outer ones off `S`. It also commutes with the conjugate
transpose (`extendAlongRegionₛₐ`), which is the transpose since `PointedConeAlgCat R` asks for
`TrivialStar R`. Forgetting the multiplicative and `*`-structure gives the same net valued in
plain modules, `stoquasticFunctorₗ`.
-/

@[expose] public section

open CategoryTheory

universe u

variable {X : Type u}
variable {Rows : RegionCat X}
variable {d : ℕ}
variable {R : Type u} [Ring R]

open scoped Matrix

section Order

variable [PartialOrder R]

public def isStoquastic
  (A : Matrix
    (Rows.carrier -> Fin d)
    (Rows.carrier -> Fin d) R) : Prop :=
  ∀ i, ∀ j, i ≠ j → (A i j) ≤ 0

public structure Stoquastic where
  A : Matrix
    (Rows.carrier -> Fin d)
    (Rows.carrier -> Fin d) R
  /-- A matrix is stoquastic if all its
  off-diagonal entries are non-positive. -/
  stoquastic : isStoquastic A

/-- The zero matrix is stoquastic: it has no positive entry at all. -/
public lemma isStoquastic_zero :
    isStoquastic (0 : Matrix (Rows.carrier -> Fin d) (Rows.carrier -> Fin d) R) :=
  fun _ _ _ => le_refl 0

public instance : Zero (Stoquastic (Rows := Rows) (d := d) (R := R)) :=
  ⟨⟨0, isStoquastic_zero⟩⟩

@[simp] public lemma Stoquastic.zero_A :
    (0 : Stoquastic (Rows := Rows) (d := d) (R := R)).A = 0 := rfl

end Order

/-! ### Conic combinations

Stoquasticity is an entrywise `≤ 0` condition on the off-diagonal, so it is preserved by sums
and by scaling with a non-negative coefficient: the stoquastic matrices on a fixed region form
a convex cone. This is what lets one assemble a stoquastic Hamiltonian out of stoquastic local
terms, as in `isStoquastic_sum_smul`. -/

section Cone

variable [PartialOrder R] [IsOrderedRing R]
variable {A B : Matrix (Rows.carrier -> Fin d) (Rows.carrier -> Fin d) R}

/-- A sum of two stoquastic matrices is stoquastic. -/
public lemma isStoquastic_add (hA : isStoquastic A) (hB : isStoquastic B) :
    isStoquastic (A + B) :=
  fun i j hij => add_nonpos (hA i j hij) (hB i j hij)

/-- Scaling a stoquastic matrix by a non-negative coefficient keeps it stoquastic; a negative
coefficient would instead flip the off-diagonal entries to be non-negative. -/
public lemma isStoquastic_smul {c : R} (hc : 0 ≤ c) (hA : isStoquastic A) :
    isStoquastic (c • A) :=
  fun i j hij => mul_nonpos_of_nonneg_of_nonpos hc (hA i j hij)

/-- A finite sum of stoquastic matrices is stoquastic. -/
public lemma isStoquastic_sum {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (Rows.carrier -> Fin d) (Rows.carrier -> Fin d) R)
    (hA : ∀ k ∈ s, isStoquastic (A k)) : isStoquastic (∑ k ∈ s, A k) := by
  intro i j hij
  rw [Matrix.sum_apply]
  exact Finset.sum_nonpos fun k hk => hA k hk i j hij

/-- **A conic combination of stoquastic matrices is stoquastic**: a finite sum of stoquastic
matrices with non-negative coefficients — in particular with positive ones. -/
public theorem isStoquastic_sum_smul {ι : Type*} (s : Finset ι) (c : ι → R)
    (A : ι → Matrix (Rows.carrier -> Fin d) (Rows.carrier -> Fin d) R)
    (hc : ∀ k ∈ s, 0 ≤ c k) (hA : ∀ k ∈ s, isStoquastic (A k)) :
    isStoquastic (∑ k ∈ s, c k • A k) :=
  isStoquastic_sum s _ fun k hk => isStoquastic_smul (hc k hk) (hA k hk)

/-- The stoquastic matrices on a fixed region, bundled as a `PointedCone`: they contain `0` and
are closed under addition and under scaling by a non-negative scalar. -/
public def stoquasticCone :
    PointedCone R (Matrix (Rows.carrier -> Fin d) (Rows.carrier -> Fin d) R) where
  carrier := {A | isStoquastic A}
  zero_mem' := isStoquastic_zero
  add_mem' := isStoquastic_add
  smul_mem' c _ hA := isStoquastic_smul c.2 hA

@[simp] public lemma mem_stoquasticCone
    {A : Matrix (Rows.carrier -> Fin d) (Rows.carrier -> Fin d) R} :
    A ∈ stoquasticCone (Rows := Rows) ↔ isStoquastic A := Iff.rfl

namespace Stoquastic

variable (H K : Stoquastic (Rows := Rows) (d := d) (R := R))

public instance : Add (Stoquastic (Rows := Rows) (d := d) (R := R)) :=
  ⟨fun H K => ⟨H.A + K.A, isStoquastic_add H.stoquastic K.stoquastic⟩⟩

@[simp] public lemma add_A : (H + K).A = H.A + K.A := rfl

/-- Scale a stoquastic Hamiltonian by a non-negative coefficient. -/
public def smul {c : R} (hc : 0 ≤ c) : Stoquastic (Rows := Rows) (d := d) (R := R) :=
  ⟨c • H.A, isStoquastic_smul hc H.stoquastic⟩

@[simp] public lemma smul_A {c : R} (hc : 0 ≤ c) : (H.smul hc).A = c • H.A := rfl

end Stoquastic

end Cone

/-! ### Extending along a region inclusion

Throughout this section `f : S ⟶ T` is a morphism of `RegionCat X`, i.e. a witness that the
region `S` sits inside the region `T`. -/

section ExtendAlongRegion

variable {S T U : RegionCat X}

/-- Restrict a qudit configuration on the region `T` to the smaller region `S`, along a
morphism `f : S ⟶ T` of `RegionCat X`. This is the map the extension below reads its `S`-block
indices through. -/
public def configRestrict (f : S ⟶ T) (v : T.carrier -> Fin d) : S.carrier -> Fin d :=
  fun i => v ⟨i, RegionCat.subsetOfHom f i.2⟩

@[simp] public lemma configRestrict_id (v : Rows.carrier -> Fin d) :
    configRestrict (𝟙 Rows) v = v := rfl

@[simp] public lemma configRestrict_comp (f : S ⟶ T) (g : T ⟶ U) (v : U.carrier -> Fin d) :
    configRestrict (f ≫ g) v = configRestrict f (configRestrict g v) := rfl

variable [DecidableEq X]

/-- Extend a qudit configuration on the region `S` to one on the larger region `T`, copying a
reference configuration `v` on the new qudits `T \ S`. It is a section of `configRestrict`, and
on the configurations agreeing with `v` off `S` it is a two-sided inverse: this is the
reindexing that makes the identity factor of `A ⊗ 1` collapse in `extendAlongRegion_mul`. -/
public def configExtend (v : T.carrier -> Fin d) (y : S.carrier -> Fin d) :
    T.carrier -> Fin d :=
  fun t => if h : (t : X) ∈ S.carrier then y ⟨t, h⟩ else v t

public lemma configExtend_apply_of_mem (v : T.carrier -> Fin d) (y : S.carrier -> Fin d)
    {t : T.carrier} (ht : (t : X) ∈ S.carrier) : configExtend v y t = y ⟨t, ht⟩ :=
  dite_eq_left ht

public lemma configExtend_apply_of_not_mem (v : T.carrier -> Fin d) (y : S.carrier -> Fin d)
    {t : T.carrier} (ht : (t : X) ∉ S.carrier) : configExtend v y t = v t :=
  dite_eq_right ht

@[simp] public lemma configRestrict_configExtend (f : S ⟶ T) (v : T.carrier -> Fin d)
    (y : S.carrier -> Fin d) : configRestrict f (configExtend v y) = y :=
  funext fun i => configExtend_apply_of_mem v y i.2

/-- `configExtend v` copies `v` on the new qudits, so it never disagrees with `v` off `S`. -/
public lemma agree_configExtend (v : T.carrier -> Fin d) (y : S.carrier -> Fin d) :
    ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = configExtend v y t :=
  fun _ ht => (configExtend_apply_of_not_mem v y ht).symm

/-- On a configuration `x` that already agrees with `v` off `S`, extending its restriction
recovers it. -/
public lemma configExtend_configRestrict (f : S ⟶ T) {v x : T.carrier -> Fin d}
    (h : ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = x t) :
    configExtend v (configRestrict f x) = x := by
  funext t
  by_cases ht : (t : X) ∈ S.carrier
  · exact configExtend_apply_of_mem v _ ht
  · exact (configExtend_apply_of_not_mem v _ ht).trans (h t ht)

/-- Extend a matrix on the configurations of the region `S` to one on the configurations of a
larger region `T`, along a morphism `f : S ⟶ T` of `RegionCat X`: act by `A` on the qudits of
`S` and by the identity on the qudits of `T \ S`. In other words this is `A ⊗ 1`, the Kronecker
delta being the condition that the two configurations agree outside `S`. -/
public def extendAlongRegion (f : S ⟶ T)
    (A : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R) :
    Matrix (T.carrier -> Fin d) (T.carrier -> Fin d) R :=
  fun v w => if ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = w t
    then A (configRestrict f v) (configRestrict f w) else 0

/-- On the "diagonal" of the identity factor — two configurations agreeing outside `S` — the
extended matrix is just the corresponding entry of `A`. -/
public lemma extendAlongRegion_apply_of_agree (f : S ⟶ T)
    (A : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R) {v w : T.carrier -> Fin d}
    (h : ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = w t) :
    extendAlongRegion f A v w = A (configRestrict f v) (configRestrict f w) :=
  ite_eq_left h

/-- Off the "diagonal" of the identity factor the extended matrix vanishes: the identity on
`T \ S` does not connect configurations differing there. -/
public lemma extendAlongRegion_apply_of_not_agree (f : S ⟶ T)
    (A : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R) {v w : T.carrier -> Fin d}
    (h : ¬ ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = w t) :
    extendAlongRegion f A v w = 0 :=
  ite_eq_right h

/-- Two configurations on `T` that agree outside `S` and whose restrictions to `S` agree are
equal: the only data a configuration on `T` carries is its `S`-block and its `T \ S`-block. -/
public lemma eq_of_configRestrict_eq_of_agree (f : S ⟶ T) {v w : T.carrier -> Fin d}
    (hoff : ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = w t)
    (hon : configRestrict f v = configRestrict f w) : v = w := by
  funext t
  by_cases ht : (t : X) ∈ S.carrier
  · exact congrFun hon ⟨t, ht⟩
  · exact hoff t ht

/-- Extending along the identity morphism changes nothing: there are no qudits to tensor an
identity onto. -/
@[simp] public lemma extendAlongRegion_id
    (A : Matrix (Rows.carrier -> Fin d) (Rows.carrier -> Fin d) R) :
    extendAlongRegion (𝟙 Rows) A = A := by
  funext v w
  exact extendAlongRegion_apply_of_agree _ _ fun t ht => absurd t.2 ht

/-- Extending along a composite is extending twice: `(A ⊗ 1_{T \ S}) ⊗ 1_{U \ T} = A ⊗ 1_{U \ S}`
for `S ⊆ T ⊆ U`. -/
public lemma extendAlongRegion_comp (f : S ⟶ T) (g : T ⟶ U)
    (A : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R) :
    extendAlongRegion (f ≫ g) A = extendAlongRegion g (extendAlongRegion f A) := by
  funext v w
  by_cases hS : ∀ u : U.carrier, (u : X) ∉ S.carrier → v u = w u
  · have hT : ∀ u : U.carrier, (u : X) ∉ T.carrier → v u = w u :=
      fun u hu => hS u fun h => hu (RegionCat.subsetOfHom f h)
    rw [extendAlongRegion_apply_of_agree _ _ hS, extendAlongRegion_apply_of_agree _ _ hT,
      extendAlongRegion_apply_of_agree _ _ fun t ht => hS ⟨t, RegionCat.subsetOfHom g t.2⟩ ht]
    rfl
  · rw [extendAlongRegion_apply_of_not_agree _ _ hS]
    by_cases hT : ∀ u : U.carrier, (u : X) ∉ T.carrier → v u = w u
    · rw [extendAlongRegion_apply_of_agree g _ hT]
      refine (extendAlongRegion_apply_of_not_agree f A fun hSt => hS fun u hu => ?_).symm
      by_cases hu' : (u : X) ∈ T.carrier
      · exact hSt ⟨u, hu'⟩ hu
      · exact hT u hu'
    · exact (extendAlongRegion_apply_of_not_agree _ _ hT).symm

/-- Extending along a region inclusion is additive: tensoring with the identity on `T \ S` is
done entrywise. -/
public lemma extendAlongRegion_add (f : S ⟶ T)
    (A B : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R) :
    extendAlongRegion f (A + B) = extendAlongRegion f A + extendAlongRegion f B := by
  funext v w
  by_cases h : ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = w t
  · rw [Matrix.add_apply, extendAlongRegion_apply_of_agree f (A + B) h,
      extendAlongRegion_apply_of_agree f A h, extendAlongRegion_apply_of_agree f B h,
      Matrix.add_apply]
  · rw [Matrix.add_apply, extendAlongRegion_apply_of_not_agree f (A + B) h,
      extendAlongRegion_apply_of_not_agree f A h, extendAlongRegion_apply_of_not_agree f B h]
    exact (add_zero 0).symm

/-- Extending along a region inclusion commutes with scaling. -/
public lemma extendAlongRegion_smul (f : S ⟶ T) (c : R)
    (A : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R) :
    extendAlongRegion f (c • A) = c • extendAlongRegion f A := by
  funext v w
  by_cases h : ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = w t
  · rw [Matrix.smul_apply, extendAlongRegion_apply_of_agree f (c • A) h,
      extendAlongRegion_apply_of_agree f A h, Matrix.smul_apply]
  · rw [Matrix.smul_apply, extendAlongRegion_apply_of_not_agree f (c • A) h,
      extendAlongRegion_apply_of_not_agree f A h]
    exact (smul_zero c).symm

/-- Extending the zero matrix gives the zero matrix. -/
public lemma extendAlongRegion_zero (f : S ⟶ T) :
    extendAlongRegion f (0 : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R) = 0 := by
  funext v w
  by_cases h : ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = w t
  · exact extendAlongRegion_apply_of_agree f 0 h
  · exact extendAlongRegion_apply_of_not_agree f 0 h

/-- Extending along a region inclusion is unital: `1 ⊗ 1 = 1`. Two configurations of `T` are
equal exactly when they agree off `S` and their restrictions to `S` agree, which is precisely
the pair of conditions the two Kronecker deltas test. -/
public lemma extendAlongRegion_one (f : S ⟶ T) :
    extendAlongRegion f (1 : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R) = 1 := by
  funext v w
  by_cases hvw : v = w
  · subst hvw
    rw [extendAlongRegion_apply_of_agree f 1 fun _ _ => rfl, Matrix.one_apply_eq,
      Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hvw]
    by_cases h : ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = w t
    · rw [extendAlongRegion_apply_of_agree f 1 h,
        Matrix.one_apply_ne fun hres => hvw (eq_of_configRestrict_eq_of_agree f h hres)]
    · exact extendAlongRegion_apply_of_not_agree f 1 h

/-- **Extending along a region inclusion is multiplicative**: `(A ⊗ 1) (B ⊗ 1) = (A B) ⊗ 1`.
The intermediate configuration summed over must agree with both outer ones off `S`, so the sum
collapses onto the configurations extending a configuration of `S` by the outer one — reindexed
by `configRestrict`/`configExtend` — which is exactly the sum computing `(A B)` on `S`. -/
public lemma extendAlongRegion_mul (f : S ⟶ T)
    (A B : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R) :
    extendAlongRegion f (A * B) = extendAlongRegion f A * extendAlongRegion f B := by
  funext v w
  rw [Matrix.mul_apply]
  by_cases h : ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = w t
  · rw [extendAlongRegion_apply_of_agree f (A * B) h, Matrix.mul_apply]
    refine Eq.trans ?_ (Finset.sum_subset (Finset.filter_subset
      (fun x => ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = x t) Finset.univ) ?_)
    · refine (Finset.sum_nbij' (configRestrict f) (configExtend v)
        (fun _ _ => Finset.mem_univ _) (fun y _ => Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, agree_configExtend v y⟩) ?_
        (fun y _ => configRestrict_configExtend f v y) ?_).symm
      · exact fun x hx => configExtend_configRestrict f (Finset.mem_filter.mp hx).2
      · intro x hx
        have hvx := (Finset.mem_filter.mp hx).2
        rw [extendAlongRegion_apply_of_agree f A hvx,
          extendAlongRegion_apply_of_agree f B fun t ht => (hvx t ht).symm.trans (h t ht)]
    · intro x _ hx
      rw [extendAlongRegion_apply_of_not_agree f A fun hvx =>
        hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvx⟩), zero_mul]
  · rw [extendAlongRegion_apply_of_not_agree f (A * B) h]
    refine (Finset.sum_eq_zero fun x _ => ?_).symm
    by_cases hvx : ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = x t
    · rw [extendAlongRegion_apply_of_not_agree f B fun hxw =>
        h fun t ht => (hvx t ht).trans (hxw t ht), mul_zero]
    · rw [extendAlongRegion_apply_of_not_agree f A hvx, zero_mul]

/-- **Isotony**: for `d ≠ 0`, extending along a region inclusion is injective. Every pair of
configurations of `S` extends, by one fixed configuration of the new qudits, to a pair of
configurations of `T` agreeing off `S`, at which `A ⊗ 1` reads off the entry of `A`. For `d = 0`
this fails: the empty region has one configuration and a nonempty one has none. -/
public lemma extendAlongRegion_injective [NeZero d] (f : S ⟶ T) :
    Function.Injective (extendAlongRegion (d := d) (R := R) f) := by
  intro A B h
  let w₀ : T.carrier -> Fin d := fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  funext y z
  have hag : ∀ t : T.carrier, (t : X) ∉ S.carrier →
      configExtend w₀ y t = configExtend w₀ z t := fun t ht => by
    rw [configExtend_apply_of_not_mem _ _ ht, configExtend_apply_of_not_mem _ _ ht]
  have hyz := congrFun (congrFun h (configExtend w₀ y)) (configExtend w₀ z)
  rwa [extendAlongRegion_apply_of_agree f A hag, extendAlongRegion_apply_of_agree f B hag,
    configRestrict_configExtend, configRestrict_configExtend] at hyz

/-- The product of extensions from two disjoint regions `S, T ⊆ U`, entrywise: it is
`A (v|_S) (w|_S) * B (v|_T) (w|_T)` when `v` and `w` agree off `S ∪ T`, and `0` otherwise. The
sum over the intermediate configuration `x` has one surviving term, `x = w` on `S` and `x = v`
off `S`. -/
public lemma extendAlongRegion_mul_extendAlongRegion_apply (hST : Disjoint S.carrier T.carrier)
    (f : S ⟶ U) (g : T ⟶ U) (A : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R)
    (B : Matrix (T.carrier -> Fin d) (T.carrier -> Fin d) R) (v w : U.carrier -> Fin d) :
    (extendAlongRegion f A * extendAlongRegion g B) v w =
      if ∀ u : U.carrier, (u : X) ∉ S.carrier → (u : X) ∉ T.carrier → v u = w u then
        A (configRestrict f v) (configRestrict f w) * B (configRestrict g v) (configRestrict g w)
      else 0 := by
  rw [Matrix.mul_apply]
  let x : U.carrier -> Fin d := fun u => if (u : X) ∈ S.carrier then w u else v u
  rw [Finset.sum_eq_single x]
  · have hvx : ∀ u : U.carrier, (u : X) ∉ S.carrier → v u = x u :=
      fun u hu => by simp [x, hu]
    have hxS : configRestrict f x = configRestrict f w :=
      funext fun i => by simp [configRestrict, x, i.2]
    have hxT : configRestrict g x = configRestrict g v :=
      funext fun i => by simp [configRestrict, x, Finset.disjoint_right.1 hST i.2]
    rw [extendAlongRegion_apply_of_agree f A hvx, hxS]
    split_ifs with hvw
    · have hxw : ∀ u : U.carrier, (u : X) ∉ T.carrier → x u = w u := fun u hu => by
        by_cases hS : (u : X) ∈ S.carrier
        · simp [x, hS]
        · simp only [x, hS, ite_false]
          exact hvw u hS hu
      rw [extendAlongRegion_apply_of_agree g B hxw, hxT]
    · have hxw : ¬ ∀ u : U.carrier, (u : X) ∉ T.carrier → x u = w u :=
        fun hxw => hvw fun u hS hT => by simpa [x, hS] using hxw u hT
      rw [extendAlongRegion_apply_of_not_agree g B hxw, mul_zero]
  · intro y _ hyx
    by_cases hvy : ∀ u : U.carrier, (u : X) ∉ S.carrier → v u = y u
    · have hyw : ¬ ∀ u : U.carrier, (u : X) ∉ T.carrier → y u = w u :=
        fun hyw => hyx (funext fun u => by
          by_cases hS : (u : X) ∈ S.carrier
          · simp only [x, hS, ite_true]
            exact hyw u (Finset.disjoint_left.1 hST hS)
          · simp only [x, hS, ite_false]
            exact (hvy u hS).symm)
      rw [extendAlongRegion_apply_of_not_agree g B hyw, mul_zero]
    · rw [extendAlongRegion_apply_of_not_agree f A hvy, zero_mul]
  · exact fun h => absurd (Finset.mem_univ x) h

/-- **Extending along a region inclusion commutes with the conjugate transpose**:
`(A ⊗ 1)ᴴ = Aᴴ ⊗ 1`. The condition of agreeing off `S` is symmetric in the two configurations,
and the identity factor is self-adjoint. -/
public lemma extendAlongRegion_conjTranspose [StarRing R] (f : S ⟶ T)
    (A : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R) :
    extendAlongRegion f A.conjTranspose = (extendAlongRegion f A).conjTranspose := by
  funext v w
  by_cases h : ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = w t
  · have h' : ∀ t : T.carrier, (t : X) ∉ S.carrier → w t = v t := fun t ht => (h t ht).symm
    rw [Matrix.conjTranspose_apply, extendAlongRegion_apply_of_agree f _ h,
      extendAlongRegion_apply_of_agree f _ h', Matrix.conjTranspose_apply]
  · have h' : ¬ ∀ t : T.carrier, (t : X) ∉ S.carrier → w t = v t :=
      fun h' => h fun t ht => (h' t ht).symm
    rw [Matrix.conjTranspose_apply, extendAlongRegion_apply_of_not_agree f _ h,
      extendAlongRegion_apply_of_not_agree f _ h', star_zero]

/-- Extension along a region inclusion as an `R`-linear map: `A ↦ A ⊗ 1` is linear in `A`. -/
public def extendAlongRegionₗ (f : S ⟶ T) :
    Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R →ₗ[R]
      Matrix (T.carrier -> Fin d) (T.carrier -> Fin d) R where
  toFun := extendAlongRegion f
  map_add' := extendAlongRegion_add f
  map_smul' := extendAlongRegion_smul f

@[simp] public lemma extendAlongRegionₗ_apply (f : S ⟶ T)
    (A : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R) :
    extendAlongRegionₗ f A = extendAlongRegion f A := rfl

/-- Extension along a region inclusion as an `R`-algebra homomorphism: over a commutative `R`,
where the matrices on a region's configurations form an `R`-algebra, `A ↦ A ⊗ 1` is unital and
multiplicative, not merely linear. -/
public def extendAlongRegionₐ {X : Type u} [DecidableEq X] {d : ℕ} {R : Type u} [CommRing R]
    {S T : RegionCat X} (f : S ⟶ T) :
    Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R →ₐ[R]
      Matrix (T.carrier -> Fin d) (T.carrier -> Fin d) R :=
  AlgHom.mk'
    { toFun := extendAlongRegion f
      map_one' := extendAlongRegion_one f
      map_mul' := extendAlongRegion_mul f
      map_zero' := extendAlongRegion_zero f
      map_add' := extendAlongRegion_add f }
    (extendAlongRegion_smul f)

@[simp] public lemma extendAlongRegionₐ_apply {X : Type u} [DecidableEq X] {d : ℕ} {R : Type u}
    [CommRing R] {S T : RegionCat X} (f : S ⟶ T)
    (A : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R) :
    extendAlongRegionₐ f A = extendAlongRegion f A := rfl

/-- Extension along a region inclusion as a `*`-algebra homomorphism, for the conjugate
transpose on matrices (`extendAlongRegion_conjTranspose`). Over a ring with `TrivialStar R`,
that `star` is the transpose. -/
public def extendAlongRegionₛₐ {X : Type u} [DecidableEq X] {d : ℕ} {R : Type u} [CommRing R]
    [StarRing R] {S T : RegionCat X} (f : S ⟶ T) :
    Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R →⋆ₐ[R]
      Matrix (T.carrier -> Fin d) (T.carrier -> Fin d) R :=
  { extendAlongRegionₐ f with map_star' := extendAlongRegion_conjTranspose f }

@[simp] public lemma extendAlongRegionₛₐ_apply {X : Type u} [DecidableEq X] {d : ℕ}
    {R : Type u} [CommRing R] [StarRing R] {S T : RegionCat X} (f : S ⟶ T)
    (A : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R) :
    extendAlongRegionₛₐ f A = extendAlongRegion f A := rfl

/-- **Microcausality**: over a commutative `R`, observables extended from disjoint regions
`S, T ⊆ U` commute, `(A ⊗ 1) (1 ⊗ B) = (1 ⊗ B) (A ⊗ 1)`; both sides are `A ⊗ B` entrywise
(`extendAlongRegion_mul_extendAlongRegion_apply`). -/
public lemma extendAlongRegion_commute {X : Type u} [DecidableEq X] {d : ℕ} {R : Type u}
    [CommRing R] {S T U : RegionCat X} (hST : Disjoint S.carrier T.carrier) (f : S ⟶ U)
    (g : T ⟶ U) (A : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R)
    (B : Matrix (T.carrier -> Fin d) (T.carrier -> Fin d) R) :
    extendAlongRegion f A * extendAlongRegion g B =
      extendAlongRegion g B * extendAlongRegion f A := by
  funext v w
  rw [extendAlongRegion_mul_extendAlongRegion_apply hST,
    extendAlongRegion_mul_extendAlongRegion_apply hST.symm]
  by_cases h : ∀ u : U.carrier, (u : X) ∉ S.carrier → (u : X) ∉ T.carrier → v u = w u
  · have h' : ∀ u : U.carrier, (u : X) ∉ T.carrier → (u : X) ∉ S.carrier → v u = w u :=
      fun u hT hS => h u hS hT
    rw [ite_eq_left h, ite_eq_left h', mul_comm]
  · have h' : ¬ ∀ u : U.carrier, (u : X) ∉ T.carrier → (u : X) ∉ S.carrier → v u = w u :=
      fun h' => h fun u hS hT => h' u hT hS
    rw [ite_eq_right h, ite_eq_right h']

variable [PartialOrder R]

/-- **Stoquasticity is preserved by extension along a region inclusion.** Tensoring with the
identity on the new qudits `T \ S` creates no positive off-diagonal entry: an off-diagonal
entry of `A ⊗ 1` whose configurations already differ on `S` is an off-diagonal entry of `A`,
and one whose configurations differ only outside `S` is `0`. -/
public theorem isStoquastic_extendAlongRegion (f : S ⟶ T)
    {A : Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R} (hA : isStoquastic A) :
    isStoquastic (extendAlongRegion f A) := by
  intro v w hvw
  by_cases h : ∀ t : T.carrier, (t : X) ∉ S.carrier → v t = w t
  · rw [extendAlongRegion_apply_of_agree _ _ h]
    exact hA _ _ fun hon => hvw (eq_of_configRestrict_eq_of_agree f h hon)
  · exact le_of_eq (extendAlongRegion_apply_of_not_agree _ _ h)

namespace Stoquastic

/-- Push a stoquastic Hamiltonian on the region `S` forward to the larger region `T` along a
morphism `f : S ⟶ T` of `RegionCat X`, by acting as the identity on the qudits of `T \ S`. -/
public def extendAlongRegion (f : S ⟶ T) (H : Stoquastic (Rows := S) (d := d) (R := R)) :
    Stoquastic (Rows := T) (d := d) (R := R) where
  A := _root_.extendAlongRegion f H.A
  stoquastic := isStoquastic_extendAlongRegion f H.stoquastic

@[simp] public lemma extendAlongRegion_A (f : S ⟶ T)
    (H : Stoquastic (Rows := S) (d := d) (R := R)) :
    (H.extendAlongRegion f).A = _root_.extendAlongRegion f H.A := rfl

end Stoquastic

end ExtendAlongRegion

/-! ### The net of all matrices -/

/-- **The net of qudit matrix algebras** `RegionCat X ⥤ StarAlgCat R`: a region `S` is sent to
the `*`-algebra of all matrices on its qudit configurations (`star` the conjugate transpose), and
a region inclusion `S ⟶ T` to `A ↦ A ⊗ 1` (`extendAlongRegionₛₐ`). No order on `R` is needed;
this is the stoquastic net below with its cones forgotten (`stoquasticFunctor_forgetCone`). -/
public def quditMatrixFunctor (X : Type u) [DecidableEq X] (d : ℕ) (R : Type u) [CommRing R]
    [StarRing R] : RegionCat X ⥤ StarAlgCat R where
  obj S := StarAlgCat.of (Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R)
  map f := StarAlgCat.ofHom (extendAlongRegionₛₐ f)
  map_id _ := StarAlgCat.hom_ext fun A => extendAlongRegion_id A
  map_comp f g := StarAlgCat.hom_ext fun A => extendAlongRegion_comp f g A

/-! ### The net of stoquastic cones

Assembling the two halves: each region carries the cone of stoquastic matrices on its
configurations, and each region inclusion acts by tensoring with the identity on the new qudits,
which is linear and cone-preserving. -/

/-- **The net of stoquastic Hamiltonians as a functor** `RegionCat X ⥤ PointedConeAlgCat R`: a
region `S` is sent to the matrix algebra on its qudit configurations together with its
stoquastic cone, and a region inclusion `S ⟶ T` to `A ↦ A ⊗ 1`, extension by the identity on the
new qudits `T \ S`. That map is a `*`-algebra homomorphism for the transpose, not merely a
linear one (`extendAlongRegionₛₐ`), and it carries stoquastic matrices to stoquastic matrices
(`isStoquastic_extendAlongRegion`). Functoriality is `extendAlongRegion_id` and
`extendAlongRegion_comp`. -/
public def stoquasticFunctor (X : Type u) [DecidableEq X] (d : ℕ) (R : Type u) [CommRing R]
    [PartialOrder R] [IsOrderedRing R] [StarRing R] [TrivialStar R] :
    RegionCat X ⥤ PointedConeAlgCat R where
  obj S := PointedConeAlgCat.of (Matrix (S.carrier -> Fin d) (S.carrier -> Fin d) R)
    (stoquasticCone (Rows := S))
  map f := PointedConeAlgCat.homOfMapsTo (extendAlongRegionₛₐ f)
    fun _ hA => isStoquastic_extendAlongRegion f hA
  map_id _ := PointedConeAlgCat.hom_ext fun A => extendAlongRegion_id A
  map_comp f g := PointedConeAlgCat.hom_ext fun A => extendAlongRegion_comp f g A

/-- Forgetting the stoquastic cones leaves the net of all qudit matrix algebras. -/
public theorem stoquasticFunctor_forgetCone (X : Type u) [DecidableEq X] (d : ℕ) (R : Type u)
    [CommRing R] [PartialOrder R] [IsOrderedRing R] [StarRing R] [TrivialStar R] :
    stoquasticFunctor X d R ⋙ PointedConeAlgCat.forgetCone = quditMatrixFunctor X d R := rfl

/-- The stoquastic net seen as a net of cones in plain modules: `stoquasticFunctor` followed by
`PointedConeAlgCat.forgetMul`, forgetting the matrix multiplication and remembering of
`A ↦ A ⊗ 1` only that it is linear (`extendAlongRegionₗ`). The objects and the underlying maps
are unchanged, so this is the same net with less structure recorded, not a different one. -/
public def stoquasticFunctorₗ (X : Type u) [DecidableEq X] (d : ℕ) (R : Type u) [CommRing R]
    [PartialOrder R] [IsOrderedRing R] [StarRing R] [TrivialStar R] :
    RegionCat X ⥤ PointedConeCat R :=
  stoquasticFunctor X d R ⋙ PointedConeAlgCat.forgetMul

@[simp] public lemma stoquasticFunctorₗ_obj_cone (X : Type u) [DecidableEq X] (d : ℕ)
    (R : Type u) [CommRing R] [PartialOrder R] [IsOrderedRing R] [StarRing R] [TrivialStar R]
    (S : RegionCat X) :
    ((stoquasticFunctorₗ X d R).obj S).cone = stoquasticCone (Rows := S) := rfl

@[simp] public lemma toLinearMap_stoquasticFunctorₗ_map (X : Type u) [DecidableEq X] (d : ℕ)
    (R : Type u) [CommRing R] [PartialOrder R] [IsOrderedRing R] [StarRing R] [TrivialStar R]
    {S T : RegionCat X} (f : S ⟶ T) :
    PointedConeCat.toLinearMap ((stoquasticFunctorₗ X d R).map f) = extendAlongRegionₗ f := rfl
