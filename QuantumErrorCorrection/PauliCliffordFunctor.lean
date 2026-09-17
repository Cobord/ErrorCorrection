/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import QuantumErrorCorrection.CliffordGroup
public import QuantumErrorCorrection.PauliFunctor
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Extending Clifford automorphisms along region inclusions

For disjoint regions `S`, `T` covering a common region `U` (`S.carrier ∪ T.carrier =
U.carrier`), the Weyl cocycle of `PauliGroup ↥U.carrier d` splits as a sum over `S` and `T`
(since the pairing `⟨a, b⟩ = ∑ i, a i * b i` splits over a disjoint union of index sets), which
is exactly what makes `PauliGroup ↥U.carrier d` a *central product* of `PauliGroup ↥S.carrier d`
and `PauliGroup ↥T.carrier d`, glued along their shared central phase group:

  `centralProdHom : PauliGroup ↥S.carrier d × PauliGroup ↥T.carrier d →* PauliGroup ↥U.carrier d`

is surjective. A Clifford automorphism `φ` of `PauliGroup ↥S.carrier d`, paired with the
identity on `T`, fixes the kernel of `centralProdHom` pointwise (every kernel element is a pair
of pure phases, and `φ` fixes phases), and so descends through the resulting
first-isomorphism-theorem equivalence to an automorphism `cliffordAutExtend φ` of `PauliGroup
↥U.carrier d` — which is again a Clifford automorphism, acting as `φ` on `S` and trivially on
the complementary qudits.
-/

public section

open CategoryTheory

universe u

namespace PauliGroup

variable {X : Type u} [DecidableEq X] {d : ℕ}

section CentralProduct

variable {S T U : RegionCat X}

/-- The central-product homomorphism combining Pauli elements on two disjoint regions into one
on a common enclosing region `U`. Well-defined as a homomorphism precisely because Pauli
elements on disjoint regions commute (`commute_of_disjoint_range`). -/
noncomputable def centralProdHom (hS : S.carrier ⊆ U.carrier) (hT : T.carrier ⊆ U.carrier)
    (hdisj : Disjoint S.carrier T.carrier) :
    PauliGroup ↥S.carrier d × PauliGroup ↥T.carrier d →* PauliGroup ↥U.carrier d where
  toFun p := quditInclusionHom hS p.1 * quditInclusionHom hT p.2
  map_one' := by simp
  map_mul' p q := by
    show quditInclusionHom hS (p.1 * q.1) * quditInclusionHom hT (p.2 * q.2)
        = quditInclusionHom hS p.1 * quditInclusionHom hT p.2 *
          (quditInclusionHom hS q.1 * quditInclusionHom hT q.2)
    rw [map_mul, map_mul]
    exact (commute_of_disjoint_range hS hT hdisj q.1 p.2).mul_mul_mul_comm _ _

omit [DecidableEq X] in
private lemma centralProdHom_apply (hS : S.carrier ⊆ U.carrier) (hT : T.carrier ⊆ U.carrier)
    (hdisj : Disjoint S.carrier T.carrier) (p : PauliGroup ↥S.carrier d × PauliGroup ↥T.carrier d) :
    centralProdHom hS hT hdisj p = quditInclusionHom hS p.1 * quditInclusionHom hT p.2 := rfl

omit [DecidableEq X] in
/-- If two vectors of exponents on disjoint regions extend (by zero) to a sum of zero, each was
already zero: at a point of `S`'s image the `T`-part vanishes (disjointness), forcing the
`S`-part to vanish there too, and vice versa. -/
private lemma eq_zero_of_extendAlong_add_extendAlong_eq_zero (hS : S.carrier ⊆ U.carrier)
    (hT : T.carrier ⊆ U.carrier) (hdisj : Disjoint S.carrier T.carrier)
    (a : ↥S.carrier → ZMod d) (b : ↥T.carrier → ZMod d)
    (h : extendAlong (regionInclusionEmbedding hS) a
      + extendAlong (regionInclusionEmbedding hT) b = 0) : a = 0 ∧ b = 0 := by
  constructor
  · funext i
    have hz := congrFun h (regionInclusionEmbedding hS i)
    have hnotmem : regionInclusionEmbedding hS i ∉ Set.range (regionInclusionEmbedding hT) := by
      rw [mem_range_regionInclusionEmbedding, regionInclusionEmbedding_coe]
      exact Finset.disjoint_left.mp hdisj i.2
    simpa [extendAlong_apply, extendAlong_apply_of_not_mem_range _ _ hnotmem] using hz
  · funext i
    have hz := congrFun h (regionInclusionEmbedding hT i)
    have hnotmem : regionInclusionEmbedding hT i ∉ Set.range (regionInclusionEmbedding hS) := by
      rw [mem_range_regionInclusionEmbedding, regionInclusionEmbedding_coe]
      exact Finset.disjoint_left.mp hdisj.symm i.2
    simpa [extendAlong_apply, extendAlong_apply_of_not_mem_range _ _ hnotmem] using hz

omit [DecidableEq X] in
/-- Every element of the kernel of `centralProdHom` is a pair of pure phases. -/
private lemma fst_eq_phaseGen_of_centralProdHom_eq_one (hS : S.carrier ⊆ U.carrier)
    (hT : T.carrier ⊆ U.carrier) (hdisj : Disjoint S.carrier T.carrier)
    {p : PauliGroup ↥S.carrier d × PauliGroup ↥T.carrier d}
    (hp : centralProdHom hS hT hdisj p = 1) : p.1 = phaseGen p.1.phase := by
  have hshift : extendAlong (regionInclusionEmbedding hS) p.1.shift
      + extendAlong (regionInclusionEmbedding hT) p.2.shift = 0 := by
    have hz := congrArg PauliGroup.shift hp
    rw [centralProdHom_apply] at hz
    rwa [mul_shift, quditInclusionHom_apply_shift, quditInclusionHom_apply_shift, one_shift]
      at hz
  have hclock : extendAlong (regionInclusionEmbedding hS) p.1.clock
      + extendAlong (regionInclusionEmbedding hT) p.2.clock = 0 := by
    have hz := congrArg PauliGroup.clock hp
    rw [centralProdHom_apply] at hz
    rwa [mul_clock, quditInclusionHom_apply_clock, quditInclusionHom_apply_clock, one_clock]
      at hz
  exact PauliGroup.ext rfl
    (eq_zero_of_extendAlong_add_extendAlong_eq_zero hS hT hdisj p.1.shift p.2.shift hshift).1
    (eq_zero_of_extendAlong_add_extendAlong_eq_zero hS hT hdisj p.1.clock p.2.clock hclock).1

/-- Given a covering `S.carrier ∪ T.carrier ⊇ U.carrier`, reconstruct a vector of exponents on
`U` from its restrictions to `S` and `T`. -/
private lemma extendAlong_cover_eq (hS : S.carrier ⊆ U.carrier) (hT : T.carrier ⊆ U.carrier)
    (hdisj : Disjoint S.carrier T.carrier) (hcov : U.carrier ⊆ S.carrier ∪ T.carrier)
    (v : ↥U.carrier → ZMod d) :
    extendAlong (regionInclusionEmbedding hS) (v ∘ regionInclusionEmbedding hS)
      + extendAlong (regionInclusionEmbedding hT) (v ∘ regionInclusionEmbedding hT) = v := by
  funext z
  simp only [Pi.add_apply]
  by_cases hzS : (z : X) ∈ S.carrier
  · have hzSr : z ∈ Set.range (regionInclusionEmbedding hS) :=
      (mem_range_regionInclusionEmbedding hS z).mpr hzS
    obtain ⟨i, rfl⟩ := hzSr
    have hzTr : regionInclusionEmbedding hS i ∉ Set.range (regionInclusionEmbedding hT) := by
      rw [mem_range_regionInclusionEmbedding]
      exact Finset.disjoint_left.mp hdisj hzS
    rw [extendAlong_apply, extendAlong_apply_of_not_mem_range _ _ hzTr, Function.comp_apply,
      add_zero]
  · have hzT : (z : X) ∈ T.carrier := (Finset.mem_union.mp (hcov z.2)).resolve_left hzS
    have hzTr : z ∈ Set.range (regionInclusionEmbedding hT) :=
      (mem_range_regionInclusionEmbedding hT z).mpr hzT
    obtain ⟨i, rfl⟩ := hzTr
    have hzSr : regionInclusionEmbedding hT i ∉ Set.range (regionInclusionEmbedding hS) := by
      rw [mem_range_regionInclusionEmbedding]
      exact Finset.disjoint_left.mp hdisj.symm hzT
    rw [extendAlong_apply_of_not_mem_range _ _ hzSr, extendAlong_apply, Function.comp_apply,
      zero_add]

/-- `centralProdHom` is surjective whenever `S` and `T` cover `U`: every Pauli element on `U`
is the product of its (phase-carrying) restriction to `S` and its (phaseless) restriction
to `T`. -/
private lemma centralProdHom_surjective (hS : S.carrier ⊆ U.carrier) (hT : T.carrier ⊆ U.carrier)
    (hdisj : Disjoint S.carrier T.carrier) (hcov : U.carrier ⊆ S.carrier ∪ T.carrier) :
    Function.Surjective (centralProdHom (d := d) hS hT hdisj) := by
  intro k
  refine ⟨(⟨k.phase, k.shift ∘ regionInclusionEmbedding hS, k.clock ∘ regionInclusionEmbedding hS⟩,
    ⟨0, k.shift ∘ regionInclusionEmbedding hT, k.clock ∘ regionInclusionEmbedding hT⟩), ?_⟩
  apply PauliGroup.ext
  · simp only [centralProdHom_apply, mul_phase, quditInclusionHom_apply_phase,
      quditInclusionHom_apply_shift, quditInclusionHom_apply_clock]
    rw [pairing_extendAlong_of_disjoint (regionInclusionEmbedding hT)
      (regionInclusionEmbedding hS) (disjoint_range_regionInclusionEmbedding hS hT hdisj).symm]
    ring
  · simp only [centralProdHom_apply, mul_shift, quditInclusionHom_apply_shift]
    exact extendAlong_cover_eq hS hT hdisj hcov k.shift
  · simp only [centralProdHom_apply, mul_clock, quditInclusionHom_apply_clock]
    exact extendAlong_cover_eq hS hT hdisj hcov k.clock

/-- Extend an automorphism of `PauliGroup ↥S.carrier d` by the identity on `T`. -/
def prodExtend (φ : MulAut (PauliGroup ↥S.carrier d)) :
    (PauliGroup ↥S.carrier d × PauliGroup ↥T.carrier d) ≃*
      (PauliGroup ↥S.carrier d × PauliGroup ↥T.carrier d) :=
  MulEquiv.prodCongr φ (MulEquiv.refl _)

omit [DecidableEq X] in
private lemma prodExtend_apply (φ : MulAut (PauliGroup ↥S.carrier d))
    (p : PauliGroup ↥S.carrier d × PauliGroup ↥T.carrier d) :
    prodExtend (T := T) φ p = (φ p.1, p.2) := rfl

omit [DecidableEq X] in
/-- If `φ` fixes every phase (i.e. lies in the Clifford automorphism group), `prodExtend φ` fixes the kernel
of `centralProdHom` pointwise: every kernel element is a pair of phases
(`fst_eq_phaseGen_of_centralProdHom_eq_one`), and `φ` fixes those. -/
private lemma prodExtend_eq_self_of_mem_ker (hS : S.carrier ⊆ U.carrier)
    (hT : T.carrier ⊆ U.carrier) (hdisj : Disjoint S.carrier T.carrier)
    (φ : CliffordAutGroup ↥S.carrier d) {p : PauliGroup ↥S.carrier d × PauliGroup ↥T.carrier d}
    (hp : p ∈ MonoidHom.ker (centralProdHom hS hT hdisj)) : prodExtend φ.1 p = p := by
  have h1 : p.1 = phaseGen p.1.phase :=
    fst_eq_phaseGen_of_centralProdHom_eq_one hS hT hdisj hp
  rw [prodExtend_apply]
  refine Prod.ext ?_ rfl
  rw [h1]
  exact φ.2 p.1.phase

omit [DecidableEq X] in
private lemma ker_map_prodExtend_eq (hS : S.carrier ⊆ U.carrier) (hT : T.carrier ⊆ U.carrier)
    (hdisj : Disjoint S.carrier T.carrier) (φ : CliffordAutGroup ↥S.carrier d) :
    (MonoidHom.ker (centralProdHom hS hT hdisj)).map
        (prodExtend (T := T) φ.1 : PauliGroup ↥S.carrier d × PauliGroup ↥T.carrier d →*
          PauliGroup ↥S.carrier d × PauliGroup ↥T.carrier d)
      = MonoidHom.ker (centralProdHom hS hT hdisj) := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    show prodExtend φ.1 p ∈ MonoidHom.ker (centralProdHom hS hT hdisj)
    rw [prodExtend_eq_self_of_mem_ker hS hT hdisj φ hp]
    exact hp
  · intro p hp
    exact ⟨p, hp, prodExtend_eq_self_of_mem_ker hS hT hdisj φ hp⟩

/-- Extend a Clifford automorphism of `PauliGroup ↥S.carrier d` to one of `PauliGroup
↥U.carrier d`, acting as the identity on the complementary region `T`. Constructed via the
isomorphism `PauliGroup ↥U.carrier d ≅ (PauliGroup ↥S.carrier d × PauliGroup ↥T.carrier d) ⧸
ker centralProdHom` (the central-product decomposition): `φ` paired with the identity on `T`
fixes the kernel pointwise (since `φ` fixes phases), hence descends to the quotient, hence
transports across the isomorphism. -/
noncomputable def cliffordAutExtend (hS : S.carrier ⊆ U.carrier) (hT : T.carrier ⊆ U.carrier)
    (hdisj : Disjoint S.carrier T.carrier) (hcov : U.carrier ⊆ S.carrier ∪ T.carrier)
    (φ : CliffordAutGroup ↥S.carrier d) : MulAut (PauliGroup ↥U.carrier d) :=
  let e := QuotientGroup.quotientKerEquivOfSurjective (centralProdHom hS hT hdisj)
    (centralProdHom_surjective hS hT hdisj hcov)
  let e' := QuotientGroup.congr (MonoidHom.ker (centralProdHom hS hT hdisj))
    (MonoidHom.ker (centralProdHom hS hT hdisj)) (prodExtend (T := T) φ.1)
    (ker_map_prodExtend_eq hS hT hdisj φ)
  e.symm.trans (e'.trans e)

/-- `cliffordAutExtend` commutes with `centralProdHom`: extending `φ` and then combining is the
same as combining `φ p` (with the `T`-part unchanged). -/
private lemma cliffordAutExtend_centralProdHom_apply (hS : S.carrier ⊆ U.carrier)
    (hT : T.carrier ⊆ U.carrier) (hdisj : Disjoint S.carrier T.carrier)
    (hcov : U.carrier ⊆ S.carrier ∪ T.carrier) (φ : CliffordAutGroup ↥S.carrier d)
    (p : PauliGroup ↥S.carrier d × PauliGroup ↥T.carrier d) :
    cliffordAutExtend hS hT hdisj hcov φ (centralProdHom hS hT hdisj p)
      = centralProdHom hS hT hdisj (prodExtend φ.1 p) := by
  show ((QuotientGroup.quotientKerEquivOfSurjective (centralProdHom hS hT hdisj)
        (centralProdHom_surjective hS hT hdisj hcov)).symm.trans
      ((QuotientGroup.congr (MonoidHom.ker (centralProdHom hS hT hdisj))
          (MonoidHom.ker (centralProdHom hS hT hdisj)) (prodExtend φ.1)
          (ker_map_prodExtend_eq hS hT hdisj φ)).trans
        (QuotientGroup.quotientKerEquivOfSurjective (centralProdHom hS hT hdisj)
          (centralProdHom_surjective hS hT hdisj hcov))))
      (centralProdHom hS hT hdisj p)
      = centralProdHom hS hT hdisj (prodExtend φ.1 p)
  simp only [MulEquiv.trans_apply]
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective (centralProdHom hS hT hdisj)
      (centralProdHom_surjective hS hT hdisj hcov)).symm (centralProdHom hS hT hdisj p)
      = QuotientGroup.mk p := by
    rw [MulEquiv.symm_apply_eq]
    exact (QuotientGroup.kerLift_mk (centralProdHom hS hT hdisj) p).symm
  have hcoe : ⇑(QuotientGroup.quotientKerEquivOfSurjective (centralProdHom (d := d) hS hT hdisj)
      (centralProdHom_surjective hS hT hdisj hcov))
      = QuotientGroup.kerLift (centralProdHom (d := d) hS hT hdisj) := rfl
  rw [h1, QuotientGroup.congr_mk, hcoe, QuotientGroup.kerLift_mk]

/-- `cliffordAutExtend φ` is again a Clifford automorphism: it fixes every phase. -/
lemma cliffordAutExtend_mem_cliffordAutGroup (hS : S.carrier ⊆ U.carrier) (hT : T.carrier ⊆ U.carrier)
    (hdisj : Disjoint S.carrier T.carrier) (hcov : U.carrier ⊆ S.carrier ∪ T.carrier)
    (φ : CliffordAutGroup ↥S.carrier d) (c : ZMod d) :
    (cliffordAutExtend hS hT hdisj hcov φ) (phaseGen c) = phaseGen c := by
  have hpc : phaseGen c = centralProdHom hS hT hdisj (phaseGen c, 1) := by
    rw [centralProdHom_apply, quditInclusionHom_phaseGen, map_one, mul_one]
  rw [hpc, cliffordAutExtend_centralProdHom_apply, prodExtend_apply, φ.2 c, centralProdHom_apply,
    quditInclusionHom_phaseGen, map_one, mul_one]

/-- `cliffordAutExtend φ` is natural with respect to `quditInclusionHom`: on points supported on
`S` (embedded into `U`), it acts exactly as `φ` does on `S`, embedded back. -/
lemma cliffordAutExtend_quditInclusionHom (hS : S.carrier ⊆ U.carrier) (hT : T.carrier ⊆ U.carrier)
    (hdisj : Disjoint S.carrier T.carrier) (hcov : U.carrier ⊆ S.carrier ∪ T.carrier)
    (φ : CliffordAutGroup ↥S.carrier d) (x : PauliGroup ↥S.carrier d) :
    cliffordAutExtend hS hT hdisj hcov φ (quditInclusionHom hS x) = quditInclusionHom hS (φ.1 x) := by
  have hx : quditInclusionHom hS x = centralProdHom hS hT hdisj (x, 1) := by
    rw [centralProdHom_apply, map_one, mul_one]
  rw [hx, cliffordAutExtend_centralProdHom_apply, prodExtend_apply, centralProdHom_apply, map_one,
    mul_one]

/-- `cliffordAutExtend` sends the identity Clifford automorphism to the identity. -/
lemma cliffordAutExtend_one (hS : S.carrier ⊆ U.carrier) (hT : T.carrier ⊆ U.carrier)
    (hdisj : Disjoint S.carrier T.carrier) (hcov : U.carrier ⊆ S.carrier ∪ T.carrier) :
    cliffordAutExtend (d := d) hS hT hdisj hcov 1 = 1 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨p, rfl⟩ := centralProdHom_surjective hS hT hdisj hcov x
  simp only [cliffordAutExtend_centralProdHom_apply, prodExtend_apply, Subgroup.coe_one,
    MulAut.one_apply]

/-- `cliffordAutExtend` is multiplicative: extending a product of Clifford automorphisms is the
product of the extensions. -/
lemma cliffordAutExtend_mul (hS : S.carrier ⊆ U.carrier) (hT : T.carrier ⊆ U.carrier)
    (hdisj : Disjoint S.carrier T.carrier) (hcov : U.carrier ⊆ S.carrier ∪ T.carrier)
    (φ ψ : CliffordAutGroup ↥S.carrier d) :
    cliffordAutExtend hS hT hdisj hcov (φ * ψ)
      = cliffordAutExtend hS hT hdisj hcov φ * cliffordAutExtend hS hT hdisj hcov ψ := by
  apply MulEquiv.ext
  intro x
  obtain ⟨p, rfl⟩ := centralProdHom_surjective hS hT hdisj hcov x
  simp only [MulAut.mul_apply, cliffordAutExtend_centralProdHom_apply, prodExtend_apply,
    Subgroup.coe_mul]

/-- `cliffordAutExtend` is injective: an extension determines the original automorphism, since it
can be recovered by restricting back to `S` via `quditInclusionHom` (itself injective). -/
lemma cliffordAutExtend_injective (hS : S.carrier ⊆ U.carrier) (hT : T.carrier ⊆ U.carrier)
    (hdisj : Disjoint S.carrier T.carrier) (hcov : U.carrier ⊆ S.carrier ∪ T.carrier) :
    Function.Injective (cliffordAutExtend (d := d) hS hT hdisj hcov) := by
  intro φ ψ heq
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  have h1 : cliffordAutExtend hS hT hdisj hcov φ (quditInclusionHom hS x)
      = cliffordAutExtend hS hT hdisj hcov ψ (quditInclusionHom hS x) := by rw [heq]
  rw [cliffordAutExtend_quditInclusionHom, cliffordAutExtend_quditInclusionHom] at h1
  exact quditInclusionHom_injective hS h1

/-- `cliffordAutExtend φ` fixes every point supported purely on the complement `T`, regardless of
`φ`: it only ever twists the `S`-part. -/
lemma cliffordAutExtend_fixes_complement (hS : S.carrier ⊆ U.carrier) (hT : T.carrier ⊆ U.carrier)
    (hdisj : Disjoint S.carrier T.carrier) (hcov : U.carrier ⊆ S.carrier ∪ T.carrier)
    (φ : CliffordAutGroup ↥S.carrier d) (y : PauliGroup ↥T.carrier d) :
    cliffordAutExtend hS hT hdisj hcov φ (quditInclusionHom hT y) = quditInclusionHom hT y := by
  have hy : quditInclusionHom hT y = centralProdHom hS hT hdisj (1, y) := by
    rw [centralProdHom_apply, map_one, one_mul]
  rw [hy, cliffordAutExtend_centralProdHom_apply, prodExtend_apply, map_one, centralProdHom_apply,
    map_one, one_mul]

/-- `cliffordAutExtend φ` fixes every point supported on *any* region `R` disjoint from `S` — not
just the specific complement `T` it was built with: since `R ⊆ U ⊆ S ∪ T` and `R` is disjoint
from `S`, `R ⊆ T`, so a point supported on `R` is in particular supported on `T`, hence fixed by
`cliffordAutExtend_fixes_complement`. -/
lemma cliffordAutExtend_fixes_disjoint (hS : S.carrier ⊆ U.carrier) (hT : T.carrier ⊆ U.carrier)
    (hdisj : Disjoint S.carrier T.carrier) (hcov : U.carrier ⊆ S.carrier ∪ T.carrier)
    (φ : CliffordAutGroup ↥S.carrier d) {R : RegionCat X} (hR : R.carrier ⊆ U.carrier)
    (hdisjR : Disjoint S.carrier R.carrier) (z : PauliGroup ↥R.carrier d) :
    cliffordAutExtend hS hT hdisj hcov φ (quditInclusionHom hR z) = quditInclusionHom hR z := by
  have hRT : R.carrier ⊆ T.carrier := fun a ha =>
    (Finset.mem_union.mp (hcov (hR ha))).resolve_left (Finset.disjoint_left.mp hdisjR.symm ha)
  have e : quditInclusionHom hR z = quditInclusionHom hT (quditInclusionHom hRT z) := by
    rw [← MonoidHom.comp_apply, ← quditInclusionHom_trans hRT hT]
  rw [e]
  exact cliffordAutExtend_fixes_complement hS hT hdisj hcov φ (quditInclusionHom hRT z)

end CentralProduct

/-! ### The Clifford automorphism functor

Specializing `cliffordAutExtend` to `T := ↥(U.carrier \ S.carrier)`, the canonical complement of
`S` inside any `U ⊇ S`, turns "extend a Clifford automorphism trivially onto new qudits" into a
functor `RegionCat X ⥤ GrpInclCat` sending a region to its Clifford automorphism group. -/

section Functor

variable {X : Type u} [DecidableEq X] {d : ℕ}

private lemma complementDisjoint {S T : RegionCat X} (_h : S.carrier ⊆ T.carrier) :
    Disjoint S.carrier (T.carrier \ S.carrier) := disjoint_sdiff_self_right

private lemma complementCov {S T : RegionCat X} (h : S.carrier ⊆ T.carrier) :
    T.carrier ⊆ S.carrier ∪ (T.carrier \ S.carrier) := (Finset.union_sdiff_of_subset h).ge

/-- Extend a Clifford automorphism along a region inclusion `S.carrier ⊆ T.carrier`, acting
trivially on the complementary qudits `T.carrier \ S.carrier`. -/
noncomputable def cliffordAutInclusionHom {S T : RegionCat X} (h : S.carrier ⊆ T.carrier) :
    CliffordAutGroup ↥S.carrier d →* CliffordAutGroup ↥T.carrier d where
  toFun φ := ⟨cliffordAutExtend h Finset.sdiff_subset (complementDisjoint h) (complementCov h) φ,
    cliffordAutExtend_mem_cliffordAutGroup h Finset.sdiff_subset (complementDisjoint h)
      (complementCov h) φ⟩
  map_one' := Subtype.ext
    (cliffordAutExtend_one h Finset.sdiff_subset (complementDisjoint h) (complementCov h))
  map_mul' φ ψ := Subtype.ext
    (cliffordAutExtend_mul h Finset.sdiff_subset (complementDisjoint h) (complementCov h) φ ψ)

private lemma cliffordAutInclusionHom_apply {S T : RegionCat X} (h : S.carrier ⊆ T.carrier)
    (φ : CliffordAutGroup ↥S.carrier d) :
    (cliffordAutInclusionHom h φ).1
      = cliffordAutExtend h Finset.sdiff_subset (complementDisjoint h) (complementCov h) φ := rfl

/-- `cliffordAutExtend` doesn't actually depend on which valid complement `(T, hT, hdisj, hcov)` it
is built with: it always agrees with `cliffordAutInclusionHom`, which fixes the canonical
complement `T.carrier \ S.carrier`. Proved by decomposing an arbitrary point via `hS`/`hT` and
checking the two sides agree on each piece (`cliffordAutExtend_quditInclusionHom` on the `S`-part,
`cliffordAutExtend_fixes_disjoint` on the `T`-part). -/
lemma cliffordAutExtend_eq_cliffordAutInclusionHom {S T U : RegionCat X} (hS : S.carrier ⊆ U.carrier)
    (hT : T.carrier ⊆ U.carrier) (hdisj : Disjoint S.carrier T.carrier)
    (hcov : U.carrier ⊆ S.carrier ∪ T.carrier) (φ : CliffordAutGroup ↥S.carrier d) :
    cliffordAutExtend hS hT hdisj hcov φ = (cliffordAutInclusionHom hS φ).1 := by
  apply MulEquiv.ext
  intro z
  obtain ⟨⟨x, y⟩, rfl⟩ := centralProdHom_surjective hS hT hdisj hcov z
  rw [cliffordAutExtend_centralProdHom_apply, prodExtend_apply, centralProdHom_apply,
    centralProdHom_apply, map_mul, cliffordAutInclusionHom_apply, cliffordAutExtend_quditInclusionHom,
    cliffordAutExtend_fixes_disjoint hS Finset.sdiff_subset (complementDisjoint hS)
      (complementCov hS) φ hT hdisj y]

lemma cliffordAutInclusionHom_injective {S T : RegionCat X} (h : S.carrier ⊆ T.carrier) :
    Function.Injective (cliffordAutInclusionHom (d := d) h) := by
  intro φ ψ heq
  apply cliffordAutExtend_injective h Finset.sdiff_subset (complementDisjoint h) (complementCov h)
  rw [← cliffordAutInclusionHom_apply, ← cliffordAutInclusionHom_apply, heq]

/-- `cliffordAutInclusionHom` turns composition of region inclusions into composition of
homomorphisms. The key extra fact needed beyond `CentralProduct` (where everything is about a
single split of one ambient region into two disjoint pieces) is that extending along `S ⊆ T ⊆ U`
in two steps agrees with extending along `S ⊆ U` directly: writing `U \ S` as the disjoint union
of `T \ S` and `U \ T`, the two-step extension fixes the `T \ S` part (since the first step
already fixes it) and the `U \ T` part (since the second step fixes its own complement), so it
agrees with the direct extension on all of `U \ S`, and both agree (naturally) on `S`. -/
lemma cliffordAutInclusionHom_trans {S T U : RegionCat X} (hf : S.carrier ⊆ T.carrier)
    (hg : T.carrier ⊆ U.carrier) :
    cliffordAutInclusionHom (d := d) (hf.trans hg)
      = (cliffordAutInclusionHom hg).comp (cliffordAutInclusionHom hf) := by
  have h1 : T.carrier \ S.carrier ⊆ U.carrier \ S.carrier :=
    Finset.sdiff_subset_sdiff hg (Finset.Subset.refl S.carrier)
  have h2 : U.carrier \ T.carrier ⊆ U.carrier \ S.carrier :=
    Finset.sdiff_subset_sdiff (Finset.Subset.refl U.carrier) hf
  have hdisj12 : Disjoint (T.carrier \ S.carrier) (U.carrier \ T.carrier) :=
    Disjoint.mono_left Finset.sdiff_subset disjoint_sdiff_self_right
  have hcov12 : U.carrier \ S.carrier ⊆ (T.carrier \ S.carrier) ∪ (U.carrier \ T.carrier) := by
    intro a ha
    rw [Finset.mem_sdiff] at ha
    by_cases haT : a ∈ T.carrier
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨haT, ha.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ha.1, haT⟩)
  have e1 : ∀ v : PauliGroup ↥(T.carrier \ S.carrier) d,
      quditInclusionHom (Finset.sdiff_subset : U.carrier \ S.carrier ⊆ U.carrier)
          (quditInclusionHom h1 v)
        = quditInclusionHom hg
            (quditInclusionHom (Finset.sdiff_subset : T.carrier \ S.carrier ⊆ T.carrier) v) := by
    intro v
    rw [← MonoidHom.comp_apply, ← quditInclusionHom_trans, ← MonoidHom.comp_apply,
      ← quditInclusionHom_trans]
  have e2 : ∀ w2 : PauliGroup ↥(U.carrier \ T.carrier) d,
      quditInclusionHom (Finset.sdiff_subset : U.carrier \ S.carrier ⊆ U.carrier)
          (quditInclusionHom h2 w2)
        = quditInclusionHom (Finset.sdiff_subset : U.carrier \ T.carrier ⊆ U.carrier) w2 := by
    intro w2
    rw [← MonoidHom.comp_apply, ← quditInclusionHom_trans]
  apply MonoidHom.ext
  intro φ
  apply Subtype.ext
  rw [cliffordAutInclusionHom_apply, MonoidHom.comp_apply, cliffordAutInclusionHom_apply]
  have hfix : ∀ w : PauliGroup ↥(U.carrier \ S.carrier) d,
      cliffordAutExtend hg (Finset.sdiff_subset : U.carrier \ T.carrier ⊆ U.carrier)
          (complementDisjoint hg) (complementCov hg)
          (cliffordAutInclusionHom hf φ)
          (quditInclusionHom (Finset.sdiff_subset : U.carrier \ S.carrier ⊆ U.carrier) w)
        = quditInclusionHom (Finset.sdiff_subset : U.carrier \ S.carrier ⊆ U.carrier) w := by
    intro w
    obtain ⟨⟨v, w2⟩, rfl⟩ := centralProdHom_surjective h1 h2 hdisj12 hcov12 w
    rw [centralProdHom_apply, map_mul, e1, e2, map_mul,
      cliffordAutExtend_quditInclusionHom, cliffordAutInclusionHom_apply,
      cliffordAutExtend_fixes_complement, cliffordAutExtend_fixes_complement]
  apply MulEquiv.ext
  intro z
  obtain ⟨⟨x, w⟩, rfl⟩ := centralProdHom_surjective (hf.trans hg) Finset.sdiff_subset
    (complementDisjoint (hf.trans hg)) (complementCov (hf.trans hg)) z
  have hLHS : cliffordAutExtend (hf.trans hg) Finset.sdiff_subset (complementDisjoint (hf.trans hg))
      (complementCov (hf.trans hg)) φ
      (centralProdHom (hf.trans hg) Finset.sdiff_subset (complementDisjoint (hf.trans hg)) (x, w))
      = quditInclusionHom hg (quditInclusionHom hf (φ.1 x))
        * quditInclusionHom (Finset.sdiff_subset : U.carrier \ S.carrier ⊆ U.carrier) w := by
    rw [cliffordAutExtend_centralProdHom_apply, prodExtend_apply, centralProdHom_apply,
      quditInclusionHom_trans, MonoidHom.comp_apply]
  have hRHS : cliffordAutExtend hg (Finset.sdiff_subset : U.carrier \ T.carrier ⊆ U.carrier)
      (complementDisjoint hg) (complementCov hg) (cliffordAutInclusionHom hf φ)
      (centralProdHom (hf.trans hg) Finset.sdiff_subset (complementDisjoint (hf.trans hg)) (x, w))
      = quditInclusionHom hg (quditInclusionHom hf (φ.1 x))
        * quditInclusionHom (Finset.sdiff_subset : U.carrier \ S.carrier ⊆ U.carrier) w := by
    rw [centralProdHom_apply, map_mul]
    dsimp only
    rw [hfix, quditInclusionHom_trans hf hg, MonoidHom.comp_apply, cliffordAutExtend_quditInclusionHom,
      cliffordAutInclusionHom_apply, cliffordAutExtend_quditInclusionHom]
  rw [hLHS, hRHS]

/-- `cliffordAutInclusionHom` sends the trivial inclusion to the identity homomorphism: the first
functor law. -/
lemma cliffordAutInclusionHom_refl {S : RegionCat X} :
    cliffordAutInclusionHom (d := d) (Finset.Subset.refl S.carrier)
      = MonoidHom.id (CliffordAutGroup ↥S.carrier d) := by
  apply MonoidHom.ext
  intro φ
  apply Subtype.ext
  rw [cliffordAutInclusionHom_apply, MonoidHom.id_apply]
  apply MulEquiv.ext
  intro x
  have hnat := cliffordAutExtend_quditInclusionHom (Finset.Subset.refl S.carrier)
    Finset.sdiff_subset (complementDisjoint (Finset.Subset.refl S.carrier))
    (complementCov (Finset.Subset.refl S.carrier)) φ x
  rwa [quditInclusionHom_refl, MonoidHom.id_apply, MonoidHom.id_apply] at hnat

/-- The functor sending a finite region of qudits to its Clifford automorphism group, and a region inclusion
to the induced "extend trivially on the complement" homomorphism. -/
noncomputable def cliffordAutInclusionFunctor (X : Type u) [DecidableEq X] (d : ℕ) :
    RegionCat X ⥤ GrpInclCat.{u} where
  obj S := GrpInclCat.of (CliffordAutGroup ↥S.carrier d)
  map {S T} f := GrpInclCat.homOfInjective
    (cliffordAutInclusionHom (d := d) (RegionCat.subsetOfHom f))
    (cliffordAutInclusionHom_injective (RegionCat.subsetOfHom f))
  map_id S := by
    apply Subtype.ext
    show cliffordAutInclusionHom (d := d) (RegionCat.subsetOfHom (𝟙 S))
        = MonoidHom.id (CliffordAutGroup ↥S.carrier d)
    rw [show RegionCat.subsetOfHom (𝟙 S) = Finset.Subset.refl S.carrier from rfl,
      cliffordAutInclusionHom_refl]
  map_comp {S T U} f g := by
    apply Subtype.ext
    show cliffordAutInclusionHom (d := d) (RegionCat.subsetOfHom (f ≫ g))
        = (cliffordAutInclusionHom (d := d) (RegionCat.subsetOfHom g)).comp
          (cliffordAutInclusionHom (d := d) (RegionCat.subsetOfHom f))
    rw [show RegionCat.subsetOfHom (f ≫ g)
          = Finset.Subset.trans (RegionCat.subsetOfHom f) (RegionCat.subsetOfHom g) from rfl,
      cliffordAutInclusionHom_trans (RegionCat.subsetOfHom f) (RegionCat.subsetOfHom g)]

/-- Clifford automorphisms extended from disjoint regions `S`, `T` (covering, together, a common
region `U`) commute: each fixes the other's support (`cliffordAutExtend_fixes_disjoint`), and the
underlying Pauli group elements they twist commute in the first place
(`commute_of_disjoint_range`). -/
lemma commute_of_disjoint_cliffordAutInclusionHom {S T U : RegionCat X} (hS : S.carrier ⊆ U.carrier)
    (hT : T.carrier ⊆ U.carrier) (hdisj : Disjoint S.carrier T.carrier)
    (hcov : U.carrier ⊆ S.carrier ∪ T.carrier) (φ : CliffordAutGroup ↥S.carrier d)
    (ψ : CliffordAutGroup ↥T.carrier d) :
    Commute (cliffordAutInclusionHom hS φ) (cliffordAutInclusionHom hT ψ) := by
  have hcov' : U.carrier ⊆ T.carrier ∪ S.carrier := by rw [Finset.union_comm]; exact hcov
  apply Subtype.ext
  show (cliffordAutInclusionHom hS φ).1 * (cliffordAutInclusionHom hT ψ).1
      = (cliffordAutInclusionHom hT ψ).1 * (cliffordAutInclusionHom hS φ).1
  rw [← cliffordAutExtend_eq_cliffordAutInclusionHom hS hT hdisj hcov,
    ← cliffordAutExtend_eq_cliffordAutInclusionHom hT hS hdisj.symm hcov']
  apply MulEquiv.ext
  intro z
  obtain ⟨⟨x, y⟩, rfl⟩ := centralProdHom_surjective hS hT hdisj hcov z
  have hswap : ∀ (a : PauliGroup ↥S.carrier d) (b : PauliGroup ↥T.carrier d),
      centralProdHom hS hT hdisj (a, b) = centralProdHom hT hS hdisj.symm (b, a) := by
    intro a b
    rw [centralProdHom_apply, centralProdHom_apply]
    exact commute_of_disjoint_range hS hT hdisj a b
  have hLHS : (cliffordAutExtend hS hT hdisj hcov φ * cliffordAutExtend hT hS hdisj.symm hcov' ψ)
      (centralProdHom hS hT hdisj (x, y))
      = quditInclusionHom hS (φ.1 x) * quditInclusionHom hT (ψ.1 y) := by
    have step1 : cliffordAutExtend hT hS hdisj.symm hcov' ψ (centralProdHom hS hT hdisj (x, y))
        = centralProdHom hT hS hdisj.symm (ψ.1 y, x) := by
      rw [hswap x y, cliffordAutExtend_centralProdHom_apply, prodExtend_apply]
    have step2 : centralProdHom hT hS hdisj.symm (ψ.1 y, x) = centralProdHom hS hT hdisj (x, ψ.1 y) :=
      (hswap x (ψ.1 y)).symm
    rw [MulAut.mul_apply, step1, step2, cliffordAutExtend_centralProdHom_apply, prodExtend_apply,
      centralProdHom_apply]
  have hRHS : (cliffordAutExtend hT hS hdisj.symm hcov' ψ * cliffordAutExtend hS hT hdisj hcov φ)
      (centralProdHom hS hT hdisj (x, y))
      = quditInclusionHom hT (ψ.1 y) * quditInclusionHom hS (φ.1 x) := by
    have step1 : cliffordAutExtend hS hT hdisj hcov φ (centralProdHom hS hT hdisj (x, y))
        = centralProdHom hS hT hdisj (φ.1 x, y) := by
      rw [cliffordAutExtend_centralProdHom_apply, prodExtend_apply]
    have step2 : centralProdHom hS hT hdisj (φ.1 x, y) = centralProdHom hT hS hdisj.symm (y, φ.1 x) :=
      hswap (φ.1 x) y
    rw [MulAut.mul_apply, step1, step2, cliffordAutExtend_centralProdHom_apply, prodExtend_apply,
      centralProdHom_apply]
  rw [hLHS, hRHS]
  exact commute_of_disjoint_range hS hT hdisj (φ.1 x) (ψ.1 y)

end Functor

end PauliGroup
