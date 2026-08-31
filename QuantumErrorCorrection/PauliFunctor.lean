/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import QuantumErrorCorrection.Pauli
public import QuantumErrorCorrection.RegionCat
public import QuantumErrorCorrection.GrpInclCat
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# `PauliGroup` is a functor from finite regions and inclusions to groups

Fixing a site set `X` (the possible qudit labels) and a qudit dimension `d`, extending a Pauli
element on a smaller region of qudits to a larger one by acting trivially (as the identity) on
the new qudits gives a functor

  `PauliGroup.quditInclusionFunctor X d : RegionCat X ⥤ GrpInclCat`

from `RegionCat X` (see `RegionCat.lean`), the category `B(X)` of finite regions of `X` ordered
by inclusion, to `GrpInclCat` (see `GrpInclCat.lean`), the category of groups and *injective*
homomorphisms — not Mathlib's `GrpCat`, whose morphisms are arbitrary group homomorphisms: every
`quditInclusionHom` really is injective (extending by zero on the new qudits loses no
information), so the functor's target correctly records this. On objects it sends a region
`S ↦ PauliGroup ↥S.carrier d`, and on a region inclusion `S.carrier ⊆ T.carrier` it sends a
Pauli element to the one with the same phase, and shift/clock exponent vectors extended by `0`
outside `S`.

Everything in this file besides `quditInclusionFunctor`, `quditInclusionHom`, and
`commute_of_disjoint_range` is private plumbing: a generic "extend along an arbitrary
embedding" construction (`extendAlong`/`quditHomOfEmbedding`) that isn't tied to `RegionCat` at
all, specialized to region inclusions only at the very end via `regionInclusionEmbedding`.
-/

public section

open CategoryTheory

universe u

namespace PauliGroup

/-! ### Generic plumbing: extending along an arbitrary embedding of qudit sets

None of this section refers to `RegionCat`; it is reused below to build the region-indexed
`quditInclusionHom` and `quditInclusionFunctor`. -/

variable {d : ℕ}

/-- Extend a vector of exponents along an arbitrary embedding, padding with `0` outside the
image. Public: reused by later files (e.g. the Clifford-group functor) building further
"combine along disjoint regions" constructions on top of the region-inclusion machinery below. -/
public noncomputable def extendAlong {α β : Type u} (f : α ↪ β) (a : α → ZMod d) :
    β → ZMod d :=
  Function.extend f a 0

public lemma extendAlong_apply {α β : Type u} (f : α ↪ β) (a : α → ZMod d) (i : α) :
    extendAlong f a (f i) = a i :=
  f.injective.extend_apply a 0 i

public lemma extendAlong_apply_of_not_mem_range {α β : Type u} (f : α ↪ β) (a : α → ZMod d)
    {j : β} (hj : j ∉ Set.range f) : extendAlong f a j = 0 := by
  apply Function.extend_apply'
  simpa using hj

public lemma extendAlong_zero {α β : Type u} (f : α ↪ β) :
    extendAlong f (0 : α → ZMod d) = 0 := by
  ext j
  by_cases hj : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hj
    simp [extendAlong_apply]
  · simp [extendAlong_apply_of_not_mem_range f 0 hj]

private lemma extendAlong_add {α β : Type u} (f : α ↪ β) (a b : α → ZMod d) :
    extendAlong f (a + b) = extendAlong f a + extendAlong f b := by
  ext j
  by_cases hj : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hj
    simp [extendAlong_apply]
  · simp [extendAlong_apply_of_not_mem_range f a hj, extendAlong_apply_of_not_mem_range f b hj,
      extendAlong_apply_of_not_mem_range f (a + b) hj]

private lemma extendAlong_refl {α : Type u} (a : α → ZMod d) :
    extendAlong (Function.Embedding.refl α) a = a := by
  show Function.extend (⇑(Function.Embedding.refl α)) a 0 = a
  rw [Function.Embedding.coe_refl]
  exact Function.extend_id a 0

private lemma extendAlong_trans {α β γ : Type u} (f : α ↪ β) (g : β ↪ γ) (a : α → ZMod d) :
    extendAlong (f.trans g) a = extendAlong g (extendAlong f a) := by
  ext k
  by_cases hk : k ∈ Set.range g
  · obtain ⟨j, rfl⟩ := hk
    by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      have hL : extendAlong (f.trans g) a (g (f i)) = a i := extendAlong_apply (f.trans g) a i
      have hR : extendAlong g (extendAlong f a) (g (f i)) = a i := by
        rw [extendAlong_apply, extendAlong_apply]
      rw [hL, hR]
    · have hjk : g j ∉ Set.range (f.trans g) := by
        rintro ⟨i, hi⟩
        exact hj ⟨i, g.injective hi⟩
      have hL : extendAlong (f.trans g) a (g j) = 0 :=
        extendAlong_apply_of_not_mem_range (f.trans g) a hjk
      have hR : extendAlong g (extendAlong f a) (g j) = 0 := by
        rw [extendAlong_apply, extendAlong_apply_of_not_mem_range f a hj]
      rw [hL, hR]
  · have hk' : k ∉ Set.range (f.trans g) := by
      rintro ⟨i, hi⟩
      exact hk ⟨f i, hi⟩
    rw [extendAlong_apply_of_not_mem_range g _ hk,
      extendAlong_apply_of_not_mem_range (f.trans g) a hk']

private lemma pairing_extendAlong {α β : Type u} [Fintype α] [Fintype β] (f : α ↪ β)
    (a b : α → ZMod d) : pairing (extendAlong f a) (extendAlong f b) = pairing a b := by
  have hsub : ∑ j ∈ (Finset.univ.map f), extendAlong f a j * extendAlong f b j
      = ∑ j : β, extendAlong f a j * extendAlong f b j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hj' : j ∉ Set.range f := by simpa using hj
    rw [extendAlong_apply_of_not_mem_range f a hj', extendAlong_apply_of_not_mem_range f b hj',
      mul_zero]
  simp only [pairing, ← hsub, Finset.sum_map, extendAlong_apply]

public noncomputable def quditHomOfEmbedding {α β : Type u} [Fintype α] [Fintype β] (f : α ↪ β) :
    PauliGroup α d →* PauliGroup β d where
  toFun g := ⟨g.phase, extendAlong f g.shift, extendAlong f g.clock⟩
  map_one' := by ext <;> simp [extendAlong_zero]
  map_mul' g h := by
    ext
    · simp [pairing_extendAlong]
    · simp [extendAlong_add]
    · simp [extendAlong_add]

private lemma quditHomOfEmbedding_apply_phase {α β : Type u} [Fintype α] [Fintype β] (f : α ↪ β)
    (g : PauliGroup α d) : (quditHomOfEmbedding f g).phase = g.phase := rfl

private lemma quditHomOfEmbedding_apply_shift {α β : Type u} [Fintype α] [Fintype β] (f : α ↪ β)
    (g : PauliGroup α d) : (quditHomOfEmbedding f g).shift = extendAlong f g.shift := rfl

private lemma quditHomOfEmbedding_apply_clock {α β : Type u} [Fintype α] [Fintype β] (f : α ↪ β)
    (g : PauliGroup α d) : (quditHomOfEmbedding f g).clock = extendAlong f g.clock := rfl

private lemma quditHomOfEmbedding_injective {α β : Type u} [Fintype α] [Fintype β] (f : α ↪ β) :
    Function.Injective (quditHomOfEmbedding (d := d) f) := by
  intro g1 g2 heq
  have hphase : g1.phase = g2.phase := by
    simpa [quditHomOfEmbedding_apply_phase] using congrArg PauliGroup.phase heq
  have hshift : g1.shift = g2.shift := by
    have hh := congrArg PauliGroup.shift heq
    simp only [quditHomOfEmbedding_apply_shift] at hh
    funext i
    simpa [extendAlong_apply] using congrFun hh (f i)
  have hclock : g1.clock = g2.clock := by
    have hh := congrArg PauliGroup.clock heq
    simp only [quditHomOfEmbedding_apply_clock] at hh
    funext i
    simpa [extendAlong_apply] using congrFun hh (f i)
  exact PauliGroup.ext hphase hshift hclock

private lemma quditHomOfEmbedding_refl {α : Type u} [Fintype α] :
    quditHomOfEmbedding (Function.Embedding.refl α) = MonoidHom.id (PauliGroup α d) := by
  ext g <;> simp [quditHomOfEmbedding_apply_phase, quditHomOfEmbedding_apply_shift,
    quditHomOfEmbedding_apply_clock, extendAlong_refl]

private lemma quditHomOfEmbedding_trans {α β γ : Type u} [Fintype α] [Fintype β] [Fintype γ]
    (f : α ↪ β) (g : β ↪ γ) :
    quditHomOfEmbedding (f.trans g)
      = (quditHomOfEmbedding g : PauliGroup β d →* PauliGroup γ d).comp
        (quditHomOfEmbedding f) := by
  ext x <;> simp [quditHomOfEmbedding_apply_phase, quditHomOfEmbedding_apply_shift,
    quditHomOfEmbedding_apply_clock, extendAlong_trans]

public lemma pairing_extendAlong_of_disjoint {α β γ : Type u} [Fintype β] [Fintype γ]
    (iA : α ↪ γ) (iB : β ↪ γ) (hAB : Disjoint (Set.range iA) (Set.range iB))
    (a : α → ZMod d) (b : β → ZMod d) :
    pairing (extendAlong iA a) (extendAlong iB b) = 0 := by
  unfold pairing
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k ∈ Set.range iA
  · rw [extendAlong_apply_of_not_mem_range iB b (Set.disjoint_left.mp hAB hk), mul_zero]
  · rw [extendAlong_apply_of_not_mem_range iA a hk, zero_mul]

private lemma commute_of_disjoint_embeddings {α β γ : Type u} [Fintype α] [Fintype β]
    [Fintype γ] (iA : α ↪ γ) (iB : β ↪ γ) (hAB : Disjoint (Set.range iA) (Set.range iB))
    (g : PauliGroup α d) (h : PauliGroup β d) :
    Commute (quditHomOfEmbedding iA g) (quditHomOfEmbedding iB h) := by
  show quditHomOfEmbedding iA g * quditHomOfEmbedding iB h
      = quditHomOfEmbedding iB h * quditHomOfEmbedding iA g
  ext
  · simp only [mul_phase, quditHomOfEmbedding_apply_phase, quditHomOfEmbedding_apply_shift,
      quditHomOfEmbedding_apply_clock]
    rw [pairing_extendAlong_of_disjoint iB iA hAB.symm h.shift g.clock,
      pairing_extendAlong_of_disjoint iA iB hAB g.shift h.clock]
    ring
  · simp only [mul_shift, quditHomOfEmbedding_apply_shift, Pi.add_apply]; ring
  · simp only [mul_clock, quditHomOfEmbedding_apply_clock, Pi.add_apply]; ring

/-- The image of `quditHomOfEmbedding f` is always a *normal* subgroup: conjugating a Pauli
element supported (via `f`) on `α` by an arbitrary element of `PauliGroup β d` changes only its
phase, never its shift/clock support, so the conjugate is still in the image. -/
private lemma quditHomOfEmbedding_range_normal {α β : Type u} [Fintype α] [Fintype β]
    (f : α ↪ β) : (MonoidHom.range (quditHomOfEmbedding (d := d) f)).Normal where
  conj_mem n hn g := by
    rw [MonoidHom.mem_range] at hn ⊢
    obtain ⟨x, rfl⟩ := hn
    refine ⟨⟨x.phase + pairing (extendAlong f x.shift) g.clock
        - pairing g.shift (extendAlong f x.clock), x.shift, x.clock⟩, ?_⟩
    ext
    · simp only [quditHomOfEmbedding_apply_phase, quditHomOfEmbedding_apply_shift,
        quditHomOfEmbedding_apply_clock, mul_phase, mul_clock, inv_phase, inv_shift,
        pairing_neg_left, pairing_add_right]
      ring
    · simp only [quditHomOfEmbedding_apply_shift, mul_shift, inv_shift, Pi.add_apply,
        Pi.neg_apply]; ring
    · simp only [quditHomOfEmbedding_apply_clock, mul_clock, inv_clock, Pi.add_apply,
        Pi.neg_apply]; ring

/-! ### The region-indexed API

Everything below is specialized to `RegionCat`: `S T U : RegionCat X` are finite regions of a
fixed site set `X`, and every "embedding of qudit sets" above is instantiated at the inclusion
embedding of one region's qudits into another's. -/

variable {X : Type u}

/-- The embedding of qudit subtypes induced by a region inclusion `S.carrier ⊆ T.carrier`.
Public: reused by later files (e.g. the Clifford-group functor) building further "combine along
disjoint regions" constructions. -/
@[expose] public def regionInclusionEmbedding {S T : RegionCat X} (h : S.carrier ⊆ T.carrier) :
    (↥S.carrier : Type u) ↪ (↥T.carrier : Type u) :=
  Subtype.impEmbedding _ _ fun _ hx => h hx

/-- The coercion of `regionInclusionEmbedding h i` back to `X` is just the coercion of `i`: the
embedding only changes which region's subtype the qudit label lives in, not the label itself.
Public: needed by later files (e.g. the Clifford-group functor) to relate memberships across
regions without unfolding `regionInclusionEmbedding` themselves. -/
public lemma regionInclusionEmbedding_coe {S T : RegionCat X} (h : S.carrier ⊆ T.carrier)
    (i : ↥S.carrier) : (regionInclusionEmbedding h i : X) = (i : X) := rfl

private lemma regionInclusionEmbedding_refl {S : RegionCat X} :
    regionInclusionEmbedding (Finset.Subset.refl S.carrier)
      = Function.Embedding.refl ↥S.carrier := by
  ext x; rfl

private lemma regionInclusionEmbedding_trans {S T U : RegionCat X} (h1 : S.carrier ⊆ T.carrier)
    (h2 : T.carrier ⊆ U.carrier) :
    regionInclusionEmbedding (Finset.Subset.trans h1 h2)
      = (regionInclusionEmbedding h1).trans (regionInclusionEmbedding h2) := by
  ext x; rfl

public lemma mem_range_regionInclusionEmbedding {S T : RegionCat X} (h : S.carrier ⊆ T.carrier)
    (k : ↥T.carrier) : k ∈ Set.range (regionInclusionEmbedding h) ↔ (k : X) ∈ S.carrier := by
  constructor
  · rintro ⟨i, rfl⟩
    exact i.2
  · intro hk
    exact ⟨⟨k, hk⟩, rfl⟩

/-- The group homomorphism induced by a region inclusion `S.carrier ⊆ T.carrier`: extend a
Pauli element by acting trivially on the new qudits, keeping the phase unchanged. -/
public noncomputable def quditInclusionHom {S T : RegionCat X} (h : S.carrier ⊆ T.carrier) :
    PauliGroup ↥S.carrier d →* PauliGroup ↥T.carrier d :=
  quditHomOfEmbedding (regionInclusionEmbedding h)

public lemma quditInclusionHom_apply_phase {S T : RegionCat X} (h : S.carrier ⊆ T.carrier)
    (g : PauliGroup ↥S.carrier d) : (quditInclusionHom h g).phase = g.phase := by
  unfold quditInclusionHom; exact quditHomOfEmbedding_apply_phase _ _

public lemma quditInclusionHom_apply_shift {S T : RegionCat X} (h : S.carrier ⊆ T.carrier)
    (g : PauliGroup ↥S.carrier d) :
    (quditInclusionHom h g).shift = extendAlong (regionInclusionEmbedding h) g.shift := by
  unfold quditInclusionHom; exact quditHomOfEmbedding_apply_shift _ _

public lemma quditInclusionHom_apply_clock {S T : RegionCat X} (h : S.carrier ⊆ T.carrier)
    (g : PauliGroup ↥S.carrier d) :
    (quditInclusionHom h g).clock = extendAlong (regionInclusionEmbedding h) g.clock := by
  unfold quditInclusionHom; exact quditHomOfEmbedding_apply_clock _ _

/-- `quditInclusionHom` fixes every pure phase: extending a Pauli element with no shift/clock
support has nothing to extend. -/
public lemma quditInclusionHom_phaseGen {S T : RegionCat X} (h : S.carrier ⊆ T.carrier)
    (c : ZMod d) : quditInclusionHom h (phaseGen c) = phaseGen c := by
  apply PauliGroup.ext
  · exact quditInclusionHom_apply_phase h (phaseGen c)
  · rw [quditInclusionHom_apply_shift]
    show extendAlong (regionInclusionEmbedding h) 0 = 0
    exact extendAlong_zero _
  · rw [quditInclusionHom_apply_clock]
    show extendAlong (regionInclusionEmbedding h) 0 = 0
    exact extendAlong_zero _

/-- `quditInclusionHom` sends the trivial inclusion to the identity homomorphism: the first
functor law. -/
public lemma quditInclusionHom_refl {S : RegionCat X} :
    quditInclusionHom (Finset.Subset.refl S.carrier) = MonoidHom.id (PauliGroup ↥S.carrier d) := by
  unfold quditInclusionHom
  rw [regionInclusionEmbedding_refl, quditHomOfEmbedding_refl]

/-- `quditInclusionHom` turns composition of region inclusions into composition of
homomorphisms: the second functor law. -/
public lemma quditInclusionHom_trans {S T U : RegionCat X} (h1 : S.carrier ⊆ T.carrier)
    (h2 : T.carrier ⊆ U.carrier) :
    quditInclusionHom (Finset.Subset.trans h1 h2)
      = (quditInclusionHom h2 : PauliGroup ↥T.carrier d →* PauliGroup ↥U.carrier d).comp
        (quditInclusionHom h1) := by
  unfold quditInclusionHom
  rw [regionInclusionEmbedding_trans, quditHomOfEmbedding_trans]

/-- `quditInclusionHom` is always injective: extending by the identity (zero exponents) on the
new qudits loses no information. -/
public lemma quditInclusionHom_injective {S T : RegionCat X} (h : S.carrier ⊆ T.carrier) :
    Function.Injective (quditInclusionHom (d := d) h) :=
  quditHomOfEmbedding_injective (regionInclusionEmbedding h)

/-- The image of `quditInclusionHom h` is always a *normal* subgroup of `PauliGroup ↥T.carrier
d`: conjugating a Pauli element supported on the smaller region `S` by an arbitrary element of
`PauliGroup ↥T.carrier d` changes only its phase, never its shift/clock support (see
`PauliGroup.commutatorElement_eq` in `Pauli.lean` for the same phenomenon at the level of
commutators), so the conjugate is still supported on `S`. -/
public lemma quditInclusionHom_range_normal {S T : RegionCat X} (h : S.carrier ⊆ T.carrier) :
    (MonoidHom.range (quditInclusionHom (d := d) h)).Normal := by
  unfold quditInclusionHom
  exact quditHomOfEmbedding_range_normal (regionInclusionEmbedding h)

/-- The functor sending a finite region of qudits to its Pauli group, and a region inclusion
`S.carrier ⊆ T.carrier` to the induced "extend by the identity" homomorphism of Pauli groups.
Its target is `GrpInclCat`, not the ordinary category of groups, since `quditInclusionHom` is
always injective (`quditInclusionHom_injective`). -/
public noncomputable def quditInclusionFunctor (X : Type u) (d : ℕ) : RegionCat X ⥤ GrpInclCat.{u} where
  obj S := GrpInclCat.of (PauliGroup ↥S.carrier d)
  map {S T} f := GrpInclCat.homOfInjective (quditInclusionHom (d := d) (RegionCat.subsetOfHom f))
    (quditInclusionHom_injective (RegionCat.subsetOfHom f))
  map_id S := by
    apply Subtype.ext
    show quditInclusionHom (d := d) (RegionCat.subsetOfHom (𝟙 S))
        = MonoidHom.id (PauliGroup ↥S.carrier d)
    rw [show RegionCat.subsetOfHom (𝟙 S) = Finset.Subset.refl S.carrier from rfl,
      quditInclusionHom_refl]
  map_comp {S T U} f g := by
    apply Subtype.ext
    show quditInclusionHom (d := d) (RegionCat.subsetOfHom (f ≫ g))
        = (quditInclusionHom (d := d) (RegionCat.subsetOfHom g)).comp
          (quditInclusionHom (d := d) (RegionCat.subsetOfHom f))
    rw [show RegionCat.subsetOfHom (f ≫ g)
          = Finset.Subset.trans (RegionCat.subsetOfHom f) (RegionCat.subsetOfHom g) from rfl,
      quditInclusionHom_trans]

public lemma disjoint_range_regionInclusionEmbedding {S T U : RegionCat X}
    (hS : S.carrier ⊆ U.carrier) (hT : T.carrier ⊆ U.carrier)
    (hdisj : Disjoint S.carrier T.carrier) :
    Disjoint (Set.range (regionInclusionEmbedding hS)) (Set.range (regionInclusionEmbedding hT)) := by
  rw [Set.disjoint_left]
  intro k hkS hkT
  rw [mem_range_regionInclusionEmbedding] at hkS hkT
  exact Finset.disjoint_left.mp hdisj hkS hkT

/-- Pauli elements on disjoint regions commute: if `S` and `T` are disjoint regions both
contained in a common region `U`, their images under `quditInclusionHom` always commute in
`PauliGroup ↥U.carrier d`. Physically: Pauli operators acting on disjoint sets of qudits always
commute, with no leftover phase — the symplectic form itself vanishes here, not just the
operators up to phase (contrast `PauliGroup.commutatorElement_eq` in `Pauli.lean`, where the
commutator phase need not vanish for overlapping qudits). -/
public lemma commute_of_disjoint_range {S T U : RegionCat X} (hS : S.carrier ⊆ U.carrier)
    (hT : T.carrier ⊆ U.carrier) (hdisj : Disjoint S.carrier T.carrier)
    (g : PauliGroup ↥S.carrier d) (h : PauliGroup ↥T.carrier d) :
    Commute (quditInclusionHom hS g) (quditInclusionHom hT h) := by
  show Commute (quditHomOfEmbedding (regionInclusionEmbedding hS) g)
      (quditHomOfEmbedding (regionInclusionEmbedding hT) h)
  exact commute_of_disjoint_embeddings (regionInclusionEmbedding hS) (regionInclusionEmbedding hT)
    (disjoint_range_regionInclusionEmbedding hS hT hdisj) g h

end PauliGroup
