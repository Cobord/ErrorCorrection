import Mathlib.CategoryTheory.Conj
import QuantumErrorCorrection.QCA

/-!
# QCAs modulo circuits, and the commutative monoid of stacking

Everything here holds with `𝕜` an arbitrary commutative `*`-ring and `X` a metric space with
finite closed balls. No normality of circuits is assumed.

* `QCAClass A := QCA A ⧸ circuitSubgroup A`: QCAs on `A` modulo circuits (left cosets). Stacking
  descends to classes (`QCAClass.stack`), because stacking maps circuits to circuits. On a
  finite site set `QCAClass A` is a subsingleton.
* `QCA.transport η`: conjugation by the spread-`0` isomorphism of a net isomorphism `η`. It maps
  layers to layers with the same blocks, hence circuits to circuits
  (`QCA.transport_mem_circuitSubgroup`).
* `QCAStackClass X 𝕜`: pairs `(A, u)` of a system and a QCA on it, identified along net
  isomorphisms modulo circuits. `(A, u) ~ (B, v)` when some net isomorphism `η` has
  `(transport η u)⁻¹ * v` a circuit. Stacking makes this a **commutative monoid**:
  * associativity, unit and commutativity come from transporting along the associator, unitors
    and braiding of nets;
  * the unit is the trivial system with the identity QCA.
-/

noncomputable section

open CategoryTheory MonoidalCategory NNReal RegionCat BoundedSpreadCat

universe u

/-! ### Conjugating tensor products of automorphisms by structural isomorphisms -/

section MonoidalAut

variable {C : Type*} [Category C] [MonoidalCategory C]

theorem conjAut_tensorIso {X X' Y Y' : C} (e : X ≅ X') (f : Y ≅ Y') (u : X ≅ X) (v : Y ≅ Y) :
    (e ⊗ᵢ f).conjAut (u ⊗ᵢ v) = (e.symm ≪≫ u ≪≫ e) ⊗ᵢ (f.symm ≪≫ v ≪≫ f) :=
  (Iso.conjAut_apply _ _).trans (Iso.ext (by
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, tensorIso_inv,
      tensorHom_comp_tensorHom]))

theorem conjAut_associator (X Y Z : C) (u : X ≅ X) (v : Y ≅ Y) (w : Z ≅ Z) :
    (α_ X Y Z).conjAut ((u ⊗ᵢ v) ⊗ᵢ w) = u ⊗ᵢ (v ⊗ᵢ w) :=
  (Iso.conjAut_apply _ _).trans (Iso.ext (by
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, associator_naturality,
      Iso.inv_hom_id_assoc]))

theorem conjAut_leftUnitor (X : C) (u : X ≅ X) :
    (λ_ X).conjAut (Iso.refl (𝟙_ C) ⊗ᵢ u) = u :=
  (Iso.conjAut_apply _ _).trans (Iso.ext (by
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom,
      leftUnitor_naturality, Iso.inv_hom_id_assoc]))

theorem conjAut_rightUnitor (X : C) (u : X ≅ X) :
    (ρ_ X).conjAut (u ⊗ᵢ Iso.refl (𝟙_ C)) = u :=
  (Iso.conjAut_apply _ _).trans (Iso.ext (by
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id,
      rightUnitor_naturality, Iso.inv_hom_id_assoc]))

theorem conjAut_braiding [BraidedCategory C] (X Y : C) (u : X ≅ X) (v : Y ≅ Y) :
    (β_ X Y).conjAut (u ⊗ᵢ v) = v ⊗ᵢ u :=
  (Iso.conjAut_apply _ _).trans (Iso.ext (by
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, BraidedCategory.braiding_naturality,
      Iso.inv_hom_id_assoc]))

end MonoidalAut

variable {X : Type u} [DecidableEq X] [MetricSpace X] [FiniteClosedBalls X]
variable {𝕜 : Type u} [CommRing 𝕜] [StarRing 𝕜]

/-! ### Net isomorphisms as spread-`0` isomorphisms -/

namespace BoundedSpreadCat

variable {A B C D : BoundedSpreadCat X 𝕜}

theorem isoOfNet_refl (A : BoundedSpreadCat X 𝕜) : isoOfNet (Iso.refl A.1.net) = Iso.refl A :=
  Iso.ext rfl

theorem isoOfNet_trans (η : A.1.net ≅ B.1.net) (θ : B.1.net ≅ C.1.net) :
    isoOfNet (η ≪≫ θ) = isoOfNet η ≪≫ isoOfNet θ :=
  Iso.ext (homOfNet_comp η.hom θ.hom).symm

theorem isoOfNet_symm (η : A.1.net ≅ B.1.net) : isoOfNet η.symm = (isoOfNet η).symm :=
  Iso.ext rfl

theorem isoOfNet_tensorIso (η : A.1.net ≅ B.1.net) (θ : C.1.net ≅ D.1.net) :
    isoOfNet (A := A ⊗ C) (A' := B ⊗ D) (η ⊗ᵢ θ) = isoOfNet η ⊗ᵢ isoOfNet θ :=
  Iso.ext (stackHom_homOfNet η.hom θ.hom).symm

end BoundedSpreadCat

/-! ### Transport of QCAs along net isomorphisms -/

namespace QCA

open BoundedSpreadHom

variable {A B C : BoundedSpreadCat X 𝕜}

/-- Transport a QCA along a net isomorphism: conjugation by the corresponding spread-`0`
isomorphism. -/
def transport (η : A.1.net ≅ B.1.net) : QCA A ≃* QCA B := (isoOfNet η).conjAut

theorem transport_refl (u : QCA A) : transport (Iso.refl A.1.net) u = u := by
  rw [transport, isoOfNet_refl]
  ext
  simp [Iso.conjAut_hom, Iso.conj_apply]

theorem transport_trans (η : A.1.net ≅ B.1.net) (θ : B.1.net ≅ C.1.net) (u : QCA A) :
    transport (η ≪≫ θ) u = transport θ (transport η u) := by
  rw [transport, transport, transport, isoOfNet_trans, Iso.trans_conjAut]

theorem transport_symm_transport (η : A.1.net ≅ B.1.net) (u : QCA A) :
    transport η.symm (transport η u) = u := by
  rw [← transport_trans, Iso.self_symm_id, transport_refl]

private lemma transport_hom (η : A.1.net ≅ B.1.net) (u : QCA A) :
    (transport η u).hom = homOfNet η.inv ≫ u.hom ≫ homOfNet η.hom := by
  rw [transport, Iso.conjAut_hom, Iso.conj_apply]
  rfl

private lemma transport_inv (η : A.1.net ≅ B.1.net) (u : QCA A) :
    (transport η u).inv = homOfNet η.inv ≫ u.inv ≫ homOfNet η.hom := by
  rw [transport, Iso.conjAut_apply]
  change ((isoOfNet η).inv ≫ u.inv) ≫ (isoOfNet η).hom = _
  rw [Category.assoc]
  rfl

private lemma preservesRegion_transport (η : A.1.net ≅ B.1.net) {r : ℝ≥0}
    {α : BoundedSpreadHom r A.1 A.1} {R : RegionCat X} (hα : α.PreservesRegion R) :
    ((α.postNet η.hom).preNet η.inv).PreservesRegion R := by
  obtain ⟨γ, hγ⟩ := hα
  refine ⟨η.inv.app R ≫ γ ≫ η.hom.app R, ?_⟩
  rw [preNet_app, postNet_app, hγ]
  simp only [Category.assoc, NatTrans.naturality]

/-- Transporting a layer along a net isomorphism gives a layer with the same blocks. -/
theorem IsLayer.transport {u : QCA A} {r : ℝ≥0} (hu : u.IsLayer r) (η : A.1.net ≅ B.1.net) :
    (QCA.transport η u).IsLayer r := by
  obtain ⟨blocks, hd, α, β, hα, hβ, hR⟩ := hu
  refine ⟨blocks, hd, (α.postNet η.hom).preNet η.inv, (β.postNet η.hom).preNet η.inv, ?_, ?_,
    fun R hRs => ⟨preservesRegion_transport η (hR R hRs).1,
      preservesRegion_transport η (hR R hRs).2⟩⟩
  · rw [transport_hom, ← hα, homMk_comp_homOfNet, homOfNet_comp_homMk]
  · rw [transport_inv, ← hβ, homMk_comp_homOfNet, homOfNet_comp_homMk]

/-- Transport along a net isomorphism maps circuits to circuits. -/
theorem transport_mem_circuitSubgroup (η : A.1.net ≅ B.1.net) {u : QCA A}
    (hu : u ∈ circuitSubgroup A) : transport η u ∈ circuitSubgroup B := by
  have h : circuitSubgroup A ≤ (circuitSubgroup B).comap (transport η).toMonoidHom := by
    rw [circuitSubgroup, Subgroup.closure_le]
    rintro w ⟨r, hw⟩
    exact Subgroup.subset_closure ⟨r, hw.transport η⟩
  exact h hu

theorem transport_stack {A' B' : BoundedSpreadCat X 𝕜} (η : A.1.net ≅ A'.1.net)
    (θ : B.1.net ≅ B'.1.net) (u : QCA A) (v : QCA B) :
    transport (A := A ⊗ B) (B := A' ⊗ B') (η ⊗ᵢ θ) (stackMonoidHom A B (u, v)) =
      stackMonoidHom A' B' (transport η u, transport θ v) :=
  ((congrArg (fun e => Iso.conjAut e (stackMonoidHom A B (u, v))) (isoOfNet_tensorIso η θ)).trans
    (conjAut_tensorIso _ _ u v)).trans
    (congrArg₂ (fun (a : A' ≅ A') (b : B' ≅ B') => a ⊗ᵢ b) (Iso.conjAut_apply _ u).symm
      (Iso.conjAut_apply _ v).symm)

theorem transport_associator (u : QCA A) (v : QCA B) (w : QCA C) :
    transport (A := (A ⊗ B) ⊗ C) (B := A ⊗ (B ⊗ C)) (α_ A.1.net B.1.net C.1.net)
        (stackMonoidHom (A ⊗ B) C (stackMonoidHom A B (u, v), w)) =
      stackMonoidHom A (B ⊗ C) (u, stackMonoidHom B C (v, w)) :=
  conjAut_associator A B C u v w

theorem transport_leftUnitor (u : QCA A) :
    transport (A := 𝟙_ _ ⊗ A) (B := A) (λ_ A.1.net) (stackMonoidHom (𝟙_ _) A (1, u)) = u :=
  conjAut_leftUnitor A u

theorem transport_rightUnitor (u : QCA A) :
    transport (A := A ⊗ 𝟙_ _) (B := A) (ρ_ A.1.net) (stackMonoidHom A (𝟙_ _) (u, 1)) = u :=
  conjAut_rightUnitor A u

theorem transport_braiding (u : QCA A) (v : QCA B) :
    transport (A := A ⊗ B) (B := B ⊗ A) (β_ A.1.net B.1.net) (stackMonoidHom A B (u, v)) =
      stackMonoidHom B A (v, u) :=
  conjAut_braiding A B u v

end QCA

/-! ### QCAs modulo circuits on a fixed system -/

/-- QCAs on `A` modulo circuits: the left cosets `QCA A ⧸ circuitSubgroup A`. -/
abbrev QCAClass (A : BoundedSpreadCat X 𝕜) : Type u := QCA A ⧸ QCA.circuitSubgroup A

namespace QCAClass

open QCA

variable {A B : BoundedSpreadCat X 𝕜}

/-- On a finite site set there is only one class: every QCA is a circuit
(`QCA.mem_circuitSubgroup_of_finite`). -/
instance [Finite X] : Subsingleton (QCAClass A) :=
  ⟨fun a b => Quotient.inductionOn₂' a b fun _ _ =>
    QuotientGroup.eq.2 (mem_circuitSubgroup_of_finite _)⟩

/-- Stacking descends to classes: `[u] ⊗ [v] = [u ⊗ v]`. -/
def stack : QCAClass A → QCAClass B → QCAClass (A ⊗ B) :=
  Quotient.map₂ (sa := QuotientGroup.leftRel (circuitSubgroup A))
    (sb := QuotientGroup.leftRel (circuitSubgroup B))
    (sc := QuotientGroup.leftRel (circuitSubgroup (A ⊗ B)))
    (fun u v => stackMonoidHom A B (u, v)) fun u u' hu v v' hv => by
      refine QuotientGroup.leftRel_apply.2 ?_
      rw [← map_inv, ← map_mul]
      exact stack_mem_circuitSubgroup (QuotientGroup.leftRel_apply.1 hu)
        (QuotientGroup.leftRel_apply.1 hv)

@[simp] theorem stack_mk (u : QCA A) (v : QCA B) :
    stack (QuotientGroup.mk u : QCAClass A) (QuotientGroup.mk v) =
      QuotientGroup.mk (stackMonoidHom A B (u, v)) :=
  rfl

end QCAClass

/-! ### The commutative monoid of QCAs modulo circuits under stacking -/

namespace QCAStackClass

open QCA

variable (X 𝕜) in
/-- Pairs `(A, u)` of a system and a QCA on it, identified along net isomorphisms modulo
circuits: `(A, u) ~ (B, v)` when some net isomorphism `η` has `(transport η u)⁻¹ * v` a
circuit. -/
def setoid : Setoid (Σ A : BoundedSpreadCat X 𝕜, QCA A) where
  r p q := ∃ η : p.1.1.net ≅ q.1.1.net, (transport η p.2)⁻¹ * q.2 ∈ circuitSubgroup q.1
  iseqv :=
    { refl := fun p => ⟨Iso.refl _, by rw [transport_refl, inv_mul_cancel]; exact one_mem _⟩
      symm := fun {p q} ⟨η, h⟩ => ⟨η.symm, by
        have := inv_mem (transport_mem_circuitSubgroup η.symm h)
        rwa [map_mul, map_inv, transport_symm_transport, mul_inv_rev, inv_inv] at this⟩
      trans := fun {p q s} ⟨η, h⟩ ⟨θ, h'⟩ => ⟨η ≪≫ θ, by
        have := mul_mem (transport_mem_circuitSubgroup θ h) h'
        rwa [map_mul, map_inv, mul_assoc, mul_inv_cancel_left, ← transport_trans] at this⟩ }

end QCAStackClass

variable (X 𝕜) in
/-- QCAs modulo circuits across all systems, identified along net isomorphisms. Stacking makes
this a commutative monoid. -/
def QCAStackClass : Type (u + 1) := Quotient (QCAStackClass.setoid X 𝕜)

namespace QCAStackClass

open QCA

/-- The class of a QCA on a system. -/
def mk (A : BoundedSpreadCat X 𝕜) (u : QCA A) : QCAStackClass X 𝕜 :=
  Quotient.mk (setoid X 𝕜) ⟨A, u⟩

/-- Every class of `QCA A ⧸ circuitSubgroup A` gives a class here. -/
def ofQCAClass (A : BoundedSpreadCat X 𝕜) : QCAClass A → QCAStackClass X 𝕜 :=
  Quotient.lift (mk A) fun u v h => Quotient.sound ⟨Iso.refl _, by
    rw [transport_refl]
    exact (QuotientGroup.leftRel_apply).1 h⟩

theorem mk_eq_mk_of_iso {A B : BoundedSpreadCat X 𝕜} (η : A.1.net ≅ B.1.net) (u : QCA A)
    (v : QCA B) (h : transport η u = v) : mk A u = mk B v :=
  Quotient.sound ⟨η, by rw [h, inv_mul_cancel]; exact one_mem _⟩

/-- Stacking of classes. -/
instance : Mul (QCAStackClass X 𝕜) where
  mul := Quotient.map₂ (fun p q => ⟨p.1 ⊗ q.1, stackMonoidHom p.1 q.1 (p.2, q.2)⟩)
    fun _ _ ⟨η, h⟩ _ _ ⟨θ, h'⟩ => ⟨η ⊗ᵢ θ, by
      rw [transport_stack, ← map_inv, ← map_mul]
      exact stack_mem_circuitSubgroup h h'⟩

/-- The trivial system with the identity QCA. -/
instance : One (QCAStackClass X 𝕜) := ⟨mk (𝟙_ _) 1⟩

theorem mk_mul_mk (A B : BoundedSpreadCat X 𝕜) (u : QCA A) (v : QCA B) :
    mk A u * mk B v = mk (A ⊗ B) (stackMonoidHom A B (u, v)) :=
  rfl

theorem exists_mk (x : QCAStackClass X 𝕜) : ∃ (A : BoundedSpreadCat X 𝕜) (u : QCA A), mk A u = x :=
  Quotient.inductionOn x fun p => ⟨p.1, p.2, rfl⟩

private theorem mk_mul_assoc (A B C : BoundedSpreadCat X 𝕜) (u : QCA A) (v : QCA B)
    (w : QCA C) : mk A u * mk B v * mk C w = mk A u * (mk B v * mk C w) := by
  rw [mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_mul_mk]
  exact mk_eq_mk_of_iso (A := (A ⊗ B) ⊗ C) (B := A ⊗ (B ⊗ C)) (α_ A.1.net B.1.net C.1.net)
    (stackMonoidHom (A ⊗ B) C (stackMonoidHom A B (u, v), w))
    (stackMonoidHom A (B ⊗ C) (u, stackMonoidHom B C (v, w))) (transport_associator u v w)

private theorem one_mul_mk (A : BoundedSpreadCat X 𝕜) (u : QCA A) :
    (1 : QCAStackClass X 𝕜) * mk A u = mk A u := by
  change mk (𝟙_ _) 1 * mk A u = mk A u
  rw [mk_mul_mk]
  exact mk_eq_mk_of_iso (A := 𝟙_ _ ⊗ A) (B := A) (λ_ A.1.net)
    (stackMonoidHom (𝟙_ _) A (1, u)) u (transport_leftUnitor u)

private theorem mk_mul_one (A : BoundedSpreadCat X 𝕜) (u : QCA A) :
    mk A u * (1 : QCAStackClass X 𝕜) = mk A u := by
  change mk A u * mk (𝟙_ _) 1 = mk A u
  rw [mk_mul_mk]
  exact mk_eq_mk_of_iso (A := A ⊗ 𝟙_ _) (B := A) (ρ_ A.1.net)
    (stackMonoidHom A (𝟙_ _) (u, 1)) u (transport_rightUnitor u)

private theorem mk_mul_comm (A B : BoundedSpreadCat X 𝕜) (u : QCA A) (v : QCA B) :
    mk A u * mk B v = mk B v * mk A u := by
  rw [mk_mul_mk, mk_mul_mk]
  exact mk_eq_mk_of_iso (A := A ⊗ B) (B := B ⊗ A) (β_ A.1.net B.1.net)
    (stackMonoidHom A B (u, v)) (stackMonoidHom B A (v, u)) (transport_braiding u v)

/-- QCAs modulo circuits, across systems, form a commutative monoid under stacking. -/
instance : CommMonoid (QCAStackClass X 𝕜) where
  mul_assoc x y z := by
    obtain ⟨A, u, rfl⟩ := exists_mk x
    obtain ⟨B, v, rfl⟩ := exists_mk y
    obtain ⟨C, w, rfl⟩ := exists_mk z
    exact mk_mul_assoc A B C u v w
  one_mul x := by
    obtain ⟨A, u, rfl⟩ := exists_mk x
    exact one_mul_mk A u
  mul_one x := by
    obtain ⟨A, u, rfl⟩ := exists_mk x
    exact mk_mul_one A u
  mul_comm x y := by
    obtain ⟨A, u, rfl⟩ := exists_mk x
    obtain ⟨B, v, rfl⟩ := exists_mk y
    exact mk_mul_comm A B u v

/-- The class of a stack is the product of the classes. -/
theorem ofQCAClass_stack {A B : BoundedSpreadCat X 𝕜} (c : QCAClass A) (d : QCAClass B) :
    ofQCAClass (A ⊗ B) (QCAClass.stack c d) = ofQCAClass A c * ofQCAClass B d :=
  Quotient.inductionOn₂ c d fun _ _ => rfl

end QCAStackClass
