import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Transport
import QuantumErrorCorrection.SuperStarTensor

/-!
# `SuperStarAlgCat 𝕜` is monoidal under the super tensor product

The tensor product of two objects is their super tensor product `A ⊗ˢ B` (`SuperTensor`), with
the Koszul-signed multiplication and star. The tensor of two morphisms is `SuperTensor.map`,
and the unit is `𝕜` with the trivial grading. The associator and unitors are
`SuperTensor.assoc`, `SuperTensor.lid` and `SuperTensor.rid`.

The coherence laws (pentagon, triangle, naturality) are not proved by hand. They are induced
along the faithful forgetful functor `SuperStarAlgCat.forgetToModuleCat` to `ModuleCat 𝕜`
(`CategoryTheory.Monoidal.induced`): on underlying modules each structure map is the
corresponding one of `ModuleCat 𝕜`, so each law holds after forgetting, and hence before.
-/

noncomputable section

open CategoryTheory MonoidalCategory SuperStarAlgebra SuperTensor

universe u

namespace SuperStarAlgCat

variable {𝕜 : Type u} [CommRing 𝕜] [StarRing 𝕜]

@[ext] theorem hom_ext {X Y : SuperStarAlgCat 𝕜} {f g : X ⟶ Y} (h : ∀ x, f.1 x = g.1 x) :
    f = g :=
  Subtype.ext (StarAlgHom.ext h)

/-- A grading-preserving `*`-algebra isomorphism is an isomorphism in `SuperStarAlgCat`. -/
def isoOfStarAlgEquiv {X Y : SuperStarAlgCat 𝕜} (e : X ≃⋆ₐ[𝕜] Y)
    (he : ∀ {i : ZMod 2} {x : X}, x ∈ superGrading 𝕜 X i → e x ∈ superGrading 𝕜 Y i)
    (he' : ∀ {i : ZMod 2} {y : Y}, y ∈ superGrading 𝕜 Y i → e.symm y ∈ superGrading 𝕜 X i) :
    X ≅ Y where
  hom := ⟨(e : X →⋆ₐ[𝕜] Y), he⟩
  inv := ⟨(e.symm : Y →⋆ₐ[𝕜] X), he'⟩
  hom_inv_id := hom_ext fun x => e.symm_apply_apply x
  inv_hom_id := hom_ext fun y => e.apply_symm_apply y

variable (𝕜) in
/-- The forgetful functor to `𝕜`-modules. -/
def forgetToModuleCat : SuperStarAlgCat 𝕜 ⥤ ModuleCat.{u} 𝕜 where
  obj X := ModuleCat.of 𝕜 X
  map f := ModuleCat.ofHom f.1.toAlgHom.toLinearMap

instance : (forgetToModuleCat 𝕜).Faithful where
  map_injective h := hom_ext fun x => congrArg (fun φ => φ.hom x) h

/-! ### The monoidal structure -/

/-- The super tensor product of two morphisms. -/
def superTensorHom {X₁ Y₁ X₂ Y₂ : SuperStarAlgCat 𝕜} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    of (𝕜 := 𝕜) (SuperTensor 𝕜 X₁ X₂) ⟶ of (𝕜 := 𝕜) (SuperTensor 𝕜 Y₁ Y₂) :=
  ⟨SuperTensor.map f.1 g.1 f.2 g.2, SuperTensor.map_mem f.1 g.1 f.2 g.2⟩

private lemma lidₗ_symm_mem {X : SuperStarAlgCat 𝕜} {n : ZMod 2} {y : X}
    (hy : y ∈ superGrading 𝕜 X n) :
    (lid 𝕜 X).symm y ∈ superGrading 𝕜 (SuperTensor 𝕜 𝕜 X) n :=
  mem_of_map_mem (lidₗ 𝕜 X).toLinearMap (lidₗ 𝕜 X).injective lidₗ_mem
    (by rwa [LinearEquiv.coe_coe, show (lidₗ 𝕜 X) ((lid 𝕜 X).symm y) = y from
      (lid 𝕜 X).apply_symm_apply y])

private lemma ridₗ_symm_mem {X : SuperStarAlgCat 𝕜} {n : ZMod 2} {y : X}
    (hy : y ∈ superGrading 𝕜 X n) :
    (rid 𝕜 X).symm y ∈ superGrading 𝕜 (SuperTensor 𝕜 X 𝕜) n :=
  mem_of_map_mem (ridₗ 𝕜 X).toLinearMap (ridₗ 𝕜 X).injective ridₗ_mem
    (by rwa [LinearEquiv.coe_coe, show (ridₗ 𝕜 X) ((rid 𝕜 X).symm y) = y from
      (rid 𝕜 X).apply_symm_apply y])

private lemma assoc_symm_mem {X Y Z : SuperStarAlgCat 𝕜} {n : ZMod 2}
    {y : SuperTensor 𝕜 X (SuperTensor 𝕜 Y Z)}
    (hy : y ∈ superGrading 𝕜 (SuperTensor 𝕜 X (SuperTensor 𝕜 Y Z)) n) :
    (assoc 𝕜 X Y Z).symm y ∈ superGrading 𝕜 (SuperTensor 𝕜 (SuperTensor 𝕜 X Y) Z) n :=
  assocₗ_symm_mem hy

instance monoidalCategoryStruct : MonoidalCategoryStruct (SuperStarAlgCat 𝕜) where
  tensorObj X Y := of (SuperTensor 𝕜 X Y)
  whiskerLeft X _ _ g := superTensorHom (𝟙 X) g
  whiskerRight f Y := superTensorHom f (𝟙 Y)
  tensorHom f g := superTensorHom f g
  tensorUnit := of 𝕜
  associator X Y Z := isoOfStarAlgEquiv (assoc 𝕜 X Y Z) assocₗ_mem assoc_symm_mem
  leftUnitor X := isoOfStarAlgEquiv (lid 𝕜 X) lidₗ_mem lidₗ_symm_mem
  rightUnitor X := isoOfStarAlgEquiv (rid 𝕜 X) ridₗ_mem ridₗ_symm_mem

/-- The forgetful functor preserves all the monoidal data on the nose. -/
private def inducingData : Monoidal.InducingFunctorData (forgetToModuleCat 𝕜) where
  μIso X Y := (SuperTensor.of 𝕜 X Y).toModuleIso
  whiskerLeft_eq X Y₁ Y₂ f := ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ => by
    with_unfolding_all rfl
  whiskerRight_eq f Y := ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ => by
    with_unfolding_all rfl
  tensorHom_eq f g := ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ => by
    with_unfolding_all rfl
  εIso := Iso.refl _
  associator_eq X Y Z := ModuleCat.hom_ext <| TensorProduct.ext_threefold fun _ _ _ => by
    with_unfolding_all rfl
  leftUnitor_eq X := ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ => by
    with_unfolding_all rfl
  rightUnitor_eq X := ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ => by
    with_unfolding_all rfl

/-- `SuperStarAlgCat 𝕜` is a monoidal category under the super tensor product. -/
instance monoidalCategory : MonoidalCategory (SuperStarAlgCat 𝕜) :=
  Monoidal.induced (forgetToModuleCat 𝕜) inducingData

/-! ### Evaluating the structure maps on pure tensors -/

section Eval

variable {X Y Z X₁ X₂ Y₁ Y₂ : SuperStarAlgCat 𝕜}

theorem comp_apply' (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g).1 x = g.1 (f.1 x) := rfl

theorem id_apply' (x : X) : (𝟙 X : X ⟶ X).1 x = x := rfl

theorem tensorHom_apply_tmul (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (a : X₁) (b : X₂) :
    (f ⊗ₘ g).1 (a ⊗ˢ[𝕜] b) = f.1 a ⊗ˢ[𝕜] g.1 b := rfl

theorem whiskerLeft_apply_tmul (f : Y₁ ⟶ Y₂) (a : X) (b : Y₁) :
    (X ◁ f).1 (a ⊗ˢ[𝕜] b) = a ⊗ˢ[𝕜] f.1 b := rfl

theorem whiskerRight_apply_tmul (f : X₁ ⟶ X₂) (a : X₁) (b : Y) :
    (f ▷ Y).1 (a ⊗ˢ[𝕜] b) = f.1 a ⊗ˢ[𝕜] b := rfl

theorem associator_hom_apply_tmul (a : X) (b : Y) (c : Z) :
    (α_ X Y Z).hom.1 ((a ⊗ˢ[𝕜] b) ⊗ˢ[𝕜] c) = a ⊗ˢ[𝕜] (b ⊗ˢ[𝕜] c) := rfl

theorem associator_inv_apply_tmul (a : X) (b : Y) (c : Z) :
    (α_ X Y Z).inv.1 (a ⊗ˢ[𝕜] (b ⊗ˢ[𝕜] c)) = (a ⊗ˢ[𝕜] b) ⊗ˢ[𝕜] c :=
  (assoc 𝕜 X Y Z).symm_apply_eq.2 (assoc_tmul a b c).symm

/-- Morphisms out of `X ⊗ Y` agree once they agree on homogeneous pure tensors. -/
theorem ext_tmul {f g : X ⊗ Y ⟶ Z}
    (h : ∀ {i j : ZMod 2} (a : X) (b : Y), a ∈ superGrading 𝕜 X i →
      b ∈ superGrading 𝕜 Y j → f.1 (a ⊗ˢ[𝕜] b) = g.1 (a ⊗ˢ[𝕜] b)) : f = g :=
  hom_ext fun x => by
    induction x using SuperTensor.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a b ha hb => exact h a b ha hb

/-- Morphisms out of `(X ⊗ Y) ⊗ Z` agree once they agree on homogeneous `(a ⊗ b) ⊗ c`. -/
theorem ext_tmul₃ {W : SuperStarAlgCat 𝕜} {f g : (X ⊗ Y) ⊗ Z ⟶ W}
    (h : ∀ {i j k : ZMod 2} (a : X) (b : Y) (c : Z), a ∈ superGrading 𝕜 X i →
      b ∈ superGrading 𝕜 Y j → c ∈ superGrading 𝕜 Z k →
        f.1 ((a ⊗ˢ[𝕜] b) ⊗ˢ[𝕜] c) = g.1 ((a ⊗ˢ[𝕜] b) ⊗ˢ[𝕜] c)) : f = g :=
  hom_ext fun x => by
    induction x using SuperTensor.induction_on₃ with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a b c ha hb hc => exact h a b c ha hb hc

/-- Morphisms out of `X ⊗ (Y ⊗ Z)` agree once they agree on homogeneous `a ⊗ (b ⊗ c)`. -/
theorem ext_tmul₃' {W : SuperStarAlgCat 𝕜} {f g : X ⊗ (Y ⊗ Z) ⟶ W}
    (h : ∀ {i j k : ZMod 2} (a : X) (b : Y) (c : Z), a ∈ superGrading 𝕜 X i →
      b ∈ superGrading 𝕜 Y j → c ∈ superGrading 𝕜 Z k →
        f.1 (a ⊗ˢ[𝕜] (b ⊗ˢ[𝕜] c)) = g.1 (a ⊗ˢ[𝕜] (b ⊗ˢ[𝕜] c))) : f = g := by
  refine ext_tmul fun {i _} a u ha hu => ?_
  refine tensorGrading_induction (P := fun u => f.1 (a ⊗ˢ[𝕜] u) = g.1 (a ⊗ˢ[𝕜] u)) hu
    (by rw [SuperTensor.tmul_zero, map_zero, map_zero])
    (fun u u' h₁ h₂ => by rw [SuperTensor.tmul_add, map_add, map_add, h₁, h₂])
    fun b c hb hc _ => h a b c ha hb hc

end Eval

/-! ### The Koszul braiding -/

/-- The Koszul braiding `X ⊗ Y ≅ Y ⊗ X`. -/
def superBraiding (X Y : SuperStarAlgCat 𝕜) : X ⊗ Y ≅ Y ⊗ X :=
  isoOfStarAlgEquiv (comm 𝕜 X Y) commₗ_mem fun hy => commₗ_mem hy

theorem superBraiding_hom_apply_tmul {X Y : SuperStarAlgCat 𝕜} {i j : ZMod 2} {a : X} {b : Y}
    (ha : a ∈ superGrading 𝕜 X i) (hb : b ∈ superGrading 𝕜 Y j) :
    (superBraiding X Y).hom.1 (a ⊗ˢ[𝕜] b) = koszulSign 𝕜 i j • (b ⊗ˢ[𝕜] a) :=
  comm_tmul ha hb

/-- `SuperStarAlgCat 𝕜` is symmetric monoidal with the Koszul braiding. -/
instance symmetricCategory : SymmetricCategory (SuperStarAlgCat 𝕜) where
  braiding := superBraiding
  braiding_naturality_right X Y Z g := ext_tmul fun a b ha hb => by
    rw [comp_apply', comp_apply', whiskerLeft_apply_tmul, superBraiding_hom_apply_tmul ha (g.2 hb),
      superBraiding_hom_apply_tmul ha hb, map_smul, whiskerRight_apply_tmul]
  braiding_naturality_left f Z := ext_tmul fun a b ha hb => by
    rw [comp_apply', comp_apply', whiskerRight_apply_tmul, superBraiding_hom_apply_tmul (f.2 ha) hb,
      superBraiding_hom_apply_tmul ha hb, map_smul, whiskerLeft_apply_tmul]
  hexagon_forward X Y Z := ext_tmul₃ fun a b c ha hb hc => by
    rw [comp_apply', comp_apply', comp_apply', comp_apply', associator_hom_apply_tmul,
      superBraiding_hom_apply_tmul ha (tmul_mem_tensorGrading hb hc), map_smul,
      associator_hom_apply_tmul, whiskerRight_apply_tmul, superBraiding_hom_apply_tmul ha hb,
      ← smul_tmul', map_smul, map_smul, associator_hom_apply_tmul, whiskerLeft_apply_tmul,
      superBraiding_hom_apply_tmul ha hc, SuperTensor.tmul_smul, smul_smul,
      koszulSign_add_right]
  hexagon_reverse X Y Z := ext_tmul₃' fun a b c ha hb hc => by
    rw [comp_apply', comp_apply', comp_apply', comp_apply', associator_inv_apply_tmul,
      superBraiding_hom_apply_tmul (tmul_mem_tensorGrading ha hb) hc, map_smul,
      associator_inv_apply_tmul, whiskerLeft_apply_tmul, superBraiding_hom_apply_tmul hb hc,
      SuperTensor.tmul_smul, map_smul, map_smul, associator_inv_apply_tmul,
      whiskerRight_apply_tmul, superBraiding_hom_apply_tmul ha hc, ← smul_tmul', smul_smul,
      koszulSign_add_left, mul_comm]
  symmetry X Y := ext_tmul fun a b ha hb => by
    rw [comp_apply', superBraiding_hom_apply_tmul ha hb, map_smul,
      superBraiding_hom_apply_tmul hb ha, smul_smul, koszulSign_comm 𝕜 _ (_ : ZMod 2),
      koszulSign_mul_self, one_smul, id_apply']

end SuperStarAlgCat
