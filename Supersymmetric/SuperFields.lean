import Supersymmetric.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

section Fields

open scoped ContDiff

universe u

/-- Bundled smooth maps from `ℝ` to a real normed space. -/
structure SmoothMap (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  toFun : ℝ → F
  contDiff_toFun : ContDiff ℝ ∞ toFun

namespace SmoothMap

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

instance : FunLike (SmoothMap F) ℝ F where
  coe := toFun
  coe_injective f g h := by cases f; cases g; simp_all

@[ext] theorem ext {f g : SmoothMap F} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

instance : Zero (SmoothMap F) := ⟨⟨fun _ ↦ 0, contDiff_const⟩⟩
instance : Add (SmoothMap F) :=
  ⟨fun f g ↦ ⟨fun x ↦ f x + g x, f.contDiff_toFun.add g.contDiff_toFun⟩⟩
instance : Neg (SmoothMap F) := ⟨fun f ↦ ⟨fun x ↦ -f x, f.contDiff_toFun.neg⟩⟩
instance : SMul ℝ (SmoothMap F) :=
  ⟨fun a f ↦ ⟨fun x ↦ a • f x, f.contDiff_toFun.const_smul a⟩⟩

instance : AddCommGroup (SmoothMap F) where
  add_assoc f g h := by apply ext; intro x; exact add_assoc _ _ _
  zero_add f := by apply ext; intro x; exact zero_add _
  add_zero f := by apply ext; intro x; exact add_zero _
  add_comm f g := by apply ext; intro x; exact add_comm _ _
  neg_add_cancel f := by apply ext; intro x; exact neg_add_cancel _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℝ (SmoothMap F) where
  one_smul f := by apply ext; intro x; exact one_smul _ _
  mul_smul a b f := by apply ext; intro x; exact mul_smul _ _ _
  smul_zero a := by apply ext; intro x; exact smul_zero _
  smul_add a f g := by apply ext; intro x; exact smul_add _ _ _
  add_smul a b f := by apply ext; intro x; exact add_smul _ _ _
  zero_smul f := by apply ext; intro x; exact zero_smul _ _

@[simp] theorem zero_apply (x : ℝ) : (0 : SmoothMap F) x = 0 := rfl
@[simp] theorem add_apply (f g : SmoothMap F) (x : ℝ) : (f + g) x = f x + g x := rfl
@[simp] theorem neg_apply (f : SmoothMap F) (x : ℝ) : (-f) x = -f x := rfl
@[simp] theorem sub_apply (f g : SmoothMap F) (x : ℝ) : (f - g) x = f x - g x := by
  simp [sub_eq_add_neg]
@[simp] theorem smul_apply (a : ℝ) (f : SmoothMap F) (x : ℝ) : (a • f) x = a • f x := rfl

/-- Differentiation of smooth sections. -/
noncomputable def deriv : SmoothMap F →ₗ[ℝ] SmoothMap F where
  toFun f := ⟨_root_.deriv f, by
    exact (contDiff_infty_iff_deriv.mp f.contDiff_toFun).2⟩
  map_add' f g := by
    ext x
    exact deriv_add (f.contDiff_toFun.differentiable (by simp) x)
      (g.contDiff_toFun.differentiable (by simp) x)
  map_smul' a f := by
    ext x
    exact deriv_const_smul a (f.contDiff_toFun.differentiable (by simp) x)

@[simp] theorem deriv_apply (f : SmoothMap F) (x : ℝ) : SmoothMap.deriv f x = _root_.deriv f x := rfl

end SmoothMap

/-- Smooth sections of the super vector bundle with even fiber `E` and odd fiber `O`. -/
abbrev SmoothSections (E O : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup O] [NormedSpace ℝ O] := SmoothMap E × SmoothMap O

namespace SmoothSections

variable {E O : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup O] [NormedSpace ℝ O]

/-- The parity grading on the infinite-dimensional space of fields.  A field is even precisely
when its odd component vanishes, and odd precisely when its even component vanishes. -/
def grading (i : ZMod 2) : Submodule ℝ (SmoothSections E O) :=
  if i = 0 then LinearMap.ker (LinearMap.snd ℝ (SmoothMap E) (SmoothMap O))
  else LinearMap.ker (LinearMap.fst ℝ (SmoothMap E) (SmoothMap O))

private theorem grading_isInternal : DirectSum.IsInternal (grading (E := E) (O := O)) := by
  apply (DirectSum.isInternal_submodule_iff_isCompl
    (grading (E := E) (O := O)) (i := 0) (j := 1)
    (by decide) (by
      ext i
      simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl)).2
  constructor
  · rw [disjoint_iff]
    ext f
    simp [grading, Prod.ext_iff, and_comm]
  · rw [codisjoint_iff]
    apply top_unique
    intro f _
    have he : (f.1, 0) ∈ grading (E := E) (O := O) 0 := by simp [grading]
    have ho : (0, f.2) ∈ grading (E := E) (O := O) 1 := by simp [grading]
    simpa using Submodule.add_mem_sup he ho

/-- The super vector space of fields `C∞(ℝ, E ⊕ ΠO)`.  This is named rather than installed
globally, since a blanket instance for product modules would overlap other product gradings. -/
@[instance_reducible]
noncomputable def superVectorSpace : SuperVectorSpace ℝ (SmoothSections E O) where
  grading := grading (E := E) (O := O)
  decomposition := grading_isInternal (E := E) (O := O).chooseDecomposition

@[simp] theorem mem_grading_zero (f : SmoothSections E O) :
    f ∈ grading (E := E) (O := O) 0 ↔ f.2 = 0 := by
  simp [grading]

@[simp] theorem mem_grading_one (f : SmoothSections E O) :
    f ∈ grading (E := E) (O := O) 1 ↔ f.1 = 0 := by
  simp [grading]

end SmoothSections
