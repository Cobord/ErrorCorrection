import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.CategoryTheory.Functor.Basic
import QuantumErrorCorrection.GrpInclCat
import QuantumErrorCorrection.QuasiLocalAlgebra

/-!
# The group algebra as a `ZMod 2`-graded `*`-algebra

For a fixed group `G` and a commutative `*`-ring `𝕜`, this file makes the group algebra
`MonoidAlgebra 𝕜 G` into a `SuperStarAlgebra 𝕜 (MonoidAlgebra 𝕜 G)` (see
`QuasiLocalAlgebra.lean`):

* `star` extends group inversion: `star (single g c) = single g⁻¹ (star c)`. It is built as an
  `AddMonoidHom` (via `Finsupp.liftAddHom`) so that additivity is free, and the `StarRing`
  axioms (`star_involutive`, `star_mul`) are then established using
  `MonoidAlgebra.addMonoidHom_ext`, which reduces an equation between additive maps out of
  `MonoidAlgebra 𝕜 G` to checking it on generators `single g c`.
* The grading is *trivial* (everything in degree `0`, i.e. bosonic): a group algebra carries no
  fermionic content on its own.

Finally, an injective group homomorphism `f : G ↪ H` (a morphism of `GrpInclCat`, see
`GrpInclCat.lean`) induces an injective, grading-preserving `*`-algebra homomorphism
`MonoidAlgebra 𝕜 G →⋆ₐ[𝕜] MonoidAlgebra 𝕜 H`, relating the group algebras of *different* groups.
-/

noncomputable section

open MonoidAlgebra DirectSum CategoryTheory

universe u

section SingleGroup

variable {𝕜 G : Type u} [CommRing 𝕜] [StarRing 𝕜] [Group G]

/-! ### `star`, extending group inversion -/

/-- `star` on a group algebra, extending group inversion on the basis:
`groupAlgebraStarHom (single g c) = single g⁻¹ (star c)`. Built as an `AddMonoidHom` (via
`Finsupp.liftAddHom`) so that additivity holds definitionally. -/
def groupAlgebraStarHom : MonoidAlgebra 𝕜 G →+ MonoidAlgebra 𝕜 G :=
  (Finsupp.liftAddHom fun g : G =>
      (MonoidAlgebra.singleAddHom (g⁻¹ : G)).comp (starAddEquiv (R := 𝕜)).toAddMonoidHom).comp
    (MonoidAlgebra.coeffAddEquiv (R := 𝕜) (M := G)).toAddMonoidHom

@[simp] lemma groupAlgebraStarHom_single (g : G) (c : 𝕜) :
    groupAlgebraStarHom (MonoidAlgebra.single g c) = MonoidAlgebra.single g⁻¹ (star c) := by
  unfold groupAlgebraStarHom
  simp [MonoidAlgebra.coeff_single]

private lemma groupAlgebraStarHom_comp_self :
    groupAlgebraStarHom.comp groupAlgebraStarHom = AddMonoidHom.id (MonoidAlgebra 𝕜 G) := by
  apply MonoidAlgebra.addMonoidHom_ext
  intro g c
  simp

/-- `groupAlgebraStarHom` is an involution: applying it twice is the identity. -/
lemma groupAlgebraStarHom_groupAlgebraStarHom (x : MonoidAlgebra 𝕜 G) :
    groupAlgebraStarHom (groupAlgebraStarHom x) = x := by
  rw [← AddMonoidHom.comp_apply, groupAlgebraStarHom_comp_self, AddMonoidHom.id_apply]

private lemma groupAlgebraStarHom_mul_single_single (m n : G) (r s : 𝕜) :
    groupAlgebraStarHom ((MonoidAlgebra.single m r : MonoidAlgebra 𝕜 G) *
        MonoidAlgebra.single n s)
      = groupAlgebraStarHom (MonoidAlgebra.single n s) *
        groupAlgebraStarHom (MonoidAlgebra.single m r) := by
  simp [MonoidAlgebra.single_mul_single, mul_inv_rev, star_mul]

private lemma groupAlgebraStarHom_mul_single_left (m : G) (r : 𝕜) (y : MonoidAlgebra 𝕜 G) :
    groupAlgebraStarHom (MonoidAlgebra.single m r * y)
      = groupAlgebraStarHom y * groupAlgebraStarHom (MonoidAlgebra.single m r) := by
  have h : groupAlgebraStarHom.comp (AddMonoidHom.mulLeft (MonoidAlgebra.single m r))
      = (AddMonoidHom.mulRight (groupAlgebraStarHom (MonoidAlgebra.single m r))).comp
        groupAlgebraStarHom := by
    apply MonoidAlgebra.addMonoidHom_ext
    intro n s
    simpa using groupAlgebraStarHom_mul_single_single m n r s
  simpa using DFunLike.congr_fun h y

/-- `groupAlgebraStarHom` is a ring *anti*-automorphism: `star (x * y) = star y * star x`. -/
lemma groupAlgebraStarHom_mul (x y : MonoidAlgebra 𝕜 G) :
    groupAlgebraStarHom (x * y) = groupAlgebraStarHom y * groupAlgebraStarHom x := by
  have h : groupAlgebraStarHom.comp (AddMonoidHom.mulRight y)
      = (AddMonoidHom.mulLeft (groupAlgebraStarHom y)).comp groupAlgebraStarHom := by
    apply MonoidAlgebra.addMonoidHom_ext
    intro m r
    simpa using groupAlgebraStarHom_mul_single_left m r y
  simpa using DFunLike.congr_fun h x

instance : Star (MonoidAlgebra 𝕜 G) := ⟨groupAlgebraStarHom⟩

@[simp] lemma star_single (g : G) (c : 𝕜) :
    star (MonoidAlgebra.single g c : MonoidAlgebra 𝕜 G) = MonoidAlgebra.single g⁻¹ (star c) :=
  groupAlgebraStarHom_single g c

instance : StarRing (MonoidAlgebra 𝕜 G) where
  star_involutive := groupAlgebraStarHom_groupAlgebraStarHom
  star_mul := groupAlgebraStarHom_mul
  star_add := groupAlgebraStarHom.map_add

instance : StarModule 𝕜 (MonoidAlgebra 𝕜 G) where
  star_smul r x := by
    have h : groupAlgebraStarHom.comp
        (AddMonoidHom.mk' (r • · : MonoidAlgebra 𝕜 G → MonoidAlgebra 𝕜 G) (smul_add r))
        = (AddMonoidHom.mk' (star r • · : MonoidAlgebra 𝕜 G → MonoidAlgebra 𝕜 G)
          (smul_add (star r))).comp groupAlgebraStarHom := by
      apply MonoidAlgebra.addMonoidHom_ext
      intro g c
      simp [star_mul, mul_comm]
    show groupAlgebraStarHom (r • x) = star r • groupAlgebraStarHom x
    exact DFunLike.congr_fun h x

/-! ### The trivial grading

A group algebra carries no fermionic (odd) content: every element is "bosonic". -/

/-- The trivial `ZMod 2`-grading on a group algebra: everything is in degree `0` (bosonic). -/
def MonoidAlgebra.trivialGrading (i : ZMod 2) : Submodule 𝕜 (MonoidAlgebra 𝕜 G) :=
  if i = 0 then ⊤ else ⊥

omit [StarRing 𝕜] [Group G] in
private lemma MonoidAlgebra.trivialGrading_isInternal :
    DirectSum.IsInternal (MonoidAlgebra.trivialGrading (𝕜 := 𝕜) (G := G)) := by
  apply (DirectSum.isInternal_submodule_iff_isCompl
    (MonoidAlgebra.trivialGrading (𝕜 := 𝕜) (G := G)) (i := 0) (j := 1) (by decide) (by
      ext i
      simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl)).2
  constructor
  · simp [MonoidAlgebra.trivialGrading]
  · simp [MonoidAlgebra.trivialGrading]

/-- The trivial `SuperVectorSpace` structure on a group algebra: everything is even. This is
scoped specifically to `MonoidAlgebra 𝕜 G`, not declared as a blanket instance on every module,
so it cannot collide with other `SuperVectorSpace` instances (e.g. the odd/even grading on
`Supersymmetric.OneN.Space` in `Supersymmetric/OneN.lean`). -/
instance : SuperVectorSpace 𝕜 (MonoidAlgebra 𝕜 G) where
  grading := MonoidAlgebra.trivialGrading
  decomposition := MonoidAlgebra.trivialGrading_isInternal.chooseDecomposition

omit [StarRing 𝕜] [Group G] in
@[simp] lemma MonoidAlgebra.mem_trivialGrading_zero (x : MonoidAlgebra 𝕜 G) :
    x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := MonoidAlgebra 𝕜 G) 0 := by
  show x ∈ MonoidAlgebra.trivialGrading (𝕜 := 𝕜) (G := G) 0
  simp [MonoidAlgebra.trivialGrading]

omit [StarRing 𝕜] in
@[simp] lemma MonoidAlgebra.mem_trivialGrading_one_iff (x : MonoidAlgebra 𝕜 G) :
    x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := MonoidAlgebra 𝕜 G) 1 ↔ x = 0 := by
  show x ∈ MonoidAlgebra.trivialGrading (𝕜 := 𝕜) (G := G) 1 ↔ x = 0
  simp [MonoidAlgebra.trivialGrading]

/-- The group algebra is a `SuperStarAlgebra`: since the grading is trivial (everything even),
`grading_mul_mem`/`grading_star_mem` reduce to the fact that every submodule contains `0`. -/
private lemma zmod2_eq_zero_or_one (i : ZMod 2) : i = 0 ∨ i = 1 := by revert i; decide

instance : SuperStarAlgebra 𝕜 (MonoidAlgebra 𝕜 G) where
  grading_mul_mem {i j x y} hx hy := by
    have hx' : x ∈ MonoidAlgebra.trivialGrading (𝕜 := 𝕜) (G := G) i := hx
    have hy' : y ∈ MonoidAlgebra.trivialGrading (𝕜 := 𝕜) (G := G) j := hy
    show x * y ∈ MonoidAlgebra.trivialGrading (𝕜 := 𝕜) (G := G) (i + j)
    obtain rfl | rfl := zmod2_eq_zero_or_one i <;> obtain rfl | rfl := zmod2_eq_zero_or_one j <;>
      simp_all [MonoidAlgebra.trivialGrading]
  grading_star_mem {i x} hx := by
    have hx' : x ∈ MonoidAlgebra.trivialGrading (𝕜 := 𝕜) (G := G) i := hx
    show star x ∈ MonoidAlgebra.trivialGrading (𝕜 := 𝕜) (G := G) i
    obtain rfl | rfl := zmod2_eq_zero_or_one i <;> simp_all [MonoidAlgebra.trivialGrading]

end SingleGroup

/-! ### Relating different groups

An injective group homomorphism `f : G ↪ H` (a `GrpInclCat` morphism) induces an injective,
grading-preserving `*`-algebra homomorphism between the group algebras. -/

section Functoriality

variable {𝕜 G H : Type u} [CommRing 𝕜] [StarRing 𝕜] [Group G] [Group H]

private lemma mapDomainAlgHom_comp_starHom (f : G →* H) :
    (MonoidAlgebra.mapDomainAlgHom 𝕜 𝕜 f).toRingHom.toAddMonoidHom.comp
        (groupAlgebraStarHom (𝕜 := 𝕜) (G := G))
      = (groupAlgebraStarHom (𝕜 := 𝕜) (G := H)).comp
        (MonoidAlgebra.mapDomainAlgHom 𝕜 𝕜 f).toRingHom.toAddMonoidHom := by
  apply MonoidAlgebra.addMonoidHom_ext
  intro g c
  simp [map_inv]

/-- The `*`-algebra homomorphism between group algebras induced by a group homomorphism
`f : G →* H`: extends `MonoidAlgebra.mapDomainAlgHom`, additionally preserving `star`. -/
def groupAlgebraMapStarAlgHom (f : G →* H) : MonoidAlgebra 𝕜 G →⋆ₐ[𝕜] MonoidAlgebra 𝕜 H :=
  { MonoidAlgebra.mapDomainAlgHom 𝕜 𝕜 f with
    map_star' := fun x => DFunLike.congr_fun (mapDomainAlgHom_comp_starHom f) x }

@[simp] lemma groupAlgebraMapStarAlgHom_apply (f : G →* H) (x : MonoidAlgebra 𝕜 G) :
    groupAlgebraMapStarAlgHom (𝕜 := 𝕜) f x = MonoidAlgebra.mapDomainAlgHom 𝕜 𝕜 f x := rfl

/-- `groupAlgebraMapStarAlgHom` preserves the (trivial) grading. -/
lemma groupAlgebraMapStarAlgHom_grading_mem (f : G →* H) {i : ZMod 2} {x : MonoidAlgebra 𝕜 G}
    (hx : x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := MonoidAlgebra 𝕜 G) i) :
    groupAlgebraMapStarAlgHom (𝕜 := 𝕜) f x ∈
      SuperVectorSpace.grading (𝕜 := 𝕜) (V := MonoidAlgebra 𝕜 H) i := by
  obtain rfl | rfl := zmod2_eq_zero_or_one i
  · exact MonoidAlgebra.mem_trivialGrading_zero _
  · rw [MonoidAlgebra.mem_trivialGrading_one_iff] at hx
    simp [groupAlgebraMapStarAlgHom_apply, hx]

/-- `groupAlgebraMapStarAlgHom` is injective whenever `f` is: extending a group embedding to
its group algebras loses no information. -/
lemma groupAlgebraMapStarAlgHom_injective {f : G →* H} (hf : Function.Injective f) :
    Function.Injective (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) f) := by
  have hfun : (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) f : MonoidAlgebra 𝕜 G → MonoidAlgebra 𝕜 H)
      = MonoidAlgebra.mapDomain f := by
    funext x
    simp [groupAlgebraMapStarAlgHom_apply]
  simpa [hfun] using MonoidAlgebra.mapDomain_injective (R := 𝕜) hf

lemma groupAlgebraMapStarAlgHom_id :
    groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (MonoidHom.id G) = StarAlgHom.id 𝕜 (MonoidAlgebra 𝕜 G) := by
  ext x
  simp [groupAlgebraMapStarAlgHom_apply]

lemma groupAlgebraMapStarAlgHom_comp {K : Type u} [Group K] (f : G →* H) (g : H →* K) :
    groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (g.comp f)
      = (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) g).comp (groupAlgebraMapStarAlgHom f) := by
  ext x
  simp [groupAlgebraMapStarAlgHom_apply]

end Functoriality

/-! ### The functor `GrpInclCat ⥤ SuperStarAlgInclCat` -/

/-- The bundled category of `ZMod 2`-graded `*`-algebras over a fixed base `*`-ring `𝕜`, with
*injective* graded `*`-algebra homomorphisms as morphisms (mirroring `RegionCat`/`GrpInclCat`:
morphisms carry their injectivity as data, rather than this being a subcategory of
`SuperStarAlgCat` cut out after the fact). -/
structure SuperStarAlgInclCat (𝕜 : Type u) [CommRing 𝕜] [StarRing 𝕜] : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [ring : Ring carrier]
  [starRing : StarRing carrier]
  [algebra : Algebra 𝕜 carrier]
  [starModule : StarModule 𝕜 carrier]
  [superStar : SuperStarAlgebra 𝕜 carrier]

namespace SuperStarAlgInclCat

variable {𝕜 : Type u} [CommRing 𝕜] [StarRing 𝕜]

instance : CoeSort (SuperStarAlgInclCat 𝕜) (Type u) := ⟨carrier⟩

attribute [instance] ring starRing algebra starModule superStar

/-- Construct a bundled `SuperStarAlgInclCat` from a type with the relevant structure. -/
abbrev of (A : Type u) [Ring A] [StarRing A] [Algebra 𝕜 A] [StarModule 𝕜 A]
    [SuperStarAlgebra 𝕜 A] : SuperStarAlgInclCat 𝕜 := ⟨A⟩

/-- Morphisms `X ⟶ Y` are exactly the *injective* `*`-algebra homomorphisms preserving the
`ZMod 2` grading. -/
instance : Category (SuperStarAlgInclCat 𝕜) where
  Hom X Y := {f : X.carrier →⋆ₐ[𝕜] Y.carrier //
    (∀ {i : ZMod 2} {x : X.carrier}, x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := X.carrier) i →
      f x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := Y.carrier) i) ∧ Function.Injective f}
  id X := ⟨StarAlgHom.id 𝕜 X.carrier, fun hx => hx, fun _ _ h => h⟩
  comp f g := ⟨g.1.comp f.1, fun hx => g.2.1 (f.2.1 hx), g.2.2.comp f.2.2⟩

/-- The forgetful functor from `SuperStarAlgInclCat` to `SuperStarAlgCat`, forgetting that
every morphism is injective. -/
def forgetful : SuperStarAlgInclCat 𝕜 ⥤ SuperStarAlgCat 𝕜 where
  obj X := SuperStarAlgCat.of X.carrier
  map f := ⟨f.1, f.2.1⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end SuperStarAlgInclCat

/-- The functor sending a group to its group algebra (a graded `*`-algebra, everything even),
and an injective group homomorphism to the induced injective, grading-preserving `*`-algebra
homomorphism between group algebras. -/
noncomputable def groupAlgebraFunctor (𝕜 : Type u) [CommRing 𝕜] [StarRing 𝕜] :
    GrpInclCat.{u} ⥤ SuperStarAlgInclCat 𝕜 where
  obj G := SuperStarAlgInclCat.of (MonoidAlgebra 𝕜 G.carrier)
  map {G H} f := ⟨groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (GrpInclCat.toMonoidHom f),
    fun hx => groupAlgebraMapStarAlgHom_grading_mem _ hx,
    groupAlgebraMapStarAlgHom_injective (GrpInclCat.injective_toMonoidHom f)⟩
  map_id G := by
    apply Subtype.ext
    show groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (GrpInclCat.toMonoidHom (𝟙 G))
        = StarAlgHom.id 𝕜 (MonoidAlgebra 𝕜 G.carrier)
    rw [show GrpInclCat.toMonoidHom (𝟙 G) = MonoidHom.id G.carrier from rfl,
      groupAlgebraMapStarAlgHom_id]
  map_comp {G H K} f g := by
    apply Subtype.ext
    show groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (GrpInclCat.toMonoidHom (f ≫ g))
        = (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (GrpInclCat.toMonoidHom g)).comp
          (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (GrpInclCat.toMonoidHom f))
    rw [show GrpInclCat.toMonoidHom (f ≫ g)
          = (GrpInclCat.toMonoidHom g).comp (GrpInclCat.toMonoidHom f) from rfl,
      groupAlgebraMapStarAlgHom_comp]

end
