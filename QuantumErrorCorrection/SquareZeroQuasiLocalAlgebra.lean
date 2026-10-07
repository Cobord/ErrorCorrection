import Mathlib.Algebra.Star.Pi
import Mathlib.LinearAlgebra.FreeModule.Basic
import QuantumErrorCorrection.AlgebraicCategories.TrivSqZeroExtStar
import QuantumErrorCorrection.QCA

/-!
# The square-zero quasi-local algebra

The simplest system on which QCAs can be computed: to a finite region `S` assign the square-zero
extension `𝕜 ⊕ 𝕜^S` (`TrivSqZeroExt 𝕜 (S.carrier → 𝕜)`, with `𝕜^S · 𝕜^S = 0`), with `star`
acting componentwise, and to an inclusion `S ⊆ T` extension of functions by zero. It is
commutative and purely even, so microcausality is automatic, and each local algebra is a free
`𝕜`-module, so it is an object `SquareZero.obj X 𝕜` of `BoundedSpreadCat X 𝕜`.

Over a reduced ring every algebra map between square-zero extensions is `map` of a linear map
(`TrivSqZeroExt.eq_map_linearPart`). So a bounded-spread homomorphism `α` of this system is the
same thing as a *banded* linear map on `X →₀ 𝕜` (the colimit of the `𝕜^S`):

* `SquareZero.linPart α : (X →₀ 𝕜) →ₗ[𝕜] (X →₀ 𝕜)` is determined by
  `linPart α (embed S m) = embed (metricNbhd l S) (lin α S m)` (`linPart_embed`), and it
  determines `α` (`linPart_injective`);
* it is compatible with identities, weakening and composition, hence defined on morphisms of
  `BoundedSpreadCat` (`linHom`), and turns a QCA into a linear automorphism (`linEquiv`);
* it sends functions supported on `S` to functions supported on the `l`-neighborhood of `S`,
  and on `S` itself when `α` preserves `S` (`linPart_mem_supported_of_preservesRegion`).

Conversely `SquareZero.ofLinear` builds a bounded-spread homomorphism from a natural,
star-compatible family of linear maps `𝕜^S → 𝕜^(metricNbhd l S)`.
-/

noncomputable section

open CategoryTheory NNReal RegionCat BoundedSpreadCat TrivSqZeroExt

universe u

namespace SquareZero

variable {X : Type u} [DecidableEq X] {𝕜 : Type u} [CommRing 𝕜]

/-! ### Functions on regions -/

section Functions

variable {S T U : RegionCat X}

variable (𝕜) in
/-- Extension by zero of a function on `S` to a function on `T ⊇ S`. -/
def extendZero (_ : S.carrier ⊆ T.carrier) : (S.carrier → 𝕜) →ₗ[𝕜] (T.carrier → 𝕜) where
  toFun m t := if ht : t.1 ∈ S.carrier then m ⟨t.1, ht⟩ else 0
  map_add' m m' := funext fun t => by by_cases ht : t.1 ∈ S.carrier <;> simp [ht]
  map_smul' c m := funext fun t => by by_cases ht : t.1 ∈ S.carrier <;> simp [ht]

theorem extendZero_apply (h : S.carrier ⊆ T.carrier) (m : S.carrier → 𝕜) (t : T.carrier) :
    extendZero 𝕜 h m t = if ht : t.1 ∈ S.carrier then m ⟨t.1, ht⟩ else 0 := rfl

@[simp] theorem extendZero_self (h : S.carrier ⊆ S.carrier) (m : S.carrier → 𝕜) :
    extendZero 𝕜 h m = m :=
  funext fun t => by simp [extendZero_apply, t.2]

@[simp] theorem extendZero_extendZero (h : S.carrier ⊆ T.carrier) (h' : T.carrier ⊆ U.carrier)
    (m : S.carrier → 𝕜) : extendZero 𝕜 h' (extendZero 𝕜 h m) = extendZero 𝕜 (h.trans h') m :=
  funext fun u => by
    by_cases hu : u.1 ∈ S.carrier
    · simp [extendZero_apply, hu, h hu]
    · by_cases hu' : u.1 ∈ T.carrier <;> simp [extendZero_apply, hu, hu']

theorem extendZero_star [StarRing 𝕜] (h : S.carrier ⊆ T.carrier) (m : S.carrier → 𝕜) :
    extendZero 𝕜 h (star m) = star (extendZero 𝕜 h m) :=
  funext fun t => by by_cases ht : t.1 ∈ S.carrier <;> simp [extendZero_apply, ht]

theorem extendZero_injective (h : S.carrier ⊆ T.carrier) :
    Function.Injective (extendZero 𝕜 h) := fun m m' e => funext fun s => by
  simpa [extendZero_apply, s.2] using congrFun e ⟨s.1, h s.2⟩

variable (𝕜) in
/-- A function on a region, as a finitely supported function on all of `X`. -/
def embed (S : RegionCat X) : (S.carrier → 𝕜) →ₗ[𝕜] (X →₀ 𝕜) where
  toFun m := Finsupp.onFinset S.carrier (fun x => if hx : x ∈ S.carrier then m ⟨x, hx⟩ else 0)
    fun x hx => by by_contra h; simp [h] at hx
  map_add' m m' := Finsupp.ext fun x => by
    by_cases hx : x ∈ S.carrier <;> simp [hx]
  map_smul' c m := Finsupp.ext fun x => by
    by_cases hx : x ∈ S.carrier <;> simp [hx]

theorem embed_apply (m : S.carrier → 𝕜) (x : X) :
    embed 𝕜 S m x = if hx : x ∈ S.carrier then m ⟨x, hx⟩ else 0 := rfl

@[simp] theorem embed_extendZero (h : S.carrier ⊆ T.carrier) (m : S.carrier → 𝕜) :
    embed 𝕜 T (extendZero 𝕜 h m) = embed 𝕜 S m :=
  Finsupp.ext fun x => by
    by_cases hx : x ∈ S.carrier
    · simp [embed_apply, extendZero_apply, hx, h hx]
    · by_cases hx' : x ∈ T.carrier <;> simp [embed_apply, extendZero_apply, hx, hx']

theorem embed_injective (S : RegionCat X) : Function.Injective (embed 𝕜 S) :=
  fun m m' e => funext fun s => by simpa [embed_apply, s.2] using DFunLike.congr_fun e s.1

theorem embed_mem_supported (m : S.carrier → 𝕜) :
    embed 𝕜 S m ∈ Finsupp.supported 𝕜 𝕜 (S.carrier : Set X) :=
  (Finsupp.mem_supported' _ _).2 fun x hx => by simp [embed_apply, show x ∉ S.carrier from hx]

theorem eq_embed_of_mem_supported {v : X →₀ 𝕜}
    (hv : v ∈ Finsupp.supported 𝕜 𝕜 (S.carrier : Set X)) :
    v = embed 𝕜 S (fun s => v s.1) :=
  Finsupp.ext fun x => by
    by_cases hx : x ∈ S.carrier
    · simp [embed_apply, hx]
    · simp [embed_apply, hx, (Finsupp.mem_supported' _ _).1 hv x hx]

theorem single_eq_embed (x : X) (c : 𝕜) :
    Finsupp.single x c = embed 𝕜 (RegionCat.of {x}) (fun _ => c) :=
  Finsupp.ext fun y => by
    rw [embed_apply]
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy]

/-- Two linear maps out of `X →₀ 𝕜` agree when they agree on functions on every region. -/
theorem linearMap_ext_embed {N : Type*} [AddCommGroup N] [Module 𝕜 N]
    {F G : (X →₀ 𝕜) →ₗ[𝕜] N} (h : ∀ (S : RegionCat X) (m : S.carrier → 𝕜),
      F (embed 𝕜 S m) = G (embed 𝕜 S m)) : F = G :=
  Finsupp.lhom_ext fun x c => by rw [single_eq_embed]; exact h _ _

end Functions

/-! ### The system -/

variable [StarRing 𝕜]

section System

variable (X 𝕜) in
/-- The net of square-zero `*`-algebras: `S ↦ 𝕜 ⊕ 𝕜^S`, with inclusions extending by zero. -/
def starNet : RegionCat X ⥤ StarAlgCat 𝕜 where
  obj S := StarAlgCat.of (TrivSqZeroExt 𝕜 (S.carrier → 𝕜))
  map h := StarAlgCat.ofHom (starMap (extendZero 𝕜 (subsetOfHom h)) (extendZero_star _))
  map_id S := StarAlgCat.hom_ext fun x => TrivSqZeroExt.ext (by simp) (by simp)
  map_comp f g := StarAlgCat.hom_ext fun x => TrivSqZeroExt.ext (by simp) (by simp)

private lemma zmod_two_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by revert i; decide

variable (X 𝕜) in
/-- The square-zero quasi-local algebra: `starNet` placed in degree `0`. Isotony is
injectivity of extension by zero; microcausality is commutativity. -/
def qla : QuasiLocalAlgebra X 𝕜 where
  net := starNet X 𝕜 ⋙ StarAlgCat.toPurelyEvenSuperStarAlgCat 𝕜
  isotony h := starMap_injective _ (extendZero_star h) (extendZero_injective h)
  superCommuting {S T} hST {i j x y} hx _ := by
    rcases zmod_two_cases i with rfl | rfl
    · simp only [koszulSign_zero_left, one_smul]
      exact mul_comm (G := TrivSqZeroExt 𝕜 ((RegionCat.of (S.carrier ∪ T.carrier)).carrier → 𝕜))
        _ _
    · have hx0 : x = 0 :=
        StarAlgCat.eq_zero_of_mem_grading_one_toPurelyEvenSuperStarAlgCat 𝕜 _ hx
      subst hx0
      simp

theorem qla_net_map_apply {S T : RegionCat X} (h : S ⟶ T)
    (x : TrivSqZeroExt 𝕜 (S.carrier → 𝕜)) :
    ((qla X 𝕜).net.map h).1 x = map (extendZero 𝕜 (subsetOfHom h)) x := rfl

/-- The local algebras are free, hence flat. -/
theorem qla_flat (S : RegionCat X) : Module.Flat 𝕜 ((qla X 𝕜).net.obj S) :=
  inferInstanceAs (Module.Flat 𝕜 (𝕜 × (S.carrier → 𝕜)))

variable [MetricSpace X] [FiniteClosedBalls X]

variable (X 𝕜) in
/-- The square-zero system as an object of `BoundedSpreadCat`. -/
abbrev obj : BoundedSpreadCat X 𝕜 := .of (qla X 𝕜) qla_flat

end System

/-! ### Linear parts of local maps -/

section LinOf

variable [IsReduced 𝕜] {S T U : RegionCat X}

/-- The linear part `𝕜^S → 𝕜^T` of a morphism between local algebras. -/
def linOf (f : (qla X 𝕜).net.obj S ⟶ (qla X 𝕜).net.obj T) :
    (S.carrier → 𝕜) →ₗ[𝕜] (T.carrier → 𝕜) :=
  linearPart (M := S.carrier → 𝕜) (N := T.carrier → 𝕜) f.1.toAlgHom

theorem apply_inr (f : (qla X 𝕜).net.obj S ⟶ (qla X 𝕜).net.obj T) (m : S.carrier → 𝕜) :
    f.1 (inr m) = inr (linOf f m) :=
  algHom_inr (M := S.carrier → 𝕜) (N := T.carrier → 𝕜) f.1.toAlgHom m

/-- A morphism between local algebras is determined by its linear part. -/
theorem linOf_injective : Function.Injective (linOf (X := X) (𝕜 := 𝕜) (S := S) (T := T)) :=
  fun f g h => Subtype.ext (StarAlgHom.ext fun x => by
    have hf := eq_map_linearPart (M := S.carrier → 𝕜) (N := T.carrier → 𝕜) f.1.toAlgHom
    have hg := eq_map_linearPart (M := S.carrier → 𝕜) (N := T.carrier → 𝕜) g.1.toAlgHom
    have := congrArg (fun φ => map (R' := 𝕜) φ x) h
    exact (DFunLike.congr_fun hf x).trans (this.trans (DFunLike.congr_fun hg x).symm))

theorem linOf_comp (f : (qla X 𝕜).net.obj S ⟶ (qla X 𝕜).net.obj T)
    (g : (qla X 𝕜).net.obj T ⟶ (qla X 𝕜).net.obj U) :
    linOf (f ≫ g) = linOf g ∘ₗ linOf f :=
  linearPart_comp (M := S.carrier → 𝕜) (N := T.carrier → 𝕜) (P := U.carrier → 𝕜)
    f.1.toAlgHom g.1.toAlgHom

omit [IsReduced 𝕜] in
/-- The linear part of `TrivSqZeroExt.starMap g` is `g`. -/
theorem linOf_starMap (g : (S.carrier → 𝕜) →ₗ[𝕜] (T.carrier → 𝕜))
    (hg : ∀ m, g (star m) = star (g m)) :
    linOf (S := S) (T := T)
      ((StarAlgCat.toPurelyEvenSuperStarAlgCat 𝕜).map (StarAlgCat.ofHom (starMap g hg))) = g :=
  linearPart_map (M := S.carrier → 𝕜) (N := T.carrier → 𝕜) _

omit [IsReduced 𝕜] in
@[simp] theorem linOf_map (h : S ⟶ T) :
    linOf ((qla X 𝕜).net.map h) = extendZero 𝕜 (subsetOfHom h) :=
  linOf_starMap _ _

end LinOf

/-! ### Linear parts of bounded-spread homomorphisms -/

section LinPart

variable [MetricSpace X] [FiniteClosedBalls X] [IsReduced 𝕜] {l l' : ℝ≥0}

/-- The local linear parts `𝕜^S → 𝕜^(metricNbhd l S)` of a bounded-spread homomorphism. -/
def lin (α : BoundedSpreadHom l (qla X 𝕜) (qla X 𝕜)) (S : RegionCat X) :
    (S.carrier → 𝕜) →ₗ[𝕜] ((metricNbhd l S).carrier → 𝕜) :=
  linOf (α.app S)

theorem lin_extendZero (α : BoundedSpreadHom l (qla X 𝕜) (qla X 𝕜)) {S T : RegionCat X}
    (h : S.carrier ⊆ T.carrier) (m : S.carrier → 𝕜) :
    lin α T (extendZero 𝕜 h m) = extendZero 𝕜 (metricNbhd_mono l h) (lin α S m) := by
  have := congrArg linOf (α.naturality h)
  rw [linOf_comp, linOf_comp, linOf_map, linOf_map] at this
  exact LinearMap.congr_fun this m

/-- The global linear part: the banded linear map on `X →₀ 𝕜` assembled from the local ones. -/
def linPart (α : BoundedSpreadHom l (qla X 𝕜) (qla X 𝕜)) : (X →₀ 𝕜) →ₗ[𝕜] (X →₀ 𝕜) :=
  Finsupp.linearCombination 𝕜 fun x =>
    embed 𝕜 (metricNbhd l (RegionCat.of {x})) (lin α (RegionCat.of {x}) fun _ => 1)

theorem linPart_embed (α : BoundedSpreadHom l (qla X 𝕜) (qla X 𝕜)) (S : RegionCat X)
    (m : S.carrier → 𝕜) : linPart α (embed 𝕜 S m) = embed 𝕜 (metricNbhd l S) (lin α S m) := by
  suffices h : linPart α ∘ₗ embed 𝕜 S = embed 𝕜 (metricNbhd l S) ∘ₗ lin α S from
    LinearMap.congr_fun h m
  refine LinearMap.pi_ext fun s c => ?_
  have hs : (RegionCat.of {s.1}).carrier ⊆ S.carrier := by simp [s.2]
  have hm : Pi.single s c = extendZero 𝕜 hs (fun _ => c) := funext fun t => by
    rw [extendZero_apply]
    by_cases ht : t = s
    · subst ht; simp
    · have : t.1 ≠ s.1 := fun e => ht (Subtype.ext e)
      simp [ht, this]
  have hc : (fun _ : (RegionCat.of {s.1}).carrier => c) = c • fun _ => (1 : 𝕜) := by
    funext; simp
  simp only [LinearMap.comp_apply]
  rw [hm, lin_extendZero, embed_extendZero, embed_extendZero, ← single_eq_embed, linPart,
    Finsupp.linearCombination_single, hc, map_smul, map_smul]

/-- `linPart α` sends functions supported on `S` to functions supported on its
`l`-neighborhood. -/
theorem linPart_mem_supported (α : BoundedSpreadHom l (qla X 𝕜) (qla X 𝕜)) (S : RegionCat X)
    {v : X →₀ 𝕜} (hv : v ∈ Finsupp.supported 𝕜 𝕜 (S.carrier : Set X)) :
    linPart α v ∈ Finsupp.supported 𝕜 𝕜 ((metricNbhd l S).carrier : Set X) := by
  rw [eq_embed_of_mem_supported hv, linPart_embed]
  exact embed_mem_supported _

/-- If `α` preserves the region `B`, then `linPart α` preserves functions supported on `B`. -/
theorem linPart_mem_supported_of_preservesRegion (α : BoundedSpreadHom l (qla X 𝕜) (qla X 𝕜))
    {B : RegionCat X} (hα : α.PreservesRegion B) {v : X →₀ 𝕜}
    (hv : v ∈ Finsupp.supported 𝕜 𝕜 (B.carrier : Set X)) :
    linPart α v ∈ Finsupp.supported 𝕜 𝕜 (B.carrier : Set X) := by
  obtain ⟨γ, hγ⟩ := hα
  rw [eq_embed_of_mem_supported hv, linPart_embed, lin, hγ, linOf_comp, linOf_map,
    LinearMap.comp_apply, embed_extendZero]
  exact embed_mem_supported _

/-- A bounded-spread homomorphism is determined by its linear part. -/
theorem linPart_injective : Function.Injective (linPart (X := X) (𝕜 := 𝕜) (l := l)) :=
  fun α β h => BoundedSpreadHom.ext fun S => linOf_injective (LinearMap.ext fun m =>
    embed_injective _ (by
      change embed 𝕜 _ (lin α S m) = embed 𝕜 _ (lin β S m)
      rw [← linPart_embed, ← linPart_embed, h]))

@[simp] theorem linPart_weaken (h : l ≤ l') (α : BoundedSpreadHom l (qla X 𝕜) (qla X 𝕜)) :
    linPart (α.weaken h) = linPart α :=
  linearMap_ext_embed fun S m => by
    rw [linPart_embed, linPart_embed, lin, BoundedSpreadHom.weaken_app, linOf_comp, linOf_map,
      LinearMap.comp_apply, embed_extendZero, lin]

@[simp] theorem linPart_id : linPart (BoundedSpreadHom.id (qla X 𝕜)) = LinearMap.id :=
  linearMap_ext_embed fun S m => by
    rw [linPart_embed, lin, BoundedSpreadHom.id_app, linOf_map, embed_extendZero,
      LinearMap.id_apply]

theorem linPart_comp (α : BoundedSpreadHom l (qla X 𝕜) (qla X 𝕜))
    (β : BoundedSpreadHom l' (qla X 𝕜) (qla X 𝕜)) :
    linPart (α.comp β) = linPart β ∘ₗ linPart α :=
  linearMap_ext_embed fun S m => by
    rw [linPart_embed, lin, BoundedSpreadHom.comp_app, linOf_comp, linOf_comp, linOf_map,
      LinearMap.comp_apply, LinearMap.comp_apply, embed_extendZero, LinearMap.comp_apply,
      linPart_embed, linPart_embed]
    rfl

/-! ### On morphisms of `BoundedSpreadCat` and on QCAs -/

/-- The linear part of a morphism of `BoundedSpreadCat`, well defined on germs because
weakening does not change it. -/
def linHom (f : obj X 𝕜 ⟶ obj X 𝕜) : (X →₀ 𝕜) →ₗ[𝕜] (X →₀ 𝕜) :=
  Quotient.lift (s := BoundedSpreadHom.germSetoid (qla X 𝕜) (qla X 𝕜))
    (fun p => linPart p.2)
    (fun _ _ ⟨_, ha, hb, h⟩ => by
      rw [← linPart_weaken ha, ← linPart_weaken hb]
      exact congrArg linPart h)
    f

@[simp] theorem linHom_homMk (α : BoundedSpreadHom l (qla X 𝕜) (qla X 𝕜)) :
    linHom (homMk (A := obj X 𝕜) (B := obj X 𝕜) α) = linPart α := rfl

@[simp] theorem linHom_id : linHom (𝟙 (obj X 𝕜)) = LinearMap.id := by
  rw [← homMk_id, linHom_homMk, linPart_id]

theorem linHom_comp (f g : obj X 𝕜 ⟶ obj X 𝕜) : linHom (f ≫ g) = linHom g ∘ₗ linHom f := by
  obtain ⟨_, α, rfl⟩ := homMk_surjective f
  obtain ⟨_, β, rfl⟩ := homMk_surjective g
  rw [← homMk_comp, linHom_homMk, linHom_homMk, linHom_homMk, linPart_comp]

/-- A QCA of the square-zero system, as a linear automorphism of `X →₀ 𝕜`. -/
def linEquiv (u : QCA (obj X 𝕜)) : (X →₀ 𝕜) ≃ₗ[𝕜] (X →₀ 𝕜) :=
  LinearEquiv.ofLinearMap (linHom u.hom) (linHom u.inv)
    (by rw [← linHom_comp, u.inv_hom_id, linHom_id])
    (by rw [← linHom_comp, u.hom_inv_id, linHom_id])

@[simp] theorem linEquiv_apply (u : QCA (obj X 𝕜)) (v : X →₀ 𝕜) :
    linEquiv u v = linHom u.hom v := rfl

@[simp] theorem linEquiv_symm_apply (u : QCA (obj X 𝕜)) (v : X →₀ 𝕜) :
    (linEquiv u).symm v = linHom u.inv v := rfl

/-- `u * v` is "first `v`, then `u`", and so is composing their linear parts. -/
theorem linEquiv_mul (u v : QCA (obj X 𝕜)) :
    linEquiv (u * v) = (linEquiv v).trans (linEquiv u) :=
  LinearEquiv.toLinearMap_injective (by
    change linHom (v.hom ≫ u.hom) = linHom u.hom ∘ₗ linHom v.hom
    exact linHom_comp _ _)

end LinPart

/-! ### Bounded-spread homomorphisms from linear maps -/

section OfLinear

variable [MetricSpace X] [FiniteClosedBalls X] {l : ℝ≥0}

/-- A bounded-spread homomorphism of the square-zero system from a family of star-compatible
linear maps `𝕜^S → 𝕜^(metricNbhd l S)`, natural with respect to extension by zero. -/
def ofLinear (f : ∀ S : RegionCat X, (S.carrier → 𝕜) →ₗ[𝕜] ((metricNbhd l S).carrier → 𝕜))
    (hstar : ∀ S m, f S (star m) = star (f S m))
    (hnat : ∀ {S T : RegionCat X} (h : S.carrier ⊆ T.carrier) (m : S.carrier → 𝕜),
      f T (extendZero 𝕜 h m) = extendZero 𝕜 (metricNbhd_mono l h) (f S m)) :
    BoundedSpreadHom l (qla X 𝕜) (qla X 𝕜) where
  toNatTrans :=
    { app S := (StarAlgCat.toPurelyEvenSuperStarAlgCat 𝕜).map
        (StarAlgCat.ofHom (starMap (f S) (hstar S)))
      naturality {S T} h := Subtype.ext (StarAlgHom.ext fun x => by
        change map (f T) (map (extendZero 𝕜 (subsetOfHom h)) x) =
          map (extendZero 𝕜 (metricNbhd_mono l (subsetOfHom h))) (map (f S) x)
        refine TrivSqZeroExt.ext ((fst_map _ _).trans ((fst_map _ _).trans
          ((fst_map _ _).trans (fst_map _ _)).symm)) ?_
        exact ((snd_map _ _).trans (congrArg (f T) (snd_map _ x))).trans ((hnat _ _).trans
          ((congrArg _ (snd_map _ x)).symm.trans (snd_map _ _).symm))) }

theorem ofLinear_app_apply (f : ∀ S : RegionCat X, (S.carrier → 𝕜) →ₗ[𝕜]
      ((metricNbhd l S).carrier → 𝕜)) (hstar hnat) (S : RegionCat X)
    (x : TrivSqZeroExt 𝕜 (S.carrier → 𝕜)) :
    ((ofLinear f hstar hnat).app S).1 x = map (f S) x := rfl

theorem lin_ofLinear [IsReduced 𝕜] (f : ∀ S : RegionCat X, (S.carrier → 𝕜) →ₗ[𝕜]
      ((metricNbhd l S).carrier → 𝕜)) (hstar hnat) (S : RegionCat X) :
    lin (ofLinear f hstar hnat) S = f S :=
  linOf_starMap (f S) (hstar S)

theorem linPart_ofLinear_embed [IsReduced 𝕜] (f : ∀ S : RegionCat X, (S.carrier → 𝕜) →ₗ[𝕜]
      ((metricNbhd l S).carrier → 𝕜)) (hstar hnat) (S : RegionCat X) (m : S.carrier → 𝕜) :
    linPart (ofLinear f hstar hnat) (embed 𝕜 S m) = embed 𝕜 (metricNbhd l S) (f S m) := by
  rw [linPart_embed, lin_ofLinear]

end OfLinear

end SquareZero
