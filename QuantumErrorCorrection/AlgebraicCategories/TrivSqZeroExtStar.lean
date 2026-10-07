import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Module

/-!
# Square-zero extensions as `*`-algebras

For a commutative `*`-ring `R` and an `R`-module `M` with a compatible `star`, the square-zero
extension `TrivSqZeroExt R M = R ⊕ M` (with `M * M = 0`) is a commutative `*`-algebra over `R`,
with `star` acting componentwise. Mathlib has the algebra but not the star structure.

Over a reduced ring every algebra homomorphism `φ : R ⊕ M → R ⊕ N` maps `M` into `N`: the image
of `m` squares to zero, so its `R`-component is nilpotent, hence zero. So `φ` is
`TrivSqZeroExt.map` of a linear map `M → N`, its *linear part* `TrivSqZeroExt.linearPart φ`, and
taking linear parts is functorial. This is what makes automorphisms of square-zero nets
computable by linear algebra.
-/

local notation "tsze" => TrivSqZeroExt

namespace TrivSqZeroExt

variable {R M N P : Type*}

/-! ### The componentwise star -/

instance instStar [Star R] [Star M] : Star (tsze R M) := ⟨fun x => (star x.fst, star x.snd)⟩

@[simp] theorem fst_star [Star R] [Star M] (x : tsze R M) : (star x).fst = star x.fst := rfl

@[simp] theorem snd_star [Star R] [Star M] (x : tsze R M) : (star x).snd = star x.snd := rfl

instance instInvolutiveStar [InvolutiveStar R] [InvolutiveStar M] :
    InvolutiveStar (tsze R M) :=
  ⟨fun x => ext (star_star x.fst) (star_star x.snd)⟩

instance instStarAddMonoid [AddMonoid R] [AddMonoid M] [StarAddMonoid R] [StarAddMonoid M] :
    StarAddMonoid (tsze R M) :=
  ⟨fun x y => ext (star_add x.fst y.fst) (star_add x.snd y.snd)⟩

section Comm

variable [CommRing R] [StarRing R]
  [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [StarAddMonoid M]
  [StarModule R M]

instance instStarRing : StarRing (tsze R M) where
  star_mul x y := by
    refine ext ?_ ?_
    · simp only [fst_star, fst_mul, star_mul', mul_comm]
    · simp only [snd_star, snd_mul, fst_star, star_add, star_smul, op_smul_eq_smul]
      exact add_comm _ _
  star_add x y := star_add x y

instance instStarModule : StarModule R (tsze R M) where
  star_smul r x := ext (by simp [star_mul']) (by simp [star_smul])

end Comm

/-! ### Star algebra maps from star-compatible linear maps -/

section Map

variable [CommRing R] [StarRing R]
  [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [StarAddMonoid M]
  [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N] [StarAddMonoid N]
  [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P] [StarAddMonoid P]

/-- `TrivSqZeroExt.map f` as a `*`-algebra homomorphism, for `f` commuting with `star`. -/
def starMap (f : M →ₗ[R] N) (hf : ∀ m, f (star m) = star (f m)) : tsze R M →⋆ₐ[R] tsze R N :=
  { map f with
    map_star' := fun x => ext (by simp [fst_map]) (by simp [snd_map, hf]) }

@[simp] theorem starMap_apply (f : M →ₗ[R] N) (hf) (x : tsze R M) :
    starMap f hf x = map f x := rfl

theorem starMap_inr (f : M →ₗ[R] N) (hf) (m : M) : starMap f hf (inr m) = inr (f m) :=
  map_inr f m

theorem starMap_id : starMap (LinearMap.id : M →ₗ[R] M) (fun _ => rfl) = StarAlgHom.id R _ :=
  StarAlgHom.ext fun x => ext (by simp) (by simp)

theorem starMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf hg) :
    starMap (g ∘ₗ f) (fun m => by simp [hf, hg]) = (starMap g hg).comp (starMap f hf) :=
  StarAlgHom.ext fun x => ext (by simp [fst_map]) (by simp [snd_map])

theorem starMap_injective (f : M →ₗ[R] N) (hf) (hfi : Function.Injective f) :
    Function.Injective (starMap f hf) := fun x y h =>
  ext (by simpa [fst_map] using congrArg fst h) (hfi (by simpa [snd_map] using congrArg snd h))

end Map

/-! ### Linear parts over a reduced ring -/

section LinearPart

variable [CommRing R]
  [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
  [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
  [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]

/-- Over a reduced ring, an algebra homomorphism maps `M` into `N`: the image of `inr m`
squares to zero, so its `R`-component is nilpotent. -/
theorem fst_algHom_inr [IsReduced R] (φ : tsze R M →ₐ[R] tsze R N) (m : M) :
    (φ (inr m)).fst = 0 := by
  have h : φ (inr m) * φ (inr m) = 0 := by rw [← map_mul, inr_mul_inr, map_zero]
  have h' : (φ (inr m)).fst * (φ (inr m)).fst = 0 := by simpa using congrArg fst h
  exact IsReduced.eq_zero _ ⟨2, by rw [pow_two, h']⟩

/-- The *linear part* `M → N` of an algebra homomorphism `R ⊕ M → R ⊕ N`. -/
def linearPart (φ : tsze R M →ₐ[R] tsze R N) : M →ₗ[R] N :=
  sndHom R N ∘ₗ φ.toLinearMap ∘ₗ inrHom R M

theorem linearPart_apply (φ : tsze R M →ₐ[R] tsze R N) (m : M) :
    linearPart φ m = (φ (inr m)).snd := rfl

theorem algHom_inr [IsReduced R] (φ : tsze R M →ₐ[R] tsze R N) (m : M) :
    φ (inr m) = inr (linearPart φ m) :=
  ext (fst_algHom_inr φ m) rfl

/-- An algebra homomorphism is `map` of its linear part. -/
theorem eq_map_linearPart [IsReduced R] (φ : tsze R M →ₐ[R] tsze R N) :
    φ = map (linearPart φ) :=
  algHom_ext fun m => by rw [algHom_inr, map_inr]

@[simp] theorem linearPart_map (f : M →ₗ[R] N) : linearPart (map f) = f :=
  LinearMap.ext fun m => by rw [linearPart_apply, map_inr, snd_inr]

@[simp] theorem linearPart_id : linearPart (AlgHom.id R (tsze R M)) = LinearMap.id :=
  LinearMap.ext fun _ => rfl

theorem linearPart_comp [IsReduced R] (φ : tsze R M →ₐ[R] tsze R N)
    (ψ : tsze R N →ₐ[R] tsze R P) :
    linearPart (ψ.comp φ) = linearPart ψ ∘ₗ linearPart φ :=
  LinearMap.ext fun m => by
    rw [linearPart_apply, AlgHom.comp_apply, algHom_inr φ, algHom_inr ψ]
    rfl

end LinearPart

end TrivSqZeroExt
