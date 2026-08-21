import Supersymmetric.OneN

/-!
# Translation Lie superalgebras

The translation Lie superalgebra is the `A = 0` specialization of the general `1 | N`
construction.  Its only nonzero brackets are `[(0,m),(0,n)] = (B m n, 0)`.
-/

universe u v

namespace LieSuperAlgebra.Translation

variable (𝕜 : Type u) (M : Type v) [CommRing 𝕜] [Invertible (2 : 𝕜)]
  [AddCommGroup M] [Module 𝕜 M]

/-- The underlying supermodule `𝕜 ⊕ ΠM`. -/
abbrev Space := LieSuperAlgebra.OneN.Space 𝕜 M

/-- The translation bracket is the general bracket with `A = 0`. -/
abbrev bracket (B : LinearMap.BilinForm 𝕜 M) :=
  LieSuperAlgebra.OneN.bracket 𝕜 M B (0 : Module.End 𝕜 M)

omit [Invertible (2 : 𝕜)] in
@[simp] theorem bracket_apply (B : LinearMap.BilinForm 𝕜 M) (x y : Space 𝕜 M) :
    bracket 𝕜 M B x y = (B x.2 y.2, 0) := by simp [bracket]

/-- The translation Lie superalgebra determined by a symmetric bilinear form. -/
@[instance_reducible]
noncomputable def lieSuperAlgebra (B : LinearMap.BilinForm 𝕜 M)
    (hB : B.IsSymm) : LieSuperAlgebra 𝕜 (Space 𝕜 M) :=
  LieSuperAlgebra.OneN.lieSuperAlgebra 𝕜 M B 0 hB
    (by simp [LieSuperAlgebra.OneN.IsSkewAdjoint])
    (by simp [LieSuperAlgebra.OneN.OddJacobi])

end LieSuperAlgebra.Translation
