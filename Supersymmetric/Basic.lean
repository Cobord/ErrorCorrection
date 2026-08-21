import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Data.ZMod.Basic

/-!
# Lie superalgebras

This file defines super vector spaces and Lie superalgebras.  A super vector space is represented
by an internal `ZMod 2`-grading.  The Lie superalgebra axioms are stated on homogeneous elements;
bilinearity then determines their extension to arbitrary elements.
-/

open DirectSum

universe u v

/-- A super vector space is a vector space with an internal decomposition into its even and odd
parts.  Degree `0` is the even part and degree `1` is the odd part. -/
class SuperVectorSpace (𝕜 : Type u) (V : Type v) [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V] where
  /-- The homogeneous component of a given parity. -/
  grading : ZMod 2 → Submodule 𝕜 V
  /-- Every vector decomposes uniquely as a sum of its homogeneous components. -/
  decomposition : DirectSum.Decomposition grading

variable (𝕜 : Type u) (V : Type v) [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [SuperVectorSpace 𝕜 V]

instance : DirectSum.Decomposition (SuperVectorSpace.grading (𝕜 := 𝕜) (V := V)) :=
  SuperVectorSpace.decomposition

namespace SuperVectorSpace

/-- The even part of a super vector space. -/
abbrev evenPart : Submodule 𝕜 V := grading (𝕜 := 𝕜) (V := V) 0

/-- The odd part of a super vector space. -/
abbrev oddPart : Submodule 𝕜 V := grading (𝕜 := 𝕜) (V := V) 1

end SuperVectorSpace

/-- The Koszul sign `(-1)^(i*j)` for parities `i` and `j`. -/
def koszulSign (i j : ZMod 2) : 𝕜 := if i = 1 ∧ j = 1 then -1 else 1

@[simp] theorem koszulSign_zero_left (i : ZMod 2) : koszulSign 𝕜 0 i = 1 := by
  simp [koszulSign]

@[simp] theorem koszulSign_zero_right (i : ZMod 2) : koszulSign 𝕜 i 0 = 1 := by
  simp [koszulSign]

@[simp] theorem koszulSign_one_one : koszulSign 𝕜 1 1 = -1 := by
  simp [koszulSign]

/-- A Lie superalgebra structure on a super vector space.

The bracket is bilinear and preserves parity.  Graded skew-symmetry and the graded Jacobi identity
are required for homogeneous elements. -/
class LieSuperAlgebra where
  /-- The super Lie bracket. -/
  bracket : V →ₗ[𝕜] V →ₗ[𝕜] V
  /-- The bracket of homogeneous elements has the sum of their parities. -/
  bracket_mem : ∀ {i j : ZMod 2} {x y : V},
    x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := V) i →
      y ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := V) j →
        bracket x y ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := V) (i + j)
  /-- Graded skew-symmetry on homogeneous elements. -/
  graded_skew : ∀ {i j : ZMod 2} {x y : V},
    x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := V) i →
      y ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := V) j →
        bracket x y = -(koszulSign 𝕜 i j) • bracket y x
  /-- The graded Jacobi identity on homogeneous elements. -/
  graded_jacobi : ∀ {i j k : ZMod 2} {x y z : V},
    x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := V) i →
      y ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := V) j →
        z ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := V) k →
        (koszulSign 𝕜 i k) • bracket x (bracket y z) +
          (koszulSign 𝕜 j i) • bracket y (bracket z x) +
            (koszulSign 𝕜 k j) • bracket z (bracket x y) = 0

namespace LieSuperAlgebra

universe w

variable {L : Type v} {W : Type w} [AddCommGroup L] [Module 𝕜 L] [SuperVectorSpace 𝕜 L]
  [lsa : LieSuperAlgebra 𝕜 L] [AddCommGroup W] [Module 𝕜 W] [SuperVectorSpace 𝕜 W]

/-- A representation of a Lie superalgebra `L` on a super vector space `W`.

The action is bilinear, takes a degree-`i` element of `L` and a degree-`j` vector of `W` to degree
`i + j`, and sends the superbracket to the supercommutator of endomorphisms. -/
structure Representation where
  /-- The bilinear action of `L` on `W`. -/
  action : L →ₗ[𝕜] W →ₗ[𝕜] W
  /-- The action respects the two gradings. -/
  action_mem : ∀ {i j : ZMod 2} {x : L} {w : W},
    x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := L) i →
      w ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := W) j →
        action x w ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := W) (i + j)
  /-- The action of the bracket is the graded commutator of the two actions. -/
  map_bracket : ∀ {i j : ZMod 2} {x y : L},
    x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := L) i →
      y ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := L) j →
        ∀ w : W,
          action (lsa.bracket x y) w =
            action x (action y w) - (koszulSign 𝕜 i j) • action y (action x w)

end LieSuperAlgebra
