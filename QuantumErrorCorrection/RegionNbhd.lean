/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import QuantumErrorCorrection.RegionCat
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Metric `l`-neighborhoods of regions

When the site set `X` carries a metric, every finite region `S : RegionCat X` has an
`l`-neighborhood `metricNbhd l S = {y | ∃ s ∈ S, dist y s ≤ l}`, the union of the closed balls of
radius `l` around its sites. For this to be a region again (a *finite* set) we need closed balls
in `X` to be finite, recorded by the class `FiniteClosedBalls X`. It holds for any finite `X`,
and for any proper, discrete metric space such as a lattice `ℤ^d` with a norm metric.

Since `S ⊆ T` implies `metricNbhd l S ⊆ metricNbhd l T`, taking the `l`-neighborhood is an
endofunctor `metricNbhdFunctor l : RegionCat X ⥤ RegionCat X`. As `l` varies, these functors
are related by natural transformations (automatically natural, `RegionCat X` being thin):

* `metricNbhdUnit l : 𝟭 _ ⟶ metricNbhdFunctor l`, since `S ⊆ metricNbhd l S`;
* `metricNbhdWeaken h : metricNbhdFunctor l ⟶ metricNbhdFunctor l'` for `l ≤ l'`;
* `metricNbhdComp l l' : metricNbhdFunctor l ⋙ metricNbhdFunctor l' ⟶ metricNbhdFunctor (l + l')`,
  by the triangle inequality.

These are what composing, and weakening the spread of, bounded-spread homomorphisms between
quasi-local algebras is built from (see `BoundedSpreadHom.lean`).
-/

@[expose] public noncomputable section

open CategoryTheory NNReal

universe u

/-- Every closed ball of a (pseudo)metric space `X` is finite. This is what makes the metric
neighborhood of a finite region a finite region again. -/
class FiniteClosedBalls (X : Type u) [PseudoMetricSpace X] : Prop where
  /-- Closed balls are finite. -/
  finite_closedBall : ∀ (x : X) (r : ℝ), (Metric.closedBall x r).Finite

/-- In a finite metric space, all closed balls are finite. -/
instance (priority := 100) FiniteClosedBalls.of_finite (X : Type u) [PseudoMetricSpace X]
    [Finite X] : FiniteClosedBalls X :=
  ⟨fun _ _ => Set.toFinite _⟩

/-- In a proper, discrete metric space (e.g. a lattice `ℤ^d` with a norm metric), closed balls
are compact, hence finite. -/
instance (priority := 100) FiniteClosedBalls.of_proper_discrete (X : Type u)
    [PseudoMetricSpace X] [ProperSpace X] [DiscreteTopology X] : FiniteClosedBalls X :=
  ⟨fun x r => (isCompact_closedBall x r).finite_of_discrete⟩

namespace RegionCat

variable {X : Type u} [MetricSpace X] [FiniteClosedBalls X] [DecidableEq X]

/-- The `l`-neighborhood of a region: all sites within distance `l` of some site of `S`, i.e. the
union of the closed balls of radius `l` around the sites of `S`. -/
def metricNbhd (l : ℝ≥0) (S : RegionCat X) : RegionCat X :=
  of (S.carrier.biUnion fun s => (FiniteClosedBalls.finite_closedBall s l).toFinset)

@[simp] theorem mem_metricNbhd {l : ℝ≥0} {S : RegionCat X} {y : X} :
    y ∈ (metricNbhd l S).carrier ↔ ∃ s ∈ S.carrier, dist y s ≤ l := by
  simp [metricNbhd, Metric.mem_closedBall]

/-- A region lies inside each of its neighborhoods. -/
theorem subset_metricNbhd (l : ℝ≥0) (S : RegionCat X) : S.carrier ⊆ (metricNbhd l S).carrier :=
  fun s hs => mem_metricNbhd.2 ⟨s, hs, by simp⟩

/-- Taking neighborhoods is monotone in the region. -/
theorem metricNbhd_mono (l : ℝ≥0) {S T : RegionCat X} (h : S.carrier ⊆ T.carrier) :
    (metricNbhd l S).carrier ⊆ (metricNbhd l T).carrier := fun y hy => by
  obtain ⟨s, hs, hys⟩ := mem_metricNbhd.1 hy
  exact mem_metricNbhd.2 ⟨s, h hs, hys⟩

/-- Taking neighborhoods is monotone in the radius. -/
theorem metricNbhd_mono_radius {l l' : ℝ≥0} (h : l ≤ l') (S : RegionCat X) :
    (metricNbhd l S).carrier ⊆ (metricNbhd l' S).carrier := fun y hy => by
  obtain ⟨s, hs, hys⟩ := mem_metricNbhd.1 hy
  exact mem_metricNbhd.2 ⟨s, hs, hys.trans (by exact_mod_cast h)⟩

/-- The triangle inequality: the `l'`-neighborhood of the `l`-neighborhood lies inside the
`(l + l')`-neighborhood. -/
theorem metricNbhd_metricNbhd_subset (l l' : ℝ≥0) (S : RegionCat X) :
    (metricNbhd l' (metricNbhd l S)).carrier ⊆ (metricNbhd (l + l') S).carrier := fun y hy => by
  obtain ⟨t, ht, hyt⟩ := mem_metricNbhd.1 hy
  obtain ⟨s, hs, hts⟩ := mem_metricNbhd.1 ht
  refine mem_metricNbhd.2 ⟨s, hs, ?_⟩
  calc dist y s ≤ dist y t + dist t s := dist_triangle y t s
    _ ≤ (l' : ℝ) + l := add_le_add hyt hts
    _ = ((l + l' : ℝ≥0) : ℝ) := by push_cast; ring

/-- The `0`-neighborhood of a region is the region itself. -/
@[simp] theorem metricNbhd_zero (S : RegionCat X) : metricNbhd 0 S = S := by
  obtain ⟨S⟩ := S
  unfold metricNbhd
  congr 1
  ext y
  simp

/-- The `l`-neighborhood as an endofunctor of `B(X)`. -/
def metricNbhdFunctor (l : ℝ≥0) : RegionCat X ⥤ RegionCat X where
  obj := metricNbhd l
  map f := homOfSubset (metricNbhd_mono l (subsetOfHom f))

@[simp] theorem metricNbhdFunctor_obj (l : ℝ≥0) (S : RegionCat X) :
    (metricNbhdFunctor l).obj S = metricNbhd l S := rfl

/-- Every region includes into its `l`-neighborhood. -/
def metricNbhdUnit (l : ℝ≥0) : 𝟭 (RegionCat X) ⟶ metricNbhdFunctor l where
  app S := homOfSubset (subset_metricNbhd l S)

/-- Enlarging the radius from `l` to `l' ≥ l`. -/
def metricNbhdWeaken {l l' : ℝ≥0} (h : l ≤ l') :
    metricNbhdFunctor l ⟶ metricNbhdFunctor l' (X := X) where
  app S := homOfSubset (metricNbhd_mono_radius h S)

/-- Neighborhoods compose subadditively in the radius (triangle inequality). -/
def metricNbhdComp (l l' : ℝ≥0) :
    metricNbhdFunctor l ⋙ metricNbhdFunctor l' ⟶ metricNbhdFunctor (l + l') (X := X) where
  app S := homOfSubset (metricNbhd_metricNbhd_subset l l' S)

end RegionCat
