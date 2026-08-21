/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Set.Card
public import ErrorCorrection.LinearECC

/-!
# Chromotopology

A Chromotopology has
- a simple graph
- vertices are colored by `Fq`
- There are `N` all differently `Fin N` colored
edges at each vertex.
- Restricting to the edges of only two different colors
gives the subgraph as a disjoint union of 4-cycles.


This also builds the quotient graph `l.quotientByCode`
of a `LinearECC` `l` by its `qi`
translations. In characteristic `2` and provided
that the code has no weight `1` vectors nor has
any of the form `e_i - e_j` (but `-1=+1`)
this gives a Chromotopology.

-/

@[expose] public section

open SimpleGraph Function

/-- The subgraph consisting only of the edges colored `i` or `j`. -/
def SimpleGraph.EdgeLabeling.doubleColorSubgraph {V : Type*} {G : SimpleGraph V} {N : ℕ}
    (C : G.EdgeLabeling (Fin N)) (i j : Fin N) : SimpleGraph V :=
  C.labelGraph i ⊔ C.labelGraph j

private lemma SimpleGraph.EdgeLabeling.doubleColorSubgraph_le {V : Type*} {G : SimpleGraph V} {N : ℕ}
    (C : G.EdgeLabeling (Fin N)) (i j : Fin N) : C.doubleColorSubgraph i j ≤ G :=
  sup_le C.labelGraph_le C.labelGraph_le

/-- A graph is a disjoint union of `4`-cycles
when every vertex with a neighbor has exactly two
neighbors (so the graph decomposes into cycles)
and every one of those cycles has exactly `4` vertices. -/
def SimpleGraph.IsUnionOfFourCycles {V : Type*} (G : SimpleGraph V) : Prop :=
  G.IsCycles ∧ ∀ v, (G.neighborSet v).Nonempty → (G.connectedComponentMk v).supp.ncard = 4

/-- `S` has no `G`-edges leaving it
every `G`-neighbor of a point of `S` is again in `S`
i.e. `S` is a union of `G`-connected components.
It does not have to be just one component.
-/
public def SimpleGraph.IsAdjClosed {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ w ∈ S, ∀ y, G.Adj w y → y ∈ S

public lemma SimpleGraph.ConnectedComponent.supp_isAdjClosed {V : Type*} {G : SimpleGraph V}
    (c : G.ConnectedComponent) : G.IsAdjClosed c.supp :=
  fun _w hw _y hadj => c.mem_supp_of_adj_mem_supp hw hadj

/--
A Chromotopology has
- a simple graph on `V`
- vertices are colored by `Fq`
- There are `N` all differently `Fin N` colored
edges at each vertex.
- Restricting to the edges of only two different colors
gives the subgraph as a disjoint union of 4-cycles.
-/
public structure Chromotopology
  (V : Type*)
  (hV : Fintype V)
  (N : ℕ)
  (Fq : Type*)
  where
  graph : SimpleGraph V
  graph_color : Coloring graph Fq
  graph_edge_colors : EdgeLabeling graph (Fin N)
  graph_edge_distinct (v : V) (k : Fin N) :
    ∃! w, ∃ h : graph.Adj v w, graph_edge_colors.get v w h = k
  graph_double_color_four_cycles (i j : Fin N) (hij : i ≠ j) :
    (graph_edge_colors.doubleColorSubgraph i j).IsUnionOfFourCycles

/-- Whether a `Chromotopology`'s graph is connected. -/
public def Chromotopology.IsConnected {V : Type*} {hV : Fintype V} {N : ℕ} {Fq : Type*}
    (Chr : Chromotopology V hV N Fq) : Prop := Chr.graph.Connected

section Isomorphism

/-- An isomorphism between two `Chromotopology`s
(necessarily sharing the same edge-color type
`Fin N`, since edge colors are required to match exactly)
- a graph isomorphism between their vertex sets
- under which corresponding edges carry the same `Fin N` label
- together with a map `colorMap` between their *vertex*-color codomains under which the vertex colorings commute.

`colorMap` need not itself be injective or surjective
-- e.g. comparing an `F2` chromotopology
to its image inside a larger `Fq`, vertex colors `0, 1 : ZMod 2` land on `0, a : Fq` for some
fixed nonzero `a`, but `Fq` may have many more elements than just those two. -/
public structure IsoChromotopology
    {V1 : Type*} {hV1 : Fintype V1} {N : ℕ} {Fq1 : Type*}
    {V2 : Type*} {hV2 : Fintype V2} {Fq2 : Type*}
    (C1 : Chromotopology V1 hV1 N Fq1) (C2 : Chromotopology V2 hV2 N Fq2) where
  /-- The underlying graph isomorphism. -/
  toIso : C1.graph ≃g C2.graph
  /-- The map on vertex colors, transported along `toIso`. Not required to be injective or
  surjective. -/
  colorMap : Fq1 → Fq2
  edge_colors_eq (x y : V1) (h : C1.graph.Adj x y) :
    C2.graph_edge_colors.get (toIso x) (toIso y) (toIso.map_rel_iff.mpr h)
      = C1.graph_edge_colors.get x y h
  vertex_color_comm (v : V1) : C2.graph_color (toIso v) = colorMap (C1.graph_color v)

end Isomorphism

/-! ### The chromotopology on an adjacency-closed subset -/
section Component

variable {V : Type*} {hV : Fintype V} {N : ℕ} {Fq : Type*}

private lemma reachable_mem_of_closed {H : SimpleGraph V} {S : Set V}
    (hclosed : H.IsAdjClosed S) {v u : V} (p : H.Walk v u)
    (hv : v ∈ S) : u ∈ S := by
  induction p with
  | nil => exact hv
  | cons h _ ih => exact ih (hclosed _ hv _ h)

private def Chromotopology.induceWalkOfClosed {H : SimpleGraph V} {S : Set V}
    (hclosed : H.IsAdjClosed S) {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) (p : H.Walk a b) : (H.induce S).Walk ⟨a, ha⟩ ⟨b, hb⟩ := by
  cases p with
  | nil => exact SimpleGraph.Walk.nil
  | @cons a c b hadj p' =>
    exact SimpleGraph.Walk.cons (SimpleGraph.induce_adj.mpr hadj)
      (Chromotopology.induceWalkOfClosed hclosed (hclosed a ha c hadj) hb p')

/-- Reachability in an induced subgraph
always implies reachability in the ambient graph -/
lemma SimpleGraph.induce_reachable_ambient {H : SimpleGraph V} {S : Set V} {x y : S}
    (h : (H.induce S).Reachable x y) : H.Reachable (x : V) (y : V) := by
  obtain ⟨p⟩ := h
  exact ⟨p.map (SimpleGraph.Embedding.induce S).toHom⟩

/-- The image, under the inclusion `S ↪ V`
of a connected component of `H.induce S` is exactly
the corresponding connected component of `H`
provided `S` is closed under `H`-adjacency. -/
private lemma Chromotopology.image_supp_connectedComponentMk_of_closed
    {H : SimpleGraph V} {S : Set V} (hclosed : H.IsAdjClosed S) (x : S) :
    Subtype.val '' ((H.induce S).connectedComponentMk x).supp
      = (H.connectedComponentMk (x : V)).supp := by
  ext z
  simp only [Set.mem_image, SimpleGraph.ConnectedComponent.mem_supp_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hreach : (H.induce S).Reachable y x := SimpleGraph.ConnectedComponent.eq.mp hy
    exact SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.induce_reachable_ambient hreach)
  · intro hz
    have hreach' : H.Reachable (x : V) z := (SimpleGraph.ConnectedComponent.eq.mp hz).symm
    have hzS : z ∈ S := reachable_mem_of_closed hclosed hreach'.some x.2
    have hreach : H.Reachable z (x : V) := hreach'.symm
    exact ⟨⟨z, hzS⟩,
      SimpleGraph.ConnectedComponent.eq.mpr
        ⟨Chromotopology.induceWalkOfClosed hclosed hzS x.2 hreach.some⟩, rfl⟩

/-- `IsUnionOfFourCycles` transfers to the induced graph
on a closed set
since no edge leaves `S`
both the per-vertex neighbor count
and the size of each connected component are unchanged
by restricting to `S`. -/
private lemma Chromotopology.isUnionOfFourCycles_induce_of_closed
    {H : SimpleGraph V} {S : Set V} (hclosed : H.IsAdjClosed S)
    (hcyc : H.IsUnionOfFourCycles) : (H.induce S).IsUnionOfFourCycles := by
  obtain ⟨hcycles, hfour⟩ := hcyc
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · have hne := H.neighborSet_induce S v
    rw [hne] at hv ⊢
    obtain ⟨y, hy⟩ := hv
    have hsub : H.neighborSet (v : V) ⊆ S := fun z hz => hclosed v v.2 z hz
    rw [Set.ncard_preimage_of_injective_subset_range Subtype.coe_injective
      (by rw [Subtype.range_coe]; exact hsub)]
    exact hcycles ⟨y.val, hy⟩
  · have hne := H.neighborSet_induce S v
    rw [hne] at hv
    obtain ⟨y, hy⟩ := hv
    have himg := Chromotopology.image_supp_connectedComponentMk_of_closed hclosed v
    have hncard : (Subtype.val '' ((H.induce S).connectedComponentMk v).supp).ncard
        = ((H.induce S).connectedComponentMk v).supp.ncard :=
      Set.ncard_image_of_injective _ Subtype.coe_injective
    rw [himg] at hncard
    rw [← hncard]
    exact hfour v.val ⟨y.val, hy⟩

/-- The `Chromotopology` induced on
any `Chr.graph`-adjacency-closed subset `S`
the graph, coloring, and edge-labeling of `Chr` restricted to `S`.
This is well-defined for *any* closed
`S` (not just a connected component's `supp`) -/
public noncomputable def Chromotopology.restrict (Chr : Chromotopology V hV N Fq)
    (S : Set V) (hS : Chr.graph.IsAdjClosed S) :
    Chromotopology S (haveI := hV; Fintype.ofFinite S) N Fq where
  graph := Chr.graph.induce S
  graph_color := Chr.graph_color.comap (SimpleGraph.Embedding.induce S).toHom
  graph_edge_colors := SimpleGraph.EdgeLabeling.mk
    (fun x y hxy => Chr.graph_edge_colors.get x.val y.val hxy)
    (fun x y hxy => Chr.graph_edge_colors.get_comm x.val y.val hxy.symm)
  graph_edge_distinct := fun v k => by
    obtain ⟨w0, ⟨h0, hcolor0⟩, huniq⟩ := Chr.graph_edge_distinct v.val k
    have hw0 : w0 ∈ S := hS v.val v.2 w0 h0
    refine ⟨⟨w0, hw0⟩, ⟨h0, hcolor0⟩, ?_⟩
    rintro ⟨w, hw⟩ ⟨h, hcolor⟩
    exact Subtype.ext (huniq w ⟨h, hcolor⟩)
  graph_double_color_four_cycles := fun i j hij => by
    have hgraph_eq :
        (SimpleGraph.EdgeLabeling.mk
          (fun x y hxy => Chr.graph_edge_colors.get x.val y.val hxy)
          (fun x y hxy => Chr.graph_edge_colors.get_comm x.val y.val hxy.symm) :
            SimpleGraph.EdgeLabeling (Chr.graph.induce S) (Fin N)).doubleColorSubgraph i j
        = (Chr.graph_edge_colors.doubleColorSubgraph i j).induce S := by
      ext x y
      simp only [SimpleGraph.EdgeLabeling.doubleColorSubgraph, SimpleGraph.sup_adj,
        SimpleGraph.EdgeLabeling.labelGraph_adj, SimpleGraph.induce_adj]
      constructor
      · rintro (⟨h, hc⟩ | ⟨h, hc⟩)
        · exact Or.inl ⟨h, hc⟩
        · exact Or.inr ⟨h, hc⟩
      · rintro (⟨h, hc⟩ | ⟨h, hc⟩)
        · exact Or.inl ⟨h, hc⟩
        · exact Or.inr ⟨h, hc⟩
    have hclosed : (Chr.graph_edge_colors.doubleColorSubgraph i j).IsAdjClosed S :=
      fun w hw y hadj => hS w hw y (SimpleGraph.EdgeLabeling.doubleColorSubgraph_le _ i j hadj)
    rw [hgraph_eq]
    exact Chromotopology.isUnionOfFourCycles_induce_of_closed hclosed
      (Chr.graph_double_color_four_cycles i j hij)

@[simp] private lemma Chromotopology.restrict_graph_color_apply (Chr : Chromotopology V hV N Fq)
    (S : Set V) (hS : Chr.graph.IsAdjClosed S) (v : S) :
    (Chr.restrict S hS).graph_color v = Chr.graph_color v.val := rfl

/-- Reachability inside a `Chromotopology.restrict`
implies reachability in the ambient `Chromotopology` -/
private lemma Chromotopology.restrict_reachable_ambient (Chr : Chromotopology V hV N Fq)
    (S : Set V) (hS : Chr.graph.IsAdjClosed S) {x y : S}
    (h : (Chr.restrict S hS).graph.Reachable x y) : Chr.graph.Reachable (x : V) (y : V) :=
  SimpleGraph.induce_reachable_ambient h

/-- The `Chromotopology` induced on
a connected component `c` of `Chr.graph`
This is a special case of
`Chromotopology.restrict`
since a connected component's `supp`
is always closed under adjacency. -/
public noncomputable def Chromotopology.component (Chr : Chromotopology V hV N Fq)
    (c : Chr.graph.ConnectedComponent) :
    Chromotopology c (haveI := hV; Fintype.ofFinite c) N Fq :=
  Chr.restrict c.supp c.supp_isAdjClosed

end Component

section QuotientByCode

variable {n k : ℕ}
variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq Fq]

namespace LinearECC

variable (l : LinearECC (n:=n) (k:=k) (Fq:=Fq))
variable (shift_scale : Units Fq)

/-- `x` and `y` are joined by a color-`i` edge
`y` is reached from `x` by translating
by a multiple of `indicator i`. -/
def Adj (x y : l.quotientByCode) : Prop := ∃ i, y = l.qi shift_scale i x

omit [Fintype Fq] [DecidableEq Fq] in
/-- `Adj` is symmetric precisely because
`qi i` is an involution.
This needs characteristic `2`
This is an explicit hypothesis `h2`
rather than an ambient Char instance. -/
lemma Adj.symm (h2 : (2 : Fq) = (0 : Fq)) {x y : l.quotientByCode}
  (h : l.Adj shift_scale x y) :
  l.Adj shift_scale y x := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨i, (l.qi_square shift_scale h2 i x).symm⟩

omit [Fintype Fq] [DecidableEq Fq] in
/-- No color-`i` edge is a self-loop
provided no `indicator i` lies in the code
this holds whenever `l` has minimum distance `≥ 2`
-/
lemma Adj.irrefl (hnz : ∀ i, indicator i ∉ l.subspace) {x : l.quotientByCode} :
    ¬ l.Adj shift_scale x x := by
  rintro ⟨i, hi⟩
  apply hnz i
  have h' : x + Submodule.Quotient.mk (shift_scale • indicator i) = x + 0 := by
    rw [add_zero]
    exact hi.symm
  rw [add_zero] at h'
  rw [add_comm] at h'
  rw [add_eq_right] at h'
  rw [Submodule.Quotient.mk_smul] at h'
  have _ : Invertible shift_scale :=
    ⟨shift_scale⁻¹, inv_mul_cancel shift_scale, mul_inv_cancel shift_scale⟩
  rw [smul_eq_iff_eq_invOf_smul (c:=shift_scale)] at h'
  rw [smul_zero] at h'
  exact (Submodule.Quotient.mk_eq_zero (p := l.subspace)).mp h'

/-- The quotient graph on `l.quotientByCode`
with `x` adjacent to `y` when some `qi i` carries `x` to `y`.
Needs characteristic `2` for undirectedness
and the absence of weight-`1` codewords for irreflexivity -/
public def graph (h2 : (2 : Fq) = (0 : Fq)) (hnz : ∀ i, indicator i ∉ l.subspace) :
    SimpleGraph l.quotientByCode where
  Adj := l.Adj shift_scale
  symm := ⟨fun _ _ => Adj.symm l shift_scale h2⟩
  loopless := ⟨fun _ => Adj.irrefl l shift_scale hnz⟩

noncomputable instance : Fintype l.quotientByCode :=
  have : Finite l.quotientByCode :=
    Finite.of_surjective (Submodule.Quotient.mk (p := l.subspace))
      (Submodule.Quotient.mk_surjective l.subspace)
  Fintype.ofFinite _

omit [Fintype Fq] [DecidableEq Fq] in
private lemma qi_injective
  (h2 : (2 : Fq) = (0 : Fq)) (i : Fin n) :
  Function.Injective (l.qi shift_scale i) :=
  Function.LeftInverse.injective (l.qi_square shift_scale h2 i)

omit [Fintype Fq] [DecidableEq Fq] in
private lemma qi_ne_self
  (hnz : ∀ i, indicator i ∉ l.subspace) (i : Fin n) (x : l.quotientByCode) :
    l.qi shift_scale i x ≠ x :=
  fun h => Adj.irrefl l shift_scale hnz (x := x) ⟨i, h.symm⟩

omit [Fintype Fq] [DecidableEq Fq] in
/-- Two different translations `qi i` and `qi j`
never send `x` to the same vertex, provided
the difference `indicator i - indicator j`
is never a codeword.
One way to acheive this is not to have anything
of weight `2` like double even codes.
However, there can be weight `2` vectors like
`indicator i - α*indicator j` with `α ≠ 0,1`
if `Fq` is not `ℤ/2ℤ`.
It can even still be characteristic `2`. -/
private lemma qi_ne_qi
  (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
  {i j : Fin n} (hij : i ≠ j) (x : l.quotientByCode) :
  l.qi shift_scale i x ≠ l.qi shift_scale j x := by
  intro heq
  apply hNoDiff i j hij
  have heq' : (Submodule.Quotient.mk (shift_scale • indicator i) : l.quotientByCode)
      = Submodule.Quotient.mk (shift_scale • indicator j) := add_left_cancel heq
  repeat rw [Submodule.Quotient.mk_smul] at heq'
  have inv_shift_scale : Invertible shift_scale :=
    ⟨shift_scale⁻¹, inv_mul_cancel shift_scale, mul_inv_cancel shift_scale⟩
  rw [smul_eq_iff_eq_invOf_smul (c:=shift_scale)] at heq'
  rw [<-smul_assoc, smul_eq_mul] at heq'
  rw [inv_shift_scale.invOf_mul_self, one_smul] at heq'
  exact (Submodule.Quotient.eq l.subspace).mp heq'

/-! ### An `Fq`-valued coloring: the sum of a representative's coordinates -/

omit [Fintype Fq] [DecidableEq Fq] in
lemma coordSum_well_defined
    (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq)) :
    ∀ v w : Fqn (n:=n) (Fq:=Fq), Submodule.quotientRel l.subspace v w →
      (∑ i, v i) = ∑ i, w i := by
  intro v w h
  rw [Submodule.quotientRel_def] at h
  have hz := hZeroSum _ h
  simp only [Pi.sub_apply] at hz
  rw [Finset.sum_sub_distrib] at hz
  exact sub_eq_zero.mp hz

/-- The sum of the coordinates of
a (any) representative bitstring
well-defined on the quotient because `hZeroSum`
says every codeword's coordinates sum to `0`. -/
noncomputable def colorFq (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq)) :
    l.quotientByCode → Fq :=
  Quotient.lift (fun v => ∑ i, v i) (coordSum_well_defined l hZeroSum)

omit [Fintype Fq] [DecidableEq Fq] in
@[simp] private lemma colorFq_mk (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq))
    (v : Fqn (n:=n) (Fq:=Fq)) :
    l.colorFq hZeroSum (Submodule.Quotient.mk v) = ∑ i, v i := rfl

omit [Fintype Fq] [DecidableEq Fq] in
/-- One `qi` step changes the coordinate-sum color
by exactly `shift_scale`, regardless of
which coordinate is translated. -/
private lemma colorFq_qi (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq)) (i : Fin n)
    (x : l.quotientByCode) :
    l.colorFq hZeroSum (l.qi shift_scale i x) = l.colorFq hZeroSum x + (shift_scale : Fq) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective l.subspace x
  have hy : (l.qi shift_scale i (Submodule.Quotient.mk v) : l.quotientByCode)
      = Submodule.Quotient.mk (v + shift_scale • indicator i) := by
    unfold qi
    rw [Submodule.Quotient.mk_add]
    abel
  rw [hy, colorFq_mk, colorFq_mk]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  congr 1
  unfold indicator
  rw [Units.smul_def]
  simp

/-- The coordinate-sum coloring:
adjacent vertices differ by translating
one coordinate by
`shift_scale` (`colorFq_qi`), and `shift_scale ≠ 0`. -/
public noncomputable def coloringFq
  (h2 : (2 : Fq) = (0 : Fq)) (hnz : ∀ i, indicator i ∉ l.subspace)
  (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq)) :
  Coloring (l.graph shift_scale h2 hnz) Fq :=
  Coloring.mk (l.colorFq hZeroSum) (by
    rintro x y ⟨i, rfl⟩
    rw [l.colorFq_qi shift_scale hZeroSum i x]
    simp)

omit [Fintype Fq] [DecidableEq Fq] in
/-- If `x` and `y` are connected in the quotient graph,
their coordinate-sum colors are either
equal or differ by exactly `shift_scale`
every single `qi` step changes the color by
`shift_scale` (`colorFq_qi`), and two steps cancel back to `0`
since `shift_scale + shift_scale
= 0` in characteristic `2` -/
private theorem colorFq_reachable_diff (h2 : (2 : Fq) = (0 : Fq)) (hnz : ∀ i, indicator i ∉ l.subspace)
    (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq)) {x y : l.quotientByCode}
    (h : (l.graph shift_scale h2 hnz).Reachable x y) :
    l.colorFq hZeroSum y = l.colorFq hZeroSum x ∨
      l.colorFq hZeroSum y = l.colorFq hZeroSum x + (shift_scale : Fq) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Or.inl rfl
  | @cons x mid y hadj p' ih =>
    obtain ⟨i, rfl⟩ := hadj
    have hstep := l.colorFq_qi shift_scale hZeroSum i x
    have hcancel : (shift_scale : Fq) + shift_scale = 0 := by rw [← two_mul, h2, zero_mul]
    rcases ih with ih | ih
    · exact Or.inr (by rw [ih, hstep])
    · exact Or.inl (by rw [ih, hstep, add_assoc, hcancel, add_zero])

/-! ### The `Fin n` edge coloring -/

omit [Fintype Fq] [DecidableEq Fq] in
/-- Given `l` has no codeword
`indicator i - indicator j` for `i ≠ j`,
the color `i` witnessing `Adj x y` is unique. -/
lemma exists_unique_qi_eq
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    {x y : l.quotientByCode} (hAdj : l.Adj shift_scale x y) : ∃! i, y = l.qi shift_scale i x := by
  obtain ⟨i0, hi0⟩ := hAdj
  refine ⟨i0, hi0, fun j hj => ?_⟩
  by_contra hij
  exact qi_ne_qi l shift_scale hNoDiff (Ne.symm hij) x (hi0.symm.trans hj)

/-- The color of the edge between adjacent `x` and `y`:
the unique `i` with `y = qi i x`. -/
noncomputable def edgeColorOf
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    {x y : l.quotientByCode} (hAdj : l.Adj shift_scale x y) : Fin n :=
  (exists_unique_qi_eq l shift_scale hNoDiff hAdj).choose

omit [Fintype Fq] [DecidableEq Fq] in
private lemma edgeColorOf_spec
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    {x y : l.quotientByCode} (hAdj : l.Adj shift_scale x y) :
    y = l.qi shift_scale (edgeColorOf l shift_scale hNoDiff hAdj) x :=
  (exists_unique_qi_eq l shift_scale hNoDiff hAdj).choose_spec.1

omit [Fintype Fq] [DecidableEq Fq] in
private lemma edgeColorOf_unique
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    {x y : l.quotientByCode} (hAdj : l.Adj shift_scale x y) {i : Fin n} (hi : y = l.qi shift_scale i x) :
    i = edgeColorOf l shift_scale hNoDiff hAdj :=
  (exists_unique_qi_eq l shift_scale hNoDiff hAdj).choose_spec.2 i hi

omit [Fintype Fq] [DecidableEq Fq] in
lemma edgeColorOf_symm (h2 : (2 : Fq) = (0 : Fq))
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    {x y : l.quotientByCode} (hAdj : l.Adj shift_scale x y) :
    edgeColorOf l shift_scale hNoDiff (Adj.symm l shift_scale h2 hAdj) = edgeColorOf l shift_scale hNoDiff hAdj := by
  refine (edgeColorOf_unique l shift_scale hNoDiff (Adj.symm l shift_scale h2 hAdj) ?_).symm
  have hspec := edgeColorOf_spec l shift_scale hNoDiff hAdj
  generalize hi0 : edgeColorOf l shift_scale hNoDiff hAdj = i0 at hspec ⊢
  rw [hspec]
  exact (l.qi_square shift_scale h2 i0 x).symm

/-- The `Fin n` edge coloring of `graph`
well-defined because `l` has no codeword
`indicator i - indicator j` for `i ≠ j`. -/
noncomputable def graphEdgeColors (h2 : (2 : Fq) = (0 : Fq))
    (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace) :
    EdgeLabeling (l.graph shift_scale h2 hnz) (Fin n) :=
  EdgeLabeling.mk (fun _ _ hAdj => edgeColorOf l shift_scale hNoDiff hAdj)
    (fun _ _ hAdj => edgeColorOf_symm l shift_scale h2 hNoDiff hAdj)

omit [Fintype Fq] [DecidableEq Fq] in
private lemma labelGraph_adj_iff (h2 : (2 : Fq) = (0 : Fq)) (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    (i : Fin n) (x y : l.quotientByCode) :
    ((graphEdgeColors l shift_scale h2 hnz hNoDiff).labelGraph i).Adj x y ↔ y = l.qi shift_scale i x := by
  rw [EdgeLabeling.labelGraph_adj]
  constructor
  · rintro ⟨H, hcolor⟩
    have hcolor' : edgeColorOf l shift_scale hNoDiff H = i := hcolor
    rw [← hcolor']
    exact edgeColorOf_spec l shift_scale hNoDiff H
  · intro hy
    refine ⟨⟨i, hy⟩, ?_⟩
    show edgeColorOf l shift_scale hNoDiff (⟨i, hy⟩ : l.Adj shift_scale x y) = i
    exact (edgeColorOf_unique l shift_scale hNoDiff ⟨i, hy⟩ hy).symm

omit [Fintype Fq] [DecidableEq Fq] in
lemma graph_edge_distinct (h2 : (2 : Fq) = (0 : Fq)) (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    (v : l.quotientByCode) (k : Fin n) :
    ∃! w, ∃ h : (l.graph shift_scale h2 hnz).Adj v w, (graphEdgeColors l shift_scale h2 hnz hNoDiff).get v w h = k := by
  refine ⟨l.qi shift_scale k v, ⟨⟨k, rfl⟩, ?_⟩, ?_⟩
  · show edgeColorOf l shift_scale hNoDiff (⟨k, rfl⟩ : l.Adj shift_scale v (l.qi shift_scale k v)) = k
    exact (edgeColorOf_unique l shift_scale hNoDiff ⟨k, rfl⟩ rfl).symm
  · rintro w ⟨h, hcolor⟩
    have hcolor' : edgeColorOf l shift_scale hNoDiff h = k := hcolor
    rw [← hcolor']
    exact edgeColorOf_spec l shift_scale hNoDiff h

/-! ### The `2`-color `4`-cycle condition -/

omit [Fintype Fq] [DecidableEq Fq] in
private lemma doubleColorSubgraph_adj_iff (h2 : (2 : Fq) = (0 : Fq))
    (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    (i j : Fin n) (x y : l.quotientByCode) :
    ((graphEdgeColors l shift_scale h2 hnz hNoDiff).doubleColorSubgraph i j).Adj x y ↔
      y = l.qi shift_scale i x ∨ y = l.qi shift_scale j x := by
  show ((graphEdgeColors l shift_scale h2 hnz hNoDiff).labelGraph i ⊔
    (graphEdgeColors l shift_scale h2 hnz hNoDiff).labelGraph j).Adj x y ↔ _
  rw [sup_adj, labelGraph_adj_iff, labelGraph_adj_iff]

omit [Fintype Fq] [DecidableEq Fq] in
private lemma doubleColorSubgraph_neighborSet_eq (h2 : (2 : Fq) = (0 : Fq))
    (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    {i j : Fin n} (_hij : i ≠ j) (v : l.quotientByCode) :
    ((graphEdgeColors l shift_scale h2 hnz hNoDiff).doubleColorSubgraph i j).neighborSet v
      = {l.qi shift_scale i v, l.qi shift_scale j v} := by
  ext y
  simp only [SimpleGraph.mem_neighborSet, doubleColorSubgraph_adj_iff l shift_scale h2 hnz hNoDiff,
    Set.mem_insert_iff, Set.mem_singleton_iff]

omit [Fintype Fq] [DecidableEq Fq] in
private lemma doubleColorSubgraph_isCycles (h2 : (2 : Fq) = (0 : Fq))
    (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    {i j : Fin n} (hij : i ≠ j) :
    ((graphEdgeColors l shift_scale h2 hnz hNoDiff).doubleColorSubgraph i j).IsCycles := by
  intro v _
  rw [doubleColorSubgraph_neighborSet_eq l shift_scale h2 hnz hNoDiff hij]
  exact Set.ncard_pair (qi_ne_qi l shift_scale hNoDiff hij v)

omit [Fintype Fq] [DecidableEq Fq] in
private lemma doubleColorSubgraph_supp_eq (h2 : (2 : Fq) = (0 : Fq))
    (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    {i j : Fin n} (_hij : i ≠ j) (v : l.quotientByCode) :
    (((graphEdgeColors l shift_scale h2 hnz hNoDiff).doubleColorSubgraph i j).connectedComponentMk v).supp
      = {v, l.qi shift_scale i v, l.qi shift_scale j v, l.qi shift_scale i (l.qi shift_scale j v)} := by
  set H := (graphEdgeColors l shift_scale h2 hnz hNoDiff).doubleColorSubgraph i j with hHdef
  set comp := H.connectedComponentMk v with hcomp_def
  have adj_iff := doubleColorSubgraph_adj_iff l shift_scale h2 hnz hNoDiff i j
  have hva : H.Adj v (l.qi shift_scale i v) := (adj_iff v _).mpr (Or.inl rfl)
  have hvb : H.Adj v (l.qi shift_scale j v) := (adj_iff v _).mpr (Or.inr rfl)
  have hac : H.Adj (l.qi shift_scale i v) (l.qi shift_scale i (l.qi shift_scale j v)) := by
    rw [l.qij_comm]
    exact (adj_iff _ _).mpr (Or.inr rfl)
  have hv_mem : v ∈ comp.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have ha_mem : l.qi shift_scale i v ∈ comp.supp := (comp.mem_supp_congr_adj hva).mp hv_mem
  have hb_mem : l.qi shift_scale j v ∈ comp.supp := (comp.mem_supp_congr_adj hvb).mp hv_mem
  have hc_mem : l.qi shift_scale i (l.qi shift_scale j v) ∈ comp.supp := (comp.mem_supp_congr_adj hac).mp ha_mem
  have hclosed : ∀ w ∈ ({v, l.qi shift_scale i v, l.qi shift_scale j v, l.qi shift_scale i (l.qi shift_scale j v)} : Set l.quotientByCode),
      ∀ y, H.Adj w y → y ∈ ({v, l.qi shift_scale i v, l.qi shift_scale j v, l.qi shift_scale i (l.qi shift_scale j v)} : Set l.quotientByCode) := by
    rintro w hw y hwy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw | hw | hw <;> rw [hw] at hwy
    · rcases (adj_iff v y).mp hwy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · rcases (adj_iff (l.qi shift_scale i v) y).mp hwy with rfl | rfl
      · rw [l.qi_square shift_scale h2]; exact Or.inl rfl
      · rw [l.qij_comm]; exact Or.inr (Or.inr (Or.inr rfl))
    · rcases (adj_iff (l.qi shift_scale j v) y).mp hwy with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr rfl))
      · rw [l.qi_square shift_scale h2]; exact Or.inl rfl
    · rcases (adj_iff (l.qi shift_scale i (l.qi shift_scale j v)) y).mp hwy with rfl | rfl
      · rw [l.qi_square shift_scale h2]; exact Or.inr (Or.inr (Or.inl rfl))
      · rw [← l.qij_comm, l.qi_square shift_scale h2]; exact Or.inr (Or.inl rfl)
  ext w
  constructor
  · intro hw
    have heq : H.connectedComponentMk v = H.connectedComponentMk w :=
      (show H.connectedComponentMk w = comp from hw).symm
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.eq.mp heq
    exact reachable_mem_of_closed hclosed p (Set.mem_insert v _)
  · rintro (rfl | rfl | rfl | rfl)
    · exact hv_mem
    · exact ha_mem
    · exact hb_mem
    · exact hc_mem

omit [Fintype Fq] [DecidableEq Fq] in
/-- The Adinkra `2`-color `4`-cycle condition:
since translation by codewords is
commutative (`qij_comm`), the `(i,j)`-double-color component
through any `v` is exactly the `4`-vertex square `v, qi i v, qi j v, qi i (qi j v)`. -/
lemma graph_double_color_four_cycles (h2 : (2 : Fq) = (0 : Fq))
    (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    (i j : Fin n) (hij : i ≠ j) :
    ((graphEdgeColors l shift_scale h2 hnz hNoDiff).doubleColorSubgraph i j).IsUnionOfFourCycles := by
  refine ⟨doubleColorSubgraph_isCycles l shift_scale h2 hnz hNoDiff hij, fun v _ => ?_⟩
  rw [doubleColorSubgraph_supp_eq l shift_scale h2 hnz hNoDiff hij v]
  refine Set.ncard_eq_four.mpr
    ⟨v, l.qi shift_scale i v, l.qi shift_scale j v, l.qi shift_scale i (l.qi shift_scale j v), ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · exact (qi_ne_self l shift_scale hnz i v).symm
  · exact (qi_ne_self l shift_scale hnz j v).symm
  · exact fun h =>
      qi_ne_qi l shift_scale hNoDiff hij v ((congrArg (l.qi shift_scale i) h).trans (l.qi_square shift_scale h2 i (l.qi shift_scale j v)))
  · exact qi_ne_qi l shift_scale hNoDiff hij v
  · exact fun h => (qi_ne_self l shift_scale hnz j v).symm (qi_injective l shift_scale h2 i h)
  · exact (qi_ne_self l shift_scale hnz i (l.qi shift_scale j v)).symm

/-! ### Assembling the `Chromotopology` -/

/-- The quotient `l.quotientByCode` as an honest `Chromotopology`
for any field `Fq`, given:
- characteristic `2` (`h2`, for undirectedness)
- no weight-`1` codewords (`hnz`, for irreflexivity)
- no `indicator i - indicator j` codeword for `i ≠ j` (`hNoDiff`,
for well-defined edge colors)
- coordinate-sums vanishing on the code (`hZeroSum`, for
the `Fq`-valued coloring). -/
public noncomputable def quotientChromotopology
    (h2 : (2 : Fq) = (0 : Fq))
    (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq)) :
    Chromotopology l.quotientByCode inferInstance n Fq where
  graph := l.graph shift_scale h2 hnz
  graph_color := l.coloringFq shift_scale h2 hnz hZeroSum
  graph_edge_colors := l.graphEdgeColors shift_scale h2 hnz hNoDiff
  graph_edge_distinct := l.graph_edge_distinct shift_scale h2 hnz hNoDiff
  graph_double_color_four_cycles := l.graph_double_color_four_cycles shift_scale h2 hnz hNoDiff

omit [DecidableEq Fq] in
@[simp] public lemma quotientChromotopology_graph_color (h2 : (2 : Fq) = (0 : Fq))
    (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq)) (v : l.quotientByCode) :
    (l.quotientChromotopology shift_scale h2 hnz hNoDiff hZeroSum).graph_color v
      = l.colorFq hZeroSum v := rfl

omit [DecidableEq Fq] in
/-- The same conclusion as `colorFq_reachable_diff`
but for reachability inside *any*
restriction of the quotient chromotopology `l.quotientChromotopology`
e.g.
`l.hammingChromotopology`, or any other choice of closed subset `S`.
Reachability inside the restriction implies reachability in the ambient quotient graph
(`Chromotopology.restrict_reachable_ambient`), which is where `colorFq_reachable_diff` applies. -/
public theorem restrict_colorFq_reachable_diff (h2 : (2 : Fq) = (0 : Fq))
    (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq))
    (S : Set l.quotientByCode) (hS : (l.graph shift_scale h2 hnz).IsAdjClosed S)
    {x y : S}
    (h : ((l.quotientChromotopology shift_scale h2 hnz hNoDiff hZeroSum).restrict S hS).graph.Reachable x y) :
    l.colorFq hZeroSum (y : l.quotientByCode) = l.colorFq hZeroSum (x : l.quotientByCode) ∨
      l.colorFq hZeroSum (y : l.quotientByCode)
        = l.colorFq hZeroSum (x : l.quotientByCode) + (shift_scale : Fq) :=
  l.colorFq_reachable_diff shift_scale h2 hnz hZeroSum
    (Chromotopology.restrict_reachable_ambient _ S hS h)

/-! ### The image of the Hamming cube is a component -/
section HammingComponent

omit [Fintype Fq] [DecidableEq Fq] in
/-- The embedding of the Hamming cube `Fin n → Bool`
(i.e. `Z_2^n`) into `Fqn`, sending each
coordinate `0 ↦ 0`, `1 ↦ shift_scale`. -/
public def hammingEmbed (v : Fin n → Bool) : Fqn (n:=n) (Fq:=Fq) :=
  fun i => if v i then (shift_scale : Fq) else 0

omit [Fintype Fq] [DecidableEq Fq] in
/-- Flipping the `i`-th coordinate of `v` translates
`hammingEmbed v` by `shift_scale • indicator i`,
regardless of which way the bit flips
turning a `0` into `shift_scale` adds it,
and (using characteristic `2`, via `h2`) turning a `shift_scale` back into `0`
also amounts to adding it
since `shift_scale + shift_scale = 0`. -/
private lemma hammingEmbed_update (h2 : (2 : Fq) = (0 : Fq)) (v : Fin n → Bool) (i : Fin n) :
    hammingEmbed shift_scale (Function.update v i !(v i))
      = hammingEmbed shift_scale v + (shift_scale : Fq) • indicator i := by
  have hcancel : (shift_scale : Fq) + shift_scale = 0 := by rw [← two_mul, h2, zero_mul]
  funext j
  simp only [hammingEmbed, Pi.add_apply, Pi.smul_apply, indicator, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self, ite_eq_left rfl, mul_one]
    cases v i with
    | false => simp
    | true => simp [hcancel]
  · rw [Function.update_of_ne (Ne.symm hij), ite_eq_right hij, mul_zero, add_zero]

omit [Fintype Fq] [DecidableEq Fq] in
/-- The composite map
from the Hamming cube to the quotient
embed via `hammingEmbed`, then
reduce mod the code. -/
def hammingProj (v : Fin n → Bool) : l.quotientByCode :=
  Submodule.Quotient.mk (hammingEmbed shift_scale v)

omit [Fintype Fq] [DecidableEq Fq] in
/-- Flipping the `i`-th coordinate of `v`
is exactly translation by `qi shift_scale i`. -/
private lemma hammingProj_qi (h2 : (2 : Fq) = (0 : Fq)) (v : Fin n → Bool) (i : Fin n) :
    l.hammingProj shift_scale (Function.update v i !(v i))
      = l.qi shift_scale i (l.hammingProj shift_scale v) := by
  show Submodule.Quotient.mk (hammingEmbed shift_scale (Function.update v i !(v i)))
      = Submodule.Quotient.mk (hammingEmbed shift_scale v)
        + Submodule.Quotient.mk ((shift_scale : Fq) • indicator i)
  rw [← Submodule.Quotient.mk_add, ← hammingEmbed_update shift_scale h2 v i]

omit [Fintype Fq] [DecidableEq Fq] in
/-- The image, in the quotient `l.quotientByCode`
of the Hamming cube `Fin n → Bool` under
`hammingProj`. -/
def hammingImage : Set l.quotientByCode :=
  Set.range (l.hammingProj shift_scale)

omit [Fintype Fq] [DecidableEq Fq] in
/-- The Hamming-cube image has no edges leaving it
every `qi`-neighbor of a residue in the
image is again in the image, reached by flipping the corresponding bit (`hammingProj_qi`). In
particular `l.hammingImage shift_scale` is a *component*, in the general,
not-necessarily-connected sense of `SimpleGraph.IsAdjClosed`, of the quotient graph -- whether
or not it happens to be connected is a separate question, addressed below by
`hammingImage_connected`, not part of this claim. -/
private theorem hammingImage_isAdjClosed_aux (h2 : (2 : Fq) = (0 : Fq)) :
    ∀ x ∈ l.hammingImage shift_scale, ∀ y, l.Adj shift_scale x y → y ∈ l.hammingImage shift_scale := by
  rintro x ⟨v, rfl⟩ y ⟨i, rfl⟩
  exact ⟨Function.update v i !(v i), (l.hammingProj_qi shift_scale h2 v i)⟩

omit [Fintype Fq] [DecidableEq Fq] in
theorem hammingImage_isAdjClosed (h2 : (2 : Fq) = (0 : Fq))
    (hnz : ∀ i, indicator i ∉ l.subspace) :
    (l.graph shift_scale h2 hnz).IsAdjClosed (l.hammingImage shift_scale) :=
  l.hammingImage_isAdjClosed_aux shift_scale h2

/-- The quotient chromotopology, restricted to the image of the Hamming cube: a genuine
`Chromotopology` on `l.hammingImage shift_scale`, exhibiting it as a component of
`l.quotientChromotopology`. -/
public noncomputable def hammingChromotopology (h2 : (2 : Fq) = (0 : Fq))
    (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq)) :
    Chromotopology (l.hammingImage shift_scale) (Fintype.ofFinite _) n Fq :=
  (l.quotientChromotopology shift_scale h2 hnz hNoDiff hZeroSum).restrict
    (l.hammingImage shift_scale) (l.hammingImage_isAdjClosed shift_scale h2 hnz)

/-! ### The image of the Hamming cube is, in fact, connected

This is a *separate* proposition from `hammingImage_isAdjClosed`: nothing about being an
`IsAdjClosed` component requires connectedness, and `Chromotopology.restrict` does not need it
either. Here it happens to be true, because the Hamming cube itself is connected (any two
`Fin n → Bool` differ in finitely many coordinates, and flipping them one at a time is a walk)
and `hammingProj` carries flips to `qi`-edges. -/

omit [Fintype Fq] [DecidableEq Fq] in
/-- Any two residues in the Hamming-cube image are joined by a walk in the quotient graph: flip
the coordinates where `v1` and `v2` differ, one at a time. -/
public theorem hammingProj_reachable (h2 : (2 : Fq) = (0 : Fq)) (hnz : ∀ i, indicator i ∉ l.subspace)
    (v1 v2 : Fin n → Bool) :
    (l.graph shift_scale h2 hnz).Reachable (l.hammingProj shift_scale v1)
      (l.hammingProj shift_scale v2) := by
  suffices h : ∀ T : Finset (Fin n),
      (l.graph shift_scale h2 hnz).Reachable (l.hammingProj shift_scale v1)
        (l.hammingProj shift_scale (T.piecewise v2 v1)) by
    simpa [Finset.piecewise_univ] using h Finset.univ
  intro T
  induction T using Finset.induction with
  | empty =>
    set_option linter.unnecessarySimpa false in
    simpa using SimpleGraph.Reachable.refl (l.hammingProj shift_scale v1)
  | @insert a T' ha ih =>
    rw [Finset.piecewise_insert]
    by_cases hv : v1 a = v2 a
    · have hval : (T'.piecewise v2 v1) a = v2 a := by
        rw [Finset.piecewise_eq_of_notMem _ _ _ ha, hv]
      rw [← hval, Function.update_eq_self]
      exact ih
    · have hflip : v2 a = !((T'.piecewise v2 v1) a) := by
        rw [Finset.piecewise_eq_of_notMem _ _ _ ha]
        exact Bool.eq_not_iff.mpr (Ne.symm hv)
      rw [hflip, l.hammingProj_qi shift_scale h2]
      exact ih.trans (SimpleGraph.Adj.reachable ⟨a, rfl⟩)

omit [Fintype Fq] [DecidableEq Fq] in
private theorem hammingImage_preconnected (h2 : (2 : Fq) = (0 : Fq)) (hnz : ∀ i, indicator i ∉ l.subspace) :
    ((l.graph shift_scale h2 hnz).induce (l.hammingImage shift_scale)).Preconnected := by
  rintro ⟨_, v1, rfl⟩ ⟨_, v2, rfl⟩
  obtain ⟨p⟩ := l.hammingProj_reachable shift_scale h2 hnz v1 v2
  exact ⟨Chromotopology.induceWalkOfClosed (l.hammingImage_isAdjClosed shift_scale h2 hnz)
    ⟨v1, rfl⟩ ⟨v2, rfl⟩ p⟩

omit [Fintype Fq] [DecidableEq Fq] in
private theorem hammingImage_connected (h2 : (2 : Fq) = (0 : Fq)) (hnz : ∀ i, indicator i ∉ l.subspace) :
    ((l.graph shift_scale h2 hnz).induce (l.hammingImage shift_scale)).Connected :=
  haveI : Nonempty ↑(l.hammingImage shift_scale) :=
    ⟨⟨l.hammingProj shift_scale (fun _ => false), fun _ => false, rfl⟩⟩
  ⟨l.hammingImage_preconnected shift_scale h2 hnz⟩

omit [DecidableEq Fq] in
/-- The `Chromotopology` on the Hamming-cube image is connected -- unlike a general
`Chromotopology.restrict`, which need not be. -/
public theorem hammingChromotopology_isConnected (h2 : (2 : Fq) = (0 : Fq))
    (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq)) :
    (l.hammingChromotopology shift_scale h2 hnz hNoDiff hZeroSum).IsConnected :=
  l.hammingImage_connected shift_scale h2 hnz

/-! ### The Hamming-cube image is itself a quotient over `F2`

Pulling the original code `C` back along the (additive, injective) embedding `hammingEmbedF2`
-- equivalently, intersecting `C` with the image of the embedding -- gives a genuine linear
code over `ZMod 2`, `l.hammingCode`, whose own quotient is in bijection with
`l.hammingImage shift_scale`: the Hamming restriction is directly a quotient chromotopology
with `Fq = F2`. -/

omit [Fintype Fq] [DecidableEq Fq] in
/-- The additive embedding of the abstract Hamming cube `Fin n → ZMod 2` into `Fqn`, sending
each coordinate `0 ↦ 0`, `1 ↦ shift_scale`. Agrees with `hammingEmbed` under the coordinatewise
identification of `Bool` with `ZMod 2` (`boolToZMod2`/`zmod2ToBool`). -/
def hammingEmbedF2 (v : Fin n → ZMod 2) : Fqn (n:=n) (Fq:=Fq) :=
  fun i => if v i = 1 then (shift_scale : Fq) else 0

omit [Fintype Fq] [DecidableEq Fq] in
private lemma hammingEmbedF2_add (h2 : (2 : Fq) = (0 : Fq)) (v w : Fin n → ZMod 2) :
    hammingEmbedF2 shift_scale (v + w)
      = hammingEmbedF2 shift_scale v + hammingEmbedF2 shift_scale w := by
  have hcancel : (shift_scale : Fq) + shift_scale = 0 := by rw [← two_mul, h2, zero_mul]
  funext i
  simp only [hammingEmbedF2, Pi.add_apply]
  rcases zmod2_eq_zero_or_one (v i) with hv | hv <;>
    rcases zmod2_eq_zero_or_one (w i) with hw | hw <;>
    simp [hv, hw, hcancel]

omit [Fintype Fq] [DecidableEq Fq] in
private lemma hammingEmbedF2_sub (h2 : (2 : Fq) = (0 : Fq)) (v w : Fin n → ZMod 2) :
    hammingEmbedF2 shift_scale v - hammingEmbedF2 shift_scale w
      = hammingEmbedF2 shift_scale (v - w) := by
  have hcancel : (shift_scale : Fq) + shift_scale = 0 := by rw [← two_mul, h2, zero_mul]
  have hneg : -(shift_scale : Fq) = shift_scale := (add_eq_zero_iff_eq_neg.mp hcancel).symm
  funext i
  simp only [hammingEmbedF2, Pi.sub_apply]
  rcases zmod2_eq_zero_or_one (v i) with hv | hv <;>
    rcases zmod2_eq_zero_or_one (w i) with hw | hw <;>
    simp [hv, hw, hneg]

/-- `l`'s original code `C`, pulled back along `hammingEmbedF2` -- equivalently, `C` intersected
with the image of the embedding, viewed inside the abstract `F2^n` cube. A genuine `F2`-linear
subspace: `hammingEmbedF2` is additive (`hammingEmbedF2_add`), and every `ZMod 2` scalar is `0`
or `1` (`zmod2_eq_zero_or_one`), so scalar closure needs nothing beyond `l.subspace` already
containing `0`. -/
def hammingCodeSubspace (h2 : (2 : Fq) = (0 : Fq)) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {v | hammingEmbedF2 shift_scale v ∈ l.subspace}
  zero_mem' := by
    show hammingEmbedF2 shift_scale 0 ∈ l.subspace
    have : hammingEmbedF2 shift_scale (0 : Fin n → ZMod 2) = 0 := by
      funext i; simp [hammingEmbedF2]
    rw [this]; exact Submodule.zero_mem _
  add_mem' := by
    intro v w hv hw
    show hammingEmbedF2 shift_scale (v + w) ∈ l.subspace
    rw [hammingEmbedF2_add shift_scale h2]
    exact Submodule.add_mem _ hv hw
  smul_mem' := by
    intro c v hv
    show hammingEmbedF2 shift_scale (c • v) ∈ l.subspace
    rcases zmod2_eq_zero_or_one c with hc | hc
    · subst hc
      have : hammingEmbedF2 shift_scale ((0 : ZMod 2) • v) = 0 := by
        rw [zero_smul]; funext i; simp [hammingEmbedF2]
      rw [this]; exact Submodule.zero_mem _
    · subst hc; rwa [one_smul]

/-- `l`'s original code `C`, restricted to the Hamming cube: a genuine linear code over `ZMod
2`, whose length is `n` (same as `l`) and whose own quotient is in bijection with
`l.hammingImage shift_scale` (`hammingCodeEquiv`). -/
public noncomputable def hammingCode (h2 : (2 : Fq) = (0 : Fq)) :
    LinearECC (n:=n) (k := Module.finrank (ZMod 2) (l.hammingCodeSubspace shift_scale h2))
      (Fq:=ZMod 2) where
  subspace := l.hammingCodeSubspace shift_scale h2
  rank_k := rfl

/-- `0 ↦ 0`, `1 ↦ 1`: the coordinatewise identification of the Hamming cube `Bool` with `ZMod
2`. -/
private def boolToZMod2 (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The inverse of `boolToZMod2`. -/
private def zmod2ToBool (x : ZMod 2) : Bool := x = 1

omit [Fintype Fq] [DecidableEq Fq] in
private lemma hammingEmbedF2_boolToZMod2 (v : Fin n → Bool) :
    hammingEmbedF2 shift_scale (fun i => boolToZMod2 (v i)) = hammingEmbed shift_scale v := by
  funext i
  simp only [hammingEmbedF2, hammingEmbed, boolToZMod2]
  by_cases hv : v i = true <;> simp [hv]

omit [Fintype Fq] [DecidableEq Fq] in
private lemma hammingEmbed_zmod2ToBool (v : Fin n → ZMod 2) :
    hammingEmbed shift_scale (fun i => zmod2ToBool (v i)) = hammingEmbedF2 shift_scale v := by
  funext i
  simp only [hammingEmbedF2, hammingEmbed, zmod2ToBool]
  rcases zmod2_eq_zero_or_one (v i) with h | h <;> simp [h]

omit [Fintype Fq] [DecidableEq Fq] in
lemma hammingImage_eq_range_hammingEmbedF2 :
    l.hammingImage shift_scale
      = Set.range (fun v : Fin n → ZMod 2 =>
          (Submodule.Quotient.mk (hammingEmbedF2 shift_scale v) : l.quotientByCode)) := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨fun i => boolToZMod2 (v i),
      congrArg Submodule.Quotient.mk (hammingEmbedF2_boolToZMod2 shift_scale v)⟩
  · rintro ⟨v, rfl⟩
    exact ⟨fun i => zmod2ToBool (v i),
      congrArg Submodule.Quotient.mk (hammingEmbed_zmod2ToBool shift_scale v)⟩

/-- `l.hammingCode`'s quotient is in bijection with the range of `hammingEmbedF2` inside
`l.quotientByCode`: `hammingEmbedF2` is additive and injective, and `l.hammingCode`'s code is
*exactly* its preimage of `l.subspace`, so this is the first isomorphism theorem in disguise. -/
noncomputable def hammingCodeRangeEquiv (h2 : (2 : Fq) = (0 : Fq)) :
    (l.hammingCode shift_scale h2).quotientByCode
      ≃ Set.range (fun v : Fin n → ZMod 2 =>
          (Submodule.Quotient.mk (hammingEmbedF2 shift_scale v) : l.quotientByCode)) :=
  Equiv.ofBijective
    (fun x => ⟨Quotient.liftOn' x (fun v => Submodule.Quotient.mk (hammingEmbedF2 shift_scale v))
      (fun v w hvw => by
        have hmem : v - w ∈ l.hammingCodeSubspace shift_scale h2 :=
          (Submodule.quotientRel_def _).mp hvw
        have hmem' : hammingEmbedF2 shift_scale v - hammingEmbedF2 shift_scale w ∈ l.subspace := by
          rw [hammingEmbedF2_sub shift_scale h2]; exact hmem
        exact (Submodule.Quotient.eq l.subspace).mpr hmem'),
      by
        induction x using Quotient.ind' with
        | _ v => exact ⟨v, rfl⟩⟩)
    ⟨by
      intro x y hxy
      induction x using Quotient.ind' with
      | _ v =>
      induction y using Quotient.ind' with
      | _ w =>
      have heq : Submodule.Quotient.mk (hammingEmbedF2 shift_scale v)
          = Submodule.Quotient.mk (hammingEmbedF2 shift_scale w) := congrArg Subtype.val hxy
      have hmem : hammingEmbedF2 shift_scale v - hammingEmbedF2 shift_scale w ∈ l.subspace :=
        (Submodule.Quotient.eq l.subspace).mp heq
      rw [hammingEmbedF2_sub shift_scale h2] at hmem
      exact Quotient.sound' ((Submodule.quotientRel_def _).mpr hmem),
     by rintro ⟨y, v, rfl⟩; exact ⟨Submodule.Quotient.mk v, rfl⟩⟩

/-- The Hamming restriction `l.hammingImage shift_scale` is directly the quotient of `l`'s code
`C`, restricted to the Hamming cube (`l.hammingCode`), over `F2`. -/
noncomputable def hammingCodeEquiv (h2 : (2 : Fq) = (0 : Fq)) :
    (l.hammingCode shift_scale h2).quotientByCode ≃ l.hammingImage shift_scale :=
  (l.hammingCodeRangeEquiv shift_scale h2).trans
    (Equiv.setCongr (l.hammingImage_eq_range_hammingEmbedF2 shift_scale).symm)

omit [Fintype Fq] [DecidableEq Fq] in
private lemma hammingCodeEquiv_mk (h2 : (2 : Fq) = (0 : Fq)) (v : Fin n → ZMod 2) :
    (l.hammingCodeEquiv shift_scale h2 (Submodule.Quotient.mk v) : l.quotientByCode)
      = Submodule.Quotient.mk (hammingEmbedF2 shift_scale v) := rfl

/-! ### An `IsoChromotopology` between the two Hamming restrictions

`l.hammingCode`'s own quotient chromotopology, over `F2`, is isomorphic to `l.hammingChromotopology`
-- the two constructions of "the Hamming restriction" agree, via `hammingCodeEquiv`. -/

omit [Fintype Fq] [DecidableEq Fq] in
/-- The map on vertex colors matching `hammingEmbedF2`: `0 ↦ 0`, `1 ↦ shift_scale`. -/
def hammingColorMap (x : ZMod 2) : Fq := if x = 1 then (shift_scale : Fq) else 0

omit [Fintype Fq] [DecidableEq Fq] in
/-- The coordinate-sum of `hammingEmbedF2 w` matches `hammingColorMap` applied to the
coordinate-sum of `w`: summing commutes with `hammingEmbedF2` up to `hammingColorMap`, since
(using `h2`) two `shift_scale`s cancel, matching the parity captured by summing in `ZMod 2`. -/
private lemma hammingEmbedF2_sum (h2 : (2 : Fq) = (0 : Fq)) (w : Fin n → ZMod 2) :
    (∑ i, hammingEmbedF2 shift_scale w i) = hammingColorMap shift_scale (∑ i, w i) := by
  have hcancel : (shift_scale : Fq) + shift_scale = 0 := by rw [← two_mul, h2, zero_mul]
  suffices h : ∀ S : Finset (Fin n),
      (∑ i ∈ S, hammingEmbedF2 shift_scale w i) = hammingColorMap shift_scale (∑ i ∈ S, w i) by
    simpa using h Finset.univ
  intro S
  induction S using Finset.induction with
  | empty => simp [hammingColorMap]
  | @insert a S' ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
    simp only [hammingEmbedF2]
    rcases zmod2_eq_zero_or_one (w a) with hw | hw <;>
      rcases zmod2_eq_zero_or_one (∑ i ∈ S', w i) with hs | hs <;>
      simp [hw, hs, hammingColorMap, hcancel]

omit [Fintype Fq] [DecidableEq Fq] in
private lemma hammingEmbedF2_indicator (i : Fin n) :
    hammingEmbedF2 shift_scale (indicator i : Fqn (n:=n) (Fq:=ZMod 2))
      = (shift_scale : Fq) • indicator i := by
  funext j
  simp only [hammingEmbedF2, indicator, Pi.smul_apply, smul_eq_mul]
  by_cases hij : i = j <;> simp [hij]

omit [Fintype Fq] [DecidableEq Fq] in
/-- No genuinely new side conditions are needed for `l.hammingCode` beyond `l`'s own: a unit
scalar (`shift_scale`) never moves a vector into or out of a submodule. -/
lemma hammingCode_hnz (h2 : (2 : Fq) = (0 : Fq)) (hnz : ∀ i, indicator i ∉ l.subspace) (i : Fin n) :
    indicator i ∉ l.hammingCodeSubspace shift_scale h2 := by
  show hammingEmbedF2 shift_scale (indicator i) ∉ l.subspace
  rw [hammingEmbedF2_indicator, l.subspace.smul_mem_iff (Units.ne_zero shift_scale)]
  exact hnz i

omit [Fintype Fq] [DecidableEq Fq] in
lemma hammingCode_hNoDiff (h2 : (2 : Fq) = (0 : Fq))
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    (i j : Fin n) (hij : i ≠ j) :
    indicator i - indicator j ∉ l.hammingCodeSubspace shift_scale h2 := by
  show hammingEmbedF2 shift_scale (indicator i - indicator j) ∉ l.subspace
  have heq : hammingEmbedF2 shift_scale ((indicator i : Fqn (n:=n) (Fq:=ZMod 2)) - indicator j)
      = (shift_scale : Fq) • ((indicator i : Fqn (n:=n) (Fq:=Fq)) - indicator j) := by
    rw [← hammingEmbedF2_sub shift_scale h2, hammingEmbedF2_indicator, hammingEmbedF2_indicator,
      smul_sub]
  rw [heq, l.subspace.smul_mem_iff (Units.ne_zero shift_scale)]
  exact hNoDiff i j hij

omit [Fintype Fq] [DecidableEq Fq] in
lemma hammingCode_hZeroSum (h2 : (2 : Fq) = (0 : Fq))
    (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq)) :
    ∀ w ∈ l.hammingCodeSubspace shift_scale h2, (∑ i, w i) = (0 : ZMod 2) := by
  intro w hw
  have h1 : (∑ i, hammingEmbedF2 shift_scale w i) = 0 := hZeroSum _ hw
  rw [hammingEmbedF2_sum shift_scale h2] at h1
  rcases zmod2_eq_zero_or_one (∑ i, w i) with h0 | h1'
  · exact h0
  · exfalso
    rw [h1', hammingColorMap] at h1
    simp only at h1
    exact Units.ne_zero shift_scale h1

/-- `l.hammingCode`'s own quotient chromotopology, over `F2`: no genuinely new side conditions
are needed beyond `l`'s own (`hammingCode_hnz`, `hammingCode_hNoDiff`, `hammingCode_hZeroSum`). -/
public noncomputable def hammingCodeChromotopology (h2 : (2 : Fq) = (0 : Fq))
    (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq)) :
    Chromotopology (l.hammingCode shift_scale h2).quotientByCode inferInstance n (ZMod 2) :=
  (l.hammingCode shift_scale h2).quotientChromotopology 1 zmod2_two_eq_zero
    (l.hammingCode_hnz shift_scale h2 hnz) (l.hammingCode_hNoDiff shift_scale h2 hNoDiff)
    (l.hammingCode_hZeroSum shift_scale h2 hZeroSum)

omit [Fintype Fq] [DecidableEq Fq] in
/-- `hammingCodeEquiv` intertwines the `qi`-translations on both sides: flipping coordinate `i`
before or after taking the equivalence gives the same result. -/
public lemma hammingCodeEquiv_qi (h2 : (2 : Fq) = (0 : Fq)) (i : Fin n)
    (x : (l.hammingCode shift_scale h2).quotientByCode) :
    (l.hammingCodeEquiv shift_scale h2 ((l.hammingCode shift_scale h2).qi 1 i x) : l.quotientByCode)
      = l.qi shift_scale i (l.hammingCodeEquiv shift_scale h2 x : l.quotientByCode) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hqi : (l.hammingCode shift_scale h2).qi 1 i (Submodule.Quotient.mk v)
      = Submodule.Quotient.mk (v + indicator i) := by
    show Submodule.Quotient.mk v + Submodule.Quotient.mk (((1 : Units (ZMod 2)) : ZMod 2) • indicator i)
        = Submodule.Quotient.mk (v + indicator i)
    rw [Units.val_one, one_smul, Submodule.Quotient.mk_add]
  rw [hqi]
  simp only [hammingCodeEquiv_mk]
  rw [hammingEmbedF2_add shift_scale h2, hammingEmbedF2_indicator]
  rfl

/-- The graph isomorphism underlying `hammingIso`: `hammingCodeEquiv`, shown to intertwine
adjacency via `hammingCodeEquiv_qi`. -/
noncomputable def hammingIsoGraph (h2 : (2 : Fq) = (0 : Fq)) (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq)) :
    (l.hammingCodeChromotopology shift_scale h2 hnz hNoDiff hZeroSum).graph
      ≃g (l.hammingChromotopology shift_scale h2 hnz hNoDiff hZeroSum).graph where
  toEquiv := l.hammingCodeEquiv shift_scale h2
  map_rel_iff' := by
    intro x y
    show l.Adj shift_scale (l.hammingCodeEquiv shift_scale h2 x : l.quotientByCode)
        (l.hammingCodeEquiv shift_scale h2 y : l.quotientByCode)
        ↔ (l.hammingCode shift_scale h2).Adj 1 x y
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, (l.hammingCodeEquiv shift_scale h2).injective (Subtype.ext ?_)⟩
      rw [l.hammingCodeEquiv_qi shift_scale h2 i x]
      exact hi
    · rintro ⟨i, rfl⟩
      exact ⟨i, l.hammingCodeEquiv_qi shift_scale h2 i x⟩

omit [DecidableEq Fq] in
@[simp] private lemma hammingIsoGraph_apply (h2 : (2 : Fq) = (0 : Fq)) (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq))
    (x : (l.hammingCode shift_scale h2).quotientByCode) :
    (l.hammingIsoGraph shift_scale h2 hnz hNoDiff hZeroSum) x
      = l.hammingCodeEquiv shift_scale h2 x := rfl

/-- `l.hammingCode`'s own quotient chromotopology (over `F2`) is isomorphic to
`l.hammingChromotopology` (the restriction of the `Fq`-quotient chromotopology): the two ways
of building "the Hamming restriction" agree. The vertex-color map `0, 1 ↦ 0, shift_scale`
(`hammingColorMap`) is generally neither injective nor surjective, since `Fq` may have many
more elements than just those two. -/
public noncomputable def hammingIso (h2 : (2 : Fq) = (0 : Fq)) (hnz : ∀ i, indicator i ∉ l.subspace)
    (hNoDiff : ∀ i j : Fin n, i ≠ j → indicator i - indicator j ∉ l.subspace)
    (hZeroSum : ∀ w ∈ l.subspace, (∑ i, w i) = (0 : Fq)) :
    IsoChromotopology (l.hammingCodeChromotopology shift_scale h2 hnz hNoDiff hZeroSum)
      (l.hammingChromotopology shift_scale h2 hnz hNoDiff hZeroSum) where
  toIso := l.hammingIsoGraph shift_scale h2 hnz hNoDiff hZeroSum
  colorMap := hammingColorMap shift_scale
  edge_colors_eq := by
    intro x y h
    set i0 := (l.hammingCode shift_scale h2).edgeColorOf 1
      (l.hammingCode_hNoDiff shift_scale h2 hNoDiff) h with hi0def
    have hspec := (l.hammingCode shift_scale h2).edgeColorOf_spec 1
      (l.hammingCode_hNoDiff shift_scale h2 hNoDiff) h
    have hkey : (l.hammingCodeEquiv shift_scale h2 y : l.quotientByCode)
        = l.qi shift_scale i0 (l.hammingCodeEquiv shift_scale h2 x : l.quotientByCode) := by
      rw [hspec, l.hammingCodeEquiv_qi shift_scale h2 i0 x]
    have hadj2 : l.Adj shift_scale
        (l.hammingCodeEquiv shift_scale h2 x : l.quotientByCode)
        (l.hammingCodeEquiv shift_scale h2 y : l.quotientByCode) := ⟨i0, hkey⟩
    show l.edgeColorOf shift_scale hNoDiff hadj2 = i0
    exact (l.edgeColorOf_unique shift_scale hNoDiff hadj2 hkey).symm
  vertex_color_comm := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [hammingIsoGraph_apply]
    exact hammingEmbedF2_sum shift_scale h2 v

end HammingComponent

end LinearECC

end QuotientByCode
