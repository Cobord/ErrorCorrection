import Mathlib.CategoryTheory.Whiskering
import Mathlib.RingTheory.Flat.Basic
import QuantumErrorCorrection.QuasiLocalAlgebra
import QuantumErrorCorrection.RegionNbhd

/-!
# Bounded-spread homomorphisms of quasi-local algebras

Let the site set `X` be a metric space whose closed balls are finite (`FiniteClosedBalls X`), so
that every finite region `S` has a finite `l`-neighborhood `metricNbhd l S` (see
`RegionNbhd.lean`). A *homomorphism of spread (at most) `l`* from a quasi-local algebra `𝒜` to
another one `𝒜'` on the same sites sends observables supported on `S` to observables supported
on the `l`-neighborhood of `S`:

  `α_S : 𝒜(S) ⟶ 𝒜'(metricNbhd l S)`,

compatibly with the inclusions of regions: for `S ⊆ T`, first including `𝒜(S) ↪ 𝒜(T)` and then
applying `α_T` agrees with first applying `α_S` and then including
`𝒜'(metricNbhd l S) ↪ 𝒜'(metricNbhd l T)`. That is, `α` is exactly a natural transformation
`𝒜.net ⟶ metricNbhdFunctor l ⋙ 𝒜'.net`. Examples include the automorphisms implemented by
finite-depth local circuits (quantum cellular automata), where `l` is the light-cone radius
given by the circuit depth times the gate range.

Since the target category `SuperStarAlgCat 𝕜` is used for the components, each `α_S` is a
grading-preserving `*`-algebra homomorphism.

The basic operations are:

* `BoundedSpreadHom.ofNetHom`: a morphism of nets `𝒜.net ⟶ 𝒜'.net` has spread `0`;
  in particular `BoundedSpreadHom.id 𝒜` has spread `0`.
* `BoundedSpreadHom.weaken`: a map of spread `l` also has spread `l'` for every `l' ≥ l`.
* `BoundedSpreadHom.comp`: spreads add under composition, by the triangle inequality.

Composition is unital and associative *up to weakening the spread*
(`BoundedSpreadHom.id_comp`, `BoundedSpreadHom.comp_id`, `BoundedSpreadHom.comp_assoc`), and
composition commutes with weakening (`BoundedSpreadHom.weaken_comp`,
`BoundedSpreadHom.comp_weaken`): the spread `0 + l` and `l` differ only in type, and the
identities hold after transporting along the evident inequality.

## The category

The spread is not part of a morphism's identity: `BoundedSpreadCat X 𝕜` has quasi-local algebras
as objects, and as morphisms `𝒜 ⟶ 𝒜'` the *germs* of bounded-spread homomorphisms of any spread,
i.e. the quotient of `Σ l, BoundedSpreadHom l 𝒜 𝒜'` identifying two homomorphisms that agree
after weakening both to a common spread (`BoundedSpreadHom.germSetoid`). This is the filtered
colimit over `l` of the spread-`l` hom-sets. The up-to-weakening laws above become strict
equalities of germs, so this is a genuine category. `BoundedSpreadCat.homMk` sends a
spread-`l` homomorphism to its morphism, and `BoundedSpreadCat.HasSpread f l` records that a
morphism is represented at spread `l`. This property is monotone in `l`, holds at `0` for the
identity, and is additive under composition. Its automorphisms are the quantum cellular automata
(`QCA.lean`).
-/

noncomputable section

open CategoryTheory NNReal RegionCat

universe u

variable {X : Type u} [DecidableEq X] [MetricSpace X] [FiniteClosedBalls X]
variable {𝕜 : Type u} [CommRing 𝕜] [StarRing 𝕜]

/-- A homomorphism of spread (at most) `l` from `𝒜` to `𝒜'`: for each region `S`, a
grading-preserving `*`-algebra map `𝒜(S) ⟶ 𝒜'(metricNbhd l S)`, natural in `S`. -/
structure BoundedSpreadHom (l : ℝ≥0) (𝒜 𝒜' : QuasiLocalAlgebra X 𝕜) where
  /-- The underlying natural transformation `𝒜.net ⟶ metricNbhdFunctor l ⋙ 𝒜'.net`. -/
  toNatTrans : 𝒜.net ⟶ metricNbhdFunctor l ⋙ 𝒜'.net

namespace BoundedSpreadHom

variable {l l' l'' : ℝ≥0} {𝒜 𝒜' 𝒜'' 𝒜''' : QuasiLocalAlgebra X 𝕜}

/-- The component at a region `S`: a map `𝒜(S) ⟶ 𝒜'(metricNbhd l S)`. -/
def app (α : BoundedSpreadHom l 𝒜 𝒜') (S : RegionCat X) :
    𝒜.net.obj S ⟶ 𝒜'.net.obj (metricNbhd l S) :=
  α.toNatTrans.app S

@[ext] theorem ext {α β : BoundedSpreadHom l 𝒜 𝒜'} (h : ∀ S, α.app S = β.app S) : α = β := by
  obtain ⟨α⟩ := α
  obtain ⟨β⟩ := β
  congr 1
  ext1
  funext S
  exact h S

/-- Naturality: including `S ↪ T` and then applying `α` is applying `α` and then including the
`l`-neighborhoods. -/
@[reassoc] theorem naturality (α : BoundedSpreadHom l 𝒜 𝒜') {S T : RegionCat X}
    (h : S.carrier ⊆ T.carrier) :
    𝒜.net.map (homOfSubset h) ≫ α.app T =
      α.app S ≫ 𝒜'.net.map (homOfSubset (metricNbhd_mono l h)) :=
  α.toNatTrans.naturality (homOfSubset h)

omit [MetricSpace X] [FiniteClosedBalls X] in
/-- In the thin category `RegionCat X`, a composite of structure maps is the structure map of
the composite inclusion. -/
@[reassoc] lemma net_map_comp_homOfSubset (𝒜 : QuasiLocalAlgebra X 𝕜)
    {S T U : RegionCat X} (h₁ : S.carrier ⊆ T.carrier) (h₂ : T.carrier ⊆ U.carrier) :
    𝒜.net.map (homOfSubset h₁) ≫ 𝒜.net.map (homOfSubset h₂) =
      𝒜.net.map (homOfSubset (h₁.trans h₂)) :=
  (𝒜.net.map_comp _ _).symm

omit [MetricSpace X] [FiniteClosedBalls X] in
lemma net_map_homOfSubset_self (𝒜 : QuasiLocalAlgebra X 𝕜) {S : RegionCat X}
    (h : S.carrier ⊆ S.carrier) : 𝒜.net.map (homOfSubset h) = 𝟙 _ :=
  𝒜.net.map_id S

/-- A morphism of nets `𝒜.net ⟶ 𝒜'.net`, which sends each `𝒜(S)` into `𝒜'(S)`, has spread
`0`. -/
def ofNetHom (η : 𝒜.net ⟶ 𝒜'.net) : BoundedSpreadHom 0 𝒜 𝒜' where
  toNatTrans := η ≫ (Functor.leftUnitor 𝒜'.net).inv ≫
    Functor.whiskerRight (metricNbhdUnit 0) 𝒜'.net

@[simp] theorem ofNetHom_app (η : 𝒜.net ⟶ 𝒜'.net) (S : RegionCat X) :
    (ofNetHom η).app S = η.app S ≫ 𝒜'.net.map (homOfSubset (subset_metricNbhd 0 S)) := by
  simp [ofNetHom, app, metricNbhdUnit]

/-- The identity, of spread `0`. -/
def id (𝒜 : QuasiLocalAlgebra X 𝕜) : BoundedSpreadHom 0 𝒜 𝒜 := ofNetHom (𝟙 _)

@[simp] theorem id_app (𝒜 : QuasiLocalAlgebra X 𝕜) (S : RegionCat X) :
    (id 𝒜).app S = 𝒜.net.map (homOfSubset (subset_metricNbhd 0 S)) := by
  simp [id]

/-- A map of spread `l` also has spread `l'` for any `l' ≥ l`: compose with the inclusion
`𝒜'(metricNbhd l S) ↪ 𝒜'(metricNbhd l' S)`. -/
def weaken (h : l ≤ l') (α : BoundedSpreadHom l 𝒜 𝒜') : BoundedSpreadHom l' 𝒜 𝒜' where
  toNatTrans := α.toNatTrans ≫ Functor.whiskerRight (metricNbhdWeaken h) 𝒜'.net

@[simp] theorem weaken_app (h : l ≤ l') (α : BoundedSpreadHom l 𝒜 𝒜') (S : RegionCat X) :
    (α.weaken h).app S = α.app S ≫ 𝒜'.net.map (homOfSubset (metricNbhd_mono_radius h S)) := by
  simp [weaken, app, metricNbhdWeaken]

@[simp] theorem weaken_refl (α : BoundedSpreadHom l 𝒜 𝒜') : α.weaken le_rfl = α := by
  ext1 S
  simp [net_map_homOfSubset_self]

@[simp] theorem weaken_weaken (h : l ≤ l') (h' : l' ≤ l'') (α : BoundedSpreadHom l 𝒜 𝒜') :
    (α.weaken h).weaken h' = α.weaken (h.trans h') := by
  ext1 S
  simp [net_map_comp_homOfSubset]

/-- Composition: if `α` has spread `l` and `β` has spread `l'`, then `α` followed by `β` has
spread `l + l'`, since `metricNbhd l' (metricNbhd l S) ⊆ metricNbhd (l + l') S`. -/
def comp (α : BoundedSpreadHom l 𝒜 𝒜') (β : BoundedSpreadHom l' 𝒜' 𝒜'') :
    BoundedSpreadHom (l + l') 𝒜 𝒜'' where
  toNatTrans := α.toNatTrans ≫ Functor.whiskerLeft (metricNbhdFunctor l) β.toNatTrans ≫
    Functor.whiskerRight (metricNbhdComp l l') 𝒜''.net

@[simp] theorem comp_app (α : BoundedSpreadHom l 𝒜 𝒜') (β : BoundedSpreadHom l' 𝒜' 𝒜'')
    (S : RegionCat X) :
    (α.comp β).app S = α.app S ≫ β.app (metricNbhd l S) ≫
      𝒜''.net.map (homOfSubset (metricNbhd_metricNbhd_subset l l' S)) := by
  simp [comp, app, metricNbhdComp]

theorem id_comp (α : BoundedSpreadHom l 𝒜 𝒜') :
    (id 𝒜).comp α = α.weaken (zero_add l).ge := by
  ext1 S
  simp [naturality_assoc, net_map_comp_homOfSubset]

theorem comp_id (α : BoundedSpreadHom l 𝒜 𝒜') :
    α.comp (id 𝒜') = α.weaken (add_zero l).ge := by
  ext1 S
  simp [net_map_comp_homOfSubset]

theorem comp_assoc (α : BoundedSpreadHom l 𝒜 𝒜') (β : BoundedSpreadHom l' 𝒜' 𝒜'')
    {l''' : ℝ≥0} (γ : BoundedSpreadHom l''' 𝒜'' 𝒜''') :
    (α.comp β).comp γ = (α.comp (β.comp γ)).weaken (add_assoc l l' l''').ge := by
  ext1 S
  simp [naturality_assoc, net_map_comp_homOfSubset]

theorem weaken_comp (h : l ≤ l'') (α : BoundedSpreadHom l 𝒜 𝒜')
    (β : BoundedSpreadHom l' 𝒜' 𝒜'') :
    (α.weaken h).comp β = (α.comp β).weaken (add_le_add h le_rfl) := by
  ext1 S
  simp [naturality_assoc, net_map_comp_homOfSubset]

theorem comp_weaken (h : l' ≤ l'') (α : BoundedSpreadHom l 𝒜 𝒜')
    (β : BoundedSpreadHom l' 𝒜' 𝒜'') :
    α.comp (β.weaken h) = (α.comp β).weaken (add_le_add le_rfl h) := by
  ext1 S
  simp [net_map_comp_homOfSubset]

private lemma weaken_comp_weaken {m m' : ℝ≥0} (h : l ≤ m) (h' : l' ≤ m')
    (α : BoundedSpreadHom l 𝒜 𝒜') (β : BoundedSpreadHom l' 𝒜' 𝒜'') :
    (α.weaken h).comp (β.weaken h') = (α.comp β).weaken (add_le_add h h') := by
  rw [weaken_comp, comp_weaken, weaken_weaken]

/-! ### Germs: forgetting the spread -/

/-- Homomorphisms of *some* bounded spread, identified when they agree after weakening both to a
common spread. The quotient is the filtered colimit over `l` of the spread-`l` homomorphisms,
and it is the hom-set of `BoundedSpreadCat`. -/
def germSetoid (𝒜 𝒜' : QuasiLocalAlgebra X 𝕜) : Setoid (Σ l : ℝ≥0, BoundedSpreadHom l 𝒜 𝒜') where
  r a b := ∃ (m : ℝ≥0) (ha : a.1 ≤ m) (hb : b.1 ≤ m), a.2.weaken ha = b.2.weaken hb
  iseqv :=
    { refl := fun a => ⟨a.1, le_rfl, le_rfl, rfl⟩
      symm := fun ⟨m, ha, hb, h⟩ => ⟨m, hb, ha, h.symm⟩
      trans := fun ⟨m, ha, _, h⟩ ⟨n, _, hc, h'⟩ =>
        ⟨max m n, ha.trans (le_max_left m n), hc.trans (le_max_right m n), by
          have h₁ := congrArg (weaken (le_max_left m n)) h
          have h₂ := congrArg (weaken (le_max_right m n)) h'
          rw [weaken_weaken, weaken_weaken] at h₁ h₂
          exact h₁.trans h₂⟩ }

/-- The germ of a bounded-spread homomorphism, forgetting its spread. -/
def germ (α : BoundedSpreadHom l 𝒜 𝒜') : Quotient (germSetoid 𝒜 𝒜') := ⟦⟨l, α⟩⟧

theorem germ_eq_germ_iff {α : BoundedSpreadHom l 𝒜 𝒜'} {β : BoundedSpreadHom l' 𝒜 𝒜'} :
    α.germ = β.germ ↔ ∃ (m : ℝ≥0) (h : l ≤ m) (h' : l' ≤ m), α.weaken h = β.weaken h' :=
  Quotient.eq

/-- Weakening the spread does not change the germ. -/
@[simp] theorem germ_weaken (h : l ≤ l') (α : BoundedSpreadHom l 𝒜 𝒜') :
    (α.weaken h).germ = α.germ :=
  germ_eq_germ_iff.2 ⟨l', le_rfl, h, weaken_refl _⟩

theorem germ_surjective (f : Quotient (germSetoid 𝒜 𝒜')) :
    ∃ (l : ℝ≥0) (α : BoundedSpreadHom l 𝒜 𝒜'), α.germ = f :=
  Quotient.inductionOn f fun ⟨l, α⟩ => ⟨l, α, rfl⟩

/-- Composition of germs, well defined because composition commutes with weakening. -/
private def germComp :
    Quotient (germSetoid 𝒜 𝒜') → Quotient (germSetoid 𝒜' 𝒜'') → Quotient (germSetoid 𝒜 𝒜'') :=
  Quotient.map₂ (fun a b => ⟨a.1 + b.1, a.2.comp b.2⟩)
    fun _ _ ⟨m, ha, ha', h⟩ _ _ ⟨n, hb, hb', h'⟩ =>
      ⟨m + n, add_le_add ha hb, add_le_add ha' hb', by
        rw [← weaken_comp_weaken ha hb, ← weaken_comp_weaken ha' hb', h, h']⟩

private lemma germComp_germ (α : BoundedSpreadHom l 𝒜 𝒜') (β : BoundedSpreadHom l' 𝒜' 𝒜'') :
    germComp α.germ β.germ = (α.comp β).germ :=
  rfl

end BoundedSpreadHom

/-! ### The category -/

/-- The category of quasi-local superalgebras on the metric site set `X`, with bounded-spread
homomorphisms of arbitrary (finite) spread as morphisms. An object is a `QuasiLocalAlgebra X 𝕜`
whose local algebras are flat `𝕜`-modules.
* Flatness is automatic over a field. It is what makes stacking (`Stacking.lean`) preserve
  isotony, so that stacking is defined on every object.
* The quasi-local algebra is wrapped so that the category structure, which depends on the chosen
  metric on `X`, is owned by this type rather than put on `QuasiLocalAlgebra X 𝕜` itself. -/
structure BoundedSpreadCat (X : Type u) [DecidableEq X] [MetricSpace X] [FiniteClosedBalls X]
    (𝕜 : Type u) [CommRing 𝕜] [StarRing 𝕜] where
  /-- The underlying quasi-local algebra. -/
  toQuasiLocalAlgebra : QuasiLocalAlgebra X 𝕜
  /-- Every local algebra is a flat `𝕜`-module. -/
  flat : ∀ S, Module.Flat 𝕜 (toQuasiLocalAlgebra.net.obj S)

namespace BoundedSpreadCat

open BoundedSpreadHom

/-- Regard a quasi-local algebra with flat local algebras as an object of `BoundedSpreadCat`. -/
abbrev of (𝒜 : QuasiLocalAlgebra X 𝕜) (h𝒜 : ∀ S, Module.Flat 𝕜 (𝒜.net.obj S)) :
    BoundedSpreadCat X 𝕜 :=
  ⟨𝒜, h𝒜⟩

/-- A morphism `A ⟶ B` is the germ of a bounded-spread homomorphism of some spread `l`, with
two such identified when they agree after weakening to a common spread. Composition adds
spreads; the identity has spread `0`. -/
instance : Category (BoundedSpreadCat X 𝕜) where
  Hom A B := Quotient (germSetoid A.toQuasiLocalAlgebra B.toQuasiLocalAlgebra)
  id A := (BoundedSpreadHom.id A.toQuasiLocalAlgebra).germ
  comp f g := germComp f g
  id_comp f := Quotient.inductionOn f fun ⟨_, α⟩ => by
    change germComp (BoundedSpreadHom.id _).germ α.germ = α.germ
    rw [germComp_germ, BoundedSpreadHom.id_comp, germ_weaken]
  comp_id f := Quotient.inductionOn f fun ⟨_, α⟩ => by
    change germComp α.germ (BoundedSpreadHom.id _).germ = α.germ
    rw [germComp_germ, BoundedSpreadHom.comp_id, germ_weaken]
  assoc f g h := Quotient.inductionOn₃ f g h fun ⟨_, α⟩ ⟨_, β⟩ ⟨_, γ⟩ => by
    change germComp (germComp α.germ β.germ) γ.germ = germComp α.germ (germComp β.germ γ.germ)
    rw [germComp_germ, germComp_germ, germComp_germ, germComp_germ,
      BoundedSpreadHom.comp_assoc, germ_weaken]

variable {A B C : BoundedSpreadCat X 𝕜} {l l' : ℝ≥0}

/-- The morphism represented by a homomorphism of spread `l`. -/
def homMk (α : BoundedSpreadHom l A.toQuasiLocalAlgebra B.toQuasiLocalAlgebra) : A ⟶ B :=
  α.germ

@[simp] theorem homMk_id : homMk (BoundedSpreadHom.id A.toQuasiLocalAlgebra) = 𝟙 A := rfl

@[simp] theorem homMk_comp (α : BoundedSpreadHom l A.toQuasiLocalAlgebra B.toQuasiLocalAlgebra)
    (β : BoundedSpreadHom l' B.toQuasiLocalAlgebra C.toQuasiLocalAlgebra) :
    homMk (α.comp β) = homMk α ≫ homMk β := rfl

@[simp] theorem homMk_weaken (h : l ≤ l')
    (α : BoundedSpreadHom l A.toQuasiLocalAlgebra B.toQuasiLocalAlgebra) :
    homMk (α.weaken h) = homMk α :=
  germ_weaken h α

theorem homMk_eq_homMk_iff {α : BoundedSpreadHom l A.toQuasiLocalAlgebra B.toQuasiLocalAlgebra}
    {β : BoundedSpreadHom l' A.toQuasiLocalAlgebra B.toQuasiLocalAlgebra} :
    homMk α = homMk β ↔ ∃ (m : ℝ≥0) (h : l ≤ m) (h' : l' ≤ m), α.weaken h = β.weaken h' :=
  germ_eq_germ_iff

/-- Every morphism is represented by a homomorphism of some bounded spread. -/
theorem homMk_surjective (f : A ⟶ B) :
    ∃ (l : ℝ≥0) (α : BoundedSpreadHom l A.toQuasiLocalAlgebra B.toQuasiLocalAlgebra),
      homMk α = f :=
  germ_surjective f

/-- A morphism *has spread at most `l`* when it is represented by a homomorphism of spread
`l`. -/
def HasSpread (f : A ⟶ B) (l : ℝ≥0) : Prop :=
  ∃ α : BoundedSpreadHom l A.toQuasiLocalAlgebra B.toQuasiLocalAlgebra, homMk α = f

theorem hasSpread_homMk (α : BoundedSpreadHom l A.toQuasiLocalAlgebra B.toQuasiLocalAlgebra) :
    HasSpread (homMk α) l :=
  ⟨α, rfl⟩

theorem HasSpread.mono {f : A ⟶ B} (hf : HasSpread f l) (h : l ≤ l') : HasSpread f l' :=
  let ⟨α, hα⟩ := hf
  ⟨α.weaken h, by rw [homMk_weaken, hα]⟩

theorem hasSpread_id (A : BoundedSpreadCat X 𝕜) : HasSpread (𝟙 A) 0 :=
  ⟨BoundedSpreadHom.id _, homMk_id⟩

theorem HasSpread.comp {f : A ⟶ B} {g : B ⟶ C} (hf : HasSpread f l) (hg : HasSpread g l') :
    HasSpread (f ≫ g) (l + l') :=
  let ⟨α, hα⟩ := hf
  let ⟨β, hβ⟩ := hg
  ⟨α.comp β, by rw [homMk_comp, hα, hβ]⟩

end BoundedSpreadCat

end
