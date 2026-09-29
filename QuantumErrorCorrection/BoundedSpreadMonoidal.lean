import QuantumErrorCorrection.BoundedSpreadHom
import QuantumErrorCorrection.Stacking

/-!
# Stacking makes `BoundedSpreadCat X 𝕜` monoidal

The tensor product of two objects of `BoundedSpreadCat X 𝕜` is their stack
(`QuasiLocalAlgebra.stack`), whose net is the pointwise super tensor product of nets. The unit is
the trivial system (`QuasiLocalAlgebra.stackUnit`).

* **Morphisms.** Two bounded-spread homomorphisms of a common spread `l` tensor to one of spread
  `l` (`BoundedSpreadHom.tensorBSH`), componentwise in `SuperStarAlgCat 𝕜`. On germs of
  possibly different spreads (`BoundedSpreadCat.stackHom`), both are first weakened to the
  larger spread; tensoring commutes with weakening, so this is well defined.
* **Structure isomorphisms.** The associator, unitors and braiding are those of the functor
  category of nets, included as spread-`0` morphisms by `BoundedSpreadCat.homOfNet`.
  `homOfNet` is compatible with composition and tensor, so pentagon and triangle reduce to their
  functor-category versions. The naturality laws reduce to componentwise naturality in
  `SuperStarAlgCat 𝕜`.
-/

noncomputable section

open CategoryTheory MonoidalCategory NNReal RegionCat

universe u

variable {X : Type u} [DecidableEq X] [MetricSpace X] [FiniteClosedBalls X]
variable {𝕜 : Type u} [CommRing 𝕜] [StarRing 𝕜]

/-! ### Composing bounded-spread homomorphisms with net morphisms -/

namespace BoundedSpreadHom

variable {l : ℝ≥0} {A A' A'' : QuasiLocalAlgebra X 𝕜}

/-- A bounded-spread homomorphism followed by a morphism of nets, keeping the spread. -/
def postNet (α : BoundedSpreadHom l A A') (θ : A'.net ⟶ A''.net) : BoundedSpreadHom l A A'' where
  toNatTrans := α.toNatTrans ≫ Functor.whiskerLeft (metricNbhdFunctor l) θ

theorem postNet_app (α : BoundedSpreadHom l A A') (θ : A'.net ⟶ A''.net) (S : RegionCat X) :
    (α.postNet θ).app S = α.app S ≫ θ.app (metricNbhd l S) :=
  rfl

/-- A morphism of nets followed by a bounded-spread homomorphism, keeping the spread. -/
def preNet (η : A.net ⟶ A'.net) (α : BoundedSpreadHom l A' A'') : BoundedSpreadHom l A A'' where
  toNatTrans := η ≫ α.toNatTrans

theorem preNet_app (η : A.net ⟶ A'.net) (α : BoundedSpreadHom l A' A'') (S : RegionCat X) :
    (α.preNet η).app S = η.app S ≫ α.app S :=
  rfl

theorem comp_ofNetHom (α : BoundedSpreadHom l A A') (θ : A'.net ⟶ A''.net) :
    α.comp (ofNetHom θ) = (α.postNet θ).weaken (add_zero l).ge := by
  ext1 S
  simp [postNet_app, net_map_comp_homOfSubset]

theorem ofNetHom_comp (η : A.net ⟶ A'.net) (α : BoundedSpreadHom l A' A'') :
    (ofNetHom η).comp α = (α.preNet η).weaken (zero_add l).ge := by
  ext1 S
  simp [preNet_app, naturality_assoc, net_map_comp_homOfSubset]

theorem ofNetHom_comp_ofNetHom (η : A.net ⟶ A'.net) (θ : A'.net ⟶ A''.net) :
    (ofNetHom η).comp (ofNetHom θ) = (ofNetHom (η ≫ θ)).weaken (zero_add 0).ge := by
  ext1 S
  simp [net_map_comp_homOfSubset]

end BoundedSpreadHom

namespace BoundedSpreadCat

open BoundedSpreadHom

/-! ### Stacking objects -/

/-- The stack of two objects: the local algebra on `S` is `A(S) ⊗ˢ B(S)`. -/
def stackObj (A B : BoundedSpreadCat X 𝕜) : BoundedSpreadCat X 𝕜 :=
  ⟨A.1.stack B.1 A.flat B.flat, QuasiLocalAlgebra.stack_flat _ _ A.flat B.flat⟩

variable (X 𝕜) in
/-- The unit for stacking: the trivial system. -/
def stackUnitObj : BoundedSpreadCat X 𝕜 :=
  ⟨QuasiLocalAlgebra.stackUnit X 𝕜, QuasiLocalAlgebra.stackUnit_flat⟩

theorem stackObj_net (A B : BoundedSpreadCat X 𝕜) :
    (stackObj A B).1.net = A.1.net ⊗ B.1.net :=
  rfl

theorem stackObj_map (A B : BoundedSpreadCat X 𝕜) {S T : RegionCat X} (f : S ⟶ T) :
    (stackObj A B).1.net.map f = A.1.net.map f ⊗ₘ B.1.net.map f :=
  rfl

variable {A A' A'' B B' B'' : BoundedSpreadCat X 𝕜} {l l' : ℝ≥0}

/-! ### Tensoring bounded-spread homomorphisms of a common spread -/

/-- The stack of two bounded-spread homomorphisms of a common spread `l`, componentwise the
super tensor product of the components. -/
def tensorBSH (α : BoundedSpreadHom l A.1 A'.1) (β : BoundedSpreadHom l B.1 B'.1) :
    BoundedSpreadHom l (stackObj A B).1 (stackObj A' B').1 where
  toNatTrans :=
    { app S := α.app S ⊗ₘ β.app S
      naturality S T f := by
        change (A.1.net.map f ⊗ₘ B.1.net.map f) ≫ (α.app T ⊗ₘ β.app T) =
          (α.app S ⊗ₘ β.app S) ≫ ((metricNbhdFunctor l ⋙ A'.1.net).map f ⊗ₘ
            (metricNbhdFunctor l ⋙ B'.1.net).map f)
        exact (tensorHom_comp_tensorHom _ _ _ _).trans ((congrArg₂ (· ⊗ₘ ·)
          (α.toNatTrans.naturality f) (β.toNatTrans.naturality f)).trans
          (tensorHom_comp_tensorHom _ _ _ _).symm) }

theorem tensorBSH_app (α : BoundedSpreadHom l A.1 A'.1) (β : BoundedSpreadHom l B.1 B'.1)
    (S : RegionCat X) : (tensorBSH α β).app S = α.app S ⊗ₘ β.app S :=
  rfl

theorem tensorBSH_weaken (h : l ≤ l') (α : BoundedSpreadHom l A.1 A'.1)
    (β : BoundedSpreadHom l B.1 B'.1) :
    tensorBSH (α.weaken h) (β.weaken h) = (tensorBSH α β).weaken h := by
  ext1 S
  rw [tensorBSH_app, weaken_app, weaken_app, weaken_app, tensorBSH_app, stackObj_map]
  exact (tensorHom_comp_tensorHom _ _ _ _).symm

theorem tensorBSH_comp (α : BoundedSpreadHom l A.1 A'.1) (β : BoundedSpreadHom l B.1 B'.1)
    (α' : BoundedSpreadHom l' A'.1 A''.1) (β' : BoundedSpreadHom l' B'.1 B''.1) :
    (tensorBSH α β).comp (tensorBSH α' β') = tensorBSH (α.comp α') (β.comp β') := by
  ext1 S
  rw [comp_app, tensorBSH_app, tensorBSH_app, tensorBSH_app, comp_app, comp_app, stackObj_map]
  exact (congrArg ((α.app S ⊗ₘ β.app S) ≫ ·) (tensorHom_comp_tensorHom _ _ _ _)).trans
    (tensorHom_comp_tensorHom _ _ _ _)

theorem tensorBSH_id (A B : BoundedSpreadCat X 𝕜) :
    tensorBSH (BoundedSpreadHom.id A.1) (BoundedSpreadHom.id B.1) =
      BoundedSpreadHom.id (stackObj A B).1 := by
  ext1 S
  rw [tensorBSH_app, id_app, id_app, id_app, stackObj_map]

theorem tensorBSH_ofNetHom (η : A.1.net ⟶ A'.1.net) (θ : B.1.net ⟶ B'.1.net) :
    tensorBSH (ofNetHom η) (ofNetHom θ) =
      ofNetHom (𝒜 := (stackObj A B).1) (𝒜' := (stackObj A' B').1) (η ⊗ₘ θ) := by
  ext1 S
  rw [tensorBSH_app, ofNetHom_app, ofNetHom_app]
  exact (tensorHom_comp_tensorHom _ _ _ _).symm

/-! ### Tensoring morphisms (germs) -/

/-- The stack of two morphisms: represent both at a common spread and tensor. -/
def stackHom (f : A ⟶ A') (g : B ⟶ B') : stackObj A B ⟶ stackObj A' B' :=
  Quotient.map₂ (sa := germSetoid A.1 A'.1) (sb := germSetoid B.1 B'.1)
    (sc := germSetoid (stackObj A B).1 (stackObj A' B').1) (fun a b => ⟨max a.1 b.1,
      tensorBSH (a.2.weaken (le_max_left a.1 b.1)) (b.2.weaken (le_max_right a.1 b.1))⟩)
    (fun _ _ ⟨m, ha, ha', h⟩ _ _ ⟨n, hb, hb', h'⟩ =>
      ⟨max m n, max_le_max ha hb, max_le_max ha' hb', by
        have e₁ := congrArg (weaken (le_max_left m n)) h
        have e₂ := congrArg (weaken (le_max_right m n)) h'
        rw [weaken_weaken, weaken_weaken] at e₁ e₂
        rw [← tensorBSH_weaken, ← tensorBSH_weaken, weaken_weaken, weaken_weaken, weaken_weaken,
          weaken_weaken, e₁, e₂]⟩)
    f g

theorem homMk_stackHom (α : BoundedSpreadHom l A.1 A'.1) (β : BoundedSpreadHom l B.1 B'.1) :
    stackHom (homMk α) (homMk β) = homMk (tensorBSH α β) := by
  change homMk (tensorBSH (α.weaken (le_max_left l l)) (β.weaken (le_max_right l l))) = _
  rw [tensorBSH_weaken, homMk_weaken]

/-- Any two morphisms are represented at a common spread. -/
theorem exists_common_spread {C C' D D' : BoundedSpreadCat X 𝕜} (f : C ⟶ C') (g : D ⟶ D') :
    ∃ (l : ℝ≥0) (α : BoundedSpreadHom l C.1 C'.1) (β : BoundedSpreadHom l D.1 D'.1),
      homMk α = f ∧ homMk β = g := by
  obtain ⟨l₁, α, rfl⟩ := homMk_surjective f
  obtain ⟨l₂, β, rfl⟩ := homMk_surjective g
  exact ⟨max l₁ l₂, α.weaken (le_max_left l₁ l₂), β.weaken (le_max_right l₁ l₂),
    homMk_weaken _ _, homMk_weaken _ _⟩

/-- Any three morphisms are represented at a common spread. -/
theorem exists_common_spread₃ {C C' D D' E E' : BoundedSpreadCat X 𝕜} (f : C ⟶ C')
    (g : D ⟶ D') (k : E ⟶ E') :
    ∃ (l : ℝ≥0) (α : BoundedSpreadHom l C.1 C'.1) (β : BoundedSpreadHom l D.1 D'.1)
      (γ : BoundedSpreadHom l E.1 E'.1), homMk α = f ∧ homMk β = g ∧ homMk γ = k := by
  obtain ⟨l₁, α, β, rfl, rfl⟩ := exists_common_spread f g
  obtain ⟨l₂, γ, rfl⟩ := homMk_surjective k
  exact ⟨max l₁ l₂, α.weaken (le_max_left l₁ l₂), β.weaken (le_max_left l₁ l₂),
    γ.weaken (le_max_right l₁ l₂), homMk_weaken _ _, homMk_weaken _ _, homMk_weaken _ _⟩

/-! ### Net morphisms as spread-`0` morphisms -/

/-- A morphism of nets, as a spread-`0` morphism of `BoundedSpreadCat`. -/
def homOfNet (η : A.1.net ⟶ A'.1.net) : A ⟶ A' := homMk (ofNetHom η)

theorem homOfNet_id (A : BoundedSpreadCat X 𝕜) : homOfNet (𝟙 A.1.net) = 𝟙 A := rfl

theorem homOfNet_comp (η : A.1.net ⟶ A'.1.net) (θ : A'.1.net ⟶ A''.1.net) :
    homOfNet η ≫ homOfNet θ = homOfNet (η ≫ θ) := by
  rw [homOfNet, homOfNet, ← homMk_comp, ofNetHom_comp_ofNetHom, homMk_weaken]
  rfl

theorem homMk_comp_homOfNet (α : BoundedSpreadHom l A.1 A'.1) (θ : A'.1.net ⟶ A''.1.net) :
    homMk α ≫ homOfNet θ = homMk (α.postNet θ) := by
  rw [homOfNet, ← homMk_comp, comp_ofNetHom, homMk_weaken]

theorem homOfNet_comp_homMk (η : A.1.net ⟶ A'.1.net) (α : BoundedSpreadHom l A'.1 A''.1) :
    homOfNet η ≫ homMk α = homMk (α.preNet η) := by
  rw [homOfNet, ← homMk_comp, ofNetHom_comp, homMk_weaken]

theorem stackHom_homOfNet (η : A.1.net ⟶ A'.1.net) (θ : B.1.net ⟶ B'.1.net) :
    stackHom (homOfNet η) (homOfNet θ) =
      homOfNet (A := stackObj A B) (A' := stackObj A' B') (η ⊗ₘ θ) := by
  rw [homOfNet, homOfNet, homMk_stackHom, tensorBSH_ofNetHom]
  rfl

/-- An isomorphism of nets, as a spread-`0` isomorphism of `BoundedSpreadCat`. -/
def isoOfNet (e : A.1.net ≅ A'.1.net) : A ≅ A' where
  hom := homOfNet e.hom
  inv := homOfNet e.inv
  hom_inv_id := by rw [homOfNet_comp, e.hom_inv_id, homOfNet_id]
  inv_hom_id := by rw [homOfNet_comp, e.inv_hom_id, homOfNet_id]

/-! ### The monoidal structure -/

instance monoidalCategoryStruct : MonoidalCategoryStruct (BoundedSpreadCat X 𝕜) where
  tensorObj := stackObj
  whiskerLeft A _ _ g := stackHom (𝟙 A) g
  whiskerRight f B := stackHom f (𝟙 B)
  tensorHom := stackHom
  tensorUnit := stackUnitObj X 𝕜
  associator A B C := isoOfNet (α_ A.1.net B.1.net C.1.net)
  leftUnitor A := isoOfNet (λ_ A.1.net)
  rightUnitor A := isoOfNet (ρ_ A.1.net)

theorem tensorHom_def' (f : A ⟶ A') (g : B ⟶ B') : f ⊗ₘ g = stackHom f g := rfl

theorem associator_hom_def (A B C : BoundedSpreadCat X 𝕜) :
    (α_ A B C).hom = homOfNet (A := (A ⊗ B) ⊗ C) (A' := A ⊗ (B ⊗ C))
      (α_ A.1.net B.1.net C.1.net).hom := rfl

theorem leftUnitor_hom_def (A : BoundedSpreadCat X 𝕜) :
    (λ_ A).hom = homOfNet (A := 𝟙_ _ ⊗ A) (λ_ A.1.net).hom := rfl

theorem rightUnitor_hom_def (A : BoundedSpreadCat X 𝕜) :
    (ρ_ A).hom = homOfNet (A := A ⊗ 𝟙_ _) (ρ_ A.1.net).hom := rfl

/-- Stacking makes `BoundedSpreadCat X 𝕜` a monoidal category. -/
instance monoidalCategory : MonoidalCategory (BoundedSpreadCat X 𝕜) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun A B => by
      rw [tensorHom_def', ← homMk_id, ← homMk_id, homMk_stackHom, tensorBSH_id, homMk_id]
      rfl)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => by
      obtain ⟨l, α₁, α₂, rfl, rfl⟩ := exists_common_spread f₁ f₂
      obtain ⟨l', β₁, β₂, rfl, rfl⟩ := exists_common_spread g₁ g₂
      rw [tensorHom_def', tensorHom_def', tensorHom_def', homMk_stackHom, homMk_stackHom]
      erw [← homMk_comp, ← homMk_comp, ← homMk_comp, homMk_stackHom, tensorBSH_comp])
    (associator_naturality := fun f₁ f₂ f₃ => by
      obtain ⟨l, α₁, α₂, α₃, rfl, rfl, rfl⟩ := exists_common_spread₃ f₁ f₂ f₃
      rw [tensorHom_def', tensorHom_def', tensorHom_def', tensorHom_def', homMk_stackHom,
        homMk_stackHom, homMk_stackHom, homMk_stackHom, associator_hom_def, associator_hom_def]
      refine (homMk_comp_homOfNet _ _).trans ((congrArg homMk (BoundedSpreadHom.ext fun S => ?_)).trans
        (homOfNet_comp_homMk _ _).symm)
      exact associator_naturality (α₁.app S) (α₂.app S) (α₃.app S))
    (leftUnitor_naturality := fun f => by
      obtain ⟨l, α, rfl⟩ := homMk_surjective f
      rw [tensorHom_def', ← homMk_id, ← homMk_weaken (zero_le : (0 : ℝ≥0) ≤ l), homMk_stackHom,
        leftUnitor_hom_def, leftUnitor_hom_def]
      refine (homMk_comp_homOfNet _ _).trans ((congrArg homMk (BoundedSpreadHom.ext fun S => ?_)).trans
        (homOfNet_comp_homMk _ _).symm)
      change ((𝟙 _ ≫ 𝟙 _) ⊗ₘ α.app S) ≫ (λ_ _).hom = (λ_ _).hom ≫ α.app S
      rw [Category.comp_id, id_tensorHom, leftUnitor_naturality])
    (rightUnitor_naturality := fun f => by
      obtain ⟨l, α, rfl⟩ := homMk_surjective f
      rw [tensorHom_def', ← homMk_id, ← homMk_weaken (zero_le : (0 : ℝ≥0) ≤ l), homMk_stackHom,
        rightUnitor_hom_def, rightUnitor_hom_def]
      refine (homMk_comp_homOfNet _ _).trans ((congrArg homMk (BoundedSpreadHom.ext fun S => ?_)).trans
        (homOfNet_comp_homMk _ _).symm)
      change (α.app S ⊗ₘ (𝟙 _ ≫ 𝟙 _)) ≫ (ρ_ _).hom = (ρ_ _).hom ≫ α.app S
      rw [Category.comp_id, tensorHom_id, rightUnitor_naturality])
    (pentagon := fun W A B C => by
      rw [associator_hom_def, associator_hom_def, associator_hom_def, associator_hom_def,
        associator_hom_def, ← homOfNet_id, ← homOfNet_id, tensorHom_def', tensorHom_def']
      erw [stackHom_homOfNet, stackHom_homOfNet, homOfNet_comp, homOfNet_comp, homOfNet_comp]
      congr 1
      exact pentagon W.1.net A.1.net B.1.net C.1.net)
    (triangle := fun A B => by
      rw [associator_hom_def, leftUnitor_hom_def, rightUnitor_hom_def, ← homOfNet_id,
        ← homOfNet_id, tensorHom_def', tensorHom_def']
      erw [stackHom_homOfNet, stackHom_homOfNet, homOfNet_comp]
      congr 1
      exact triangle A.1.net B.1.net)

theorem whiskerLeft_def' (A : BoundedSpreadCat X 𝕜) (g : B ⟶ B') : A ◁ g = stackHom (𝟙 A) g :=
  rfl

theorem whiskerRight_def' (f : A ⟶ A') (B : BoundedSpreadCat X 𝕜) : f ▷ B = stackHom f (𝟙 B) :=
  rfl

theorem associator_inv_def (A B C : BoundedSpreadCat X 𝕜) :
    (α_ A B C).inv = homOfNet (A := A ⊗ (B ⊗ C)) (A' := (A ⊗ B) ⊗ C)
      (α_ A.1.net B.1.net C.1.net).inv := rfl

/-- Stacking morphisms of spreads `l` and `l'` gives a morphism of spread `max l l'`. -/
theorem HasSpread.stackHom {f : A ⟶ A'} {g : B ⟶ B'} (hf : HasSpread f l) (hg : HasSpread g l') :
    HasSpread (f ⊗ₘ g) (max l l') := by
  obtain ⟨α, rfl⟩ := hf
  obtain ⟨β, rfl⟩ := hg
  refine ⟨tensorBSH (α.weaken (le_max_left l l')) (β.weaken (le_max_right l l')), ?_⟩
  rw [tensorHom_def', ← homMk_stackHom, homMk_weaken, homMk_weaken]

/-! ### The symmetric structure -/

/-- The Koszul braiding of stacked systems, as a spread-`0` isomorphism. -/
def stackBraiding (A B : BoundedSpreadCat X 𝕜) : A ⊗ B ≅ B ⊗ A :=
  isoOfNet (β_ A.1.net B.1.net)

theorem stackBraiding_hom (A B : BoundedSpreadCat X 𝕜) :
    (stackBraiding A B).hom = homOfNet (A := A ⊗ B) (A' := B ⊗ A) (β_ A.1.net B.1.net).hom :=
  rfl

/-- Naturality of the braiding with respect to stacking of arbitrary bounded-spread morphisms. -/
theorem stackHom_stackBraiding (f : A ⟶ A') (g : B ⟶ B') :
    stackHom f g ≫ (stackBraiding A' B').hom = (stackBraiding A B).hom ≫ stackHom g f := by
  obtain ⟨l, α, β, rfl, rfl⟩ := exists_common_spread f g
  rw [homMk_stackHom, homMk_stackHom, stackBraiding_hom, stackBraiding_hom]
  refine (homMk_comp_homOfNet _ _).trans ((congrArg homMk (BoundedSpreadHom.ext fun S => ?_)).trans
    (homOfNet_comp_homMk _ _).symm)
  exact BraidedCategory.braiding_naturality (α.app S) (β.app S)

/-- Stacking with the Koszul braiding makes `BoundedSpreadCat X 𝕜` a symmetric monoidal
category. -/
instance symmetricCategory : SymmetricCategory (BoundedSpreadCat X 𝕜) where
  braiding := stackBraiding
  braiding_naturality_right A _ _ g := stackHom_stackBraiding (𝟙 A) g
  braiding_naturality_left f B := stackHom_stackBraiding f (𝟙 B)
  hexagon_forward A B C := by
    rw [associator_hom_def, associator_hom_def, stackBraiding_hom, stackBraiding_hom,
      stackBraiding_hom, whiskerRight_def', whiskerLeft_def', ← homOfNet_id, ← homOfNet_id]
    erw [stackHom_homOfNet, stackHom_homOfNet, homOfNet_comp, homOfNet_comp, homOfNet_comp,
      homOfNet_comp]
    congr 1
    exact BraidedCategory.hexagon_forward A.1.net B.1.net C.1.net
  hexagon_reverse A B C := by
    rw [associator_inv_def, associator_inv_def, stackBraiding_hom, stackBraiding_hom,
      stackBraiding_hom, whiskerRight_def', whiskerLeft_def', ← homOfNet_id, ← homOfNet_id]
    erw [stackHom_homOfNet, stackHom_homOfNet, homOfNet_comp, homOfNet_comp, homOfNet_comp,
      homOfNet_comp]
    congr 1
    exact BraidedCategory.hexagon_reverse A.1.net B.1.net C.1.net
  symmetry A B := by
    rw [stackBraiding_hom, stackBraiding_hom]
    erw [homOfNet_comp]
    exact (congrArg homOfNet (SymmetricCategory.symmetry A.1.net B.1.net)).trans
      (homOfNet_id (A ⊗ B))

end BoundedSpreadCat
