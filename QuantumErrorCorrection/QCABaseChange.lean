import QuantumErrorCorrection.QCAClass
import QuantumErrorCorrection.AlgebraicCategories.SuperStarBaseChange

/-!
# Base change of bounded-spread homomorphisms, QCAs and circuits

Let `σ : R ⟶ S` be a morphism of `FlatCommStarRingCat`: a star ring map making `S` flat over
`R`. Base change of super `*`-algebras along `σ` (`SuperStarAlgCat.baseChange`) gives base
change of quasi-local algebras (`QuasiLocalAlgebra.baseChange`), regionwise: isotony is kept by
flatness and microcausality by compatibility of Koszul signs. This extends to:

* bounded-spread homomorphisms, keeping the spread (`BoundedSpreadHom.baseChange`);
* a functor `BoundedSpreadCat.baseChange σ : BoundedSpreadCat X R ⥤ BoundedSpreadCat X S`;
* QCAs, via `Functor.mapAut` (`QCA.baseChange σ A : QCA A →* QCA (…)`), sending layers to
  layers with the same blocks, hence circuits to circuits (`QCA.baseChange_mem_circuitSubgroup`);
* QCAs modulo circuits on a fixed system (`QCAClass.baseChange`);
* QCAs modulo circuits across systems (`QCAStackClass.baseChange`). This is well defined because
  base change commutes with transport along net isomorphisms.
* Base change commutes with stacking, so it is a homomorphism of commutative monoids
  (`QCAStackClass.baseChangeHom`).
* Functoriality: base change along the identity is the identity and along a composite is the
  composite (via `R ⊗[R] A ≃ A` and `T ⊗[S] (S ⊗[R] A) ≃ T ⊗[R] A`). So QCAs modulo circuits form
  a functor `QCAStackClass.baseChangeFunctor X : FlatCommStarRingCat ⥤ CommMonCat`.
-/

noncomputable section

open CategoryTheory NNReal RegionCat BoundedSpreadCat

universe u

/-! ### Quasi-local algebras -/

namespace QuasiLocalAlgebra

variable {X : Type u} [DecidableEq X] {R S : FlatCommStarRingCat.{u}} (σ : R ⟶ S)

/-- Base change of a quasi-local algebra along a flat star ring map `σ`: the local algebra on `T`
is `S ⊗[R] A(T)`. Isotony survives because `S` is flat over `R`. Microcausality is checked on
generators `1 ⊗ a`, using that `σ` maps Koszul signs to Koszul signs. -/
def baseChange (A : QuasiLocalAlgebra X R) : QuasiLocalAlgebra X S where
  net := A.net ⋙ SuperStarAlgCat.baseChange σ
  isotony h := SuperStarAlgCat.baseChange_map_injective σ (A.isotony h)
  superCommuting {T₁ T₂} hT {i j} {x} {y} hx hy := by
    let _ := σ.toAlgebra
    have := σ.starModule
    exact SuperStarAlgebra.baseChangeHom_superCommute
      (A.net.map (RegionCat.homOfSubset Finset.subset_union_left)).1
      (A.net.map (RegionCat.homOfSubset Finset.subset_union_right)).1
      (fun ha hc => A.superCommuting hT ha hc) hx hy

theorem baseChange_flat (A : QuasiLocalAlgebra X R) (hA : ∀ T, Module.Flat R (A.net.obj T))
    (T : RegionCat X) : Module.Flat S ((A.baseChange σ).net.obj T) := by
  let _ := σ.toAlgebra
  have := hA T
  exact Module.Flat.baseChange R S (A.net.obj T)

end QuasiLocalAlgebra

variable {X : Type u} [DecidableEq X] [MetricSpace X] [FiniteClosedBalls X]
variable {R S : FlatCommStarRingCat.{u}} (σ : R ⟶ S)

/-! ### Bounded-spread homomorphisms -/

namespace BoundedSpreadHom

variable {l l' : ℝ≥0} {𝒜 𝒜' 𝒜'' : QuasiLocalAlgebra X R}

/-- Base change of a bounded-spread homomorphism along `σ`, componentwise; the spread is kept. -/
def baseChange (α : BoundedSpreadHom l 𝒜 𝒜') :
    BoundedSpreadHom l (𝒜.baseChange σ) (𝒜'.baseChange σ) where
  toNatTrans := Functor.whiskerRight α.toNatTrans (SuperStarAlgCat.baseChange σ)

theorem baseChange_app (α : BoundedSpreadHom l 𝒜 𝒜') (T : RegionCat X) :
    (α.baseChange σ).app T = (SuperStarAlgCat.baseChange σ).map (α.app T) :=
  rfl

theorem baseChange_weaken (h : l ≤ l') (α : BoundedSpreadHom l 𝒜 𝒜') :
    (α.weaken h).baseChange σ = (α.baseChange σ).weaken h := by
  ext1 T
  rw [baseChange_app, weaken_app, weaken_app, baseChange_app, Functor.map_comp]
  rfl

theorem baseChange_comp (α : BoundedSpreadHom l 𝒜 𝒜') (β : BoundedSpreadHom l' 𝒜' 𝒜'') :
    (α.comp β).baseChange σ = (α.baseChange σ).comp (β.baseChange σ) := by
  ext1 T
  rw [baseChange_app, comp_app, comp_app, baseChange_app, baseChange_app, Functor.map_comp,
    Functor.map_comp]
  rfl

theorem baseChange_id (𝒜 : QuasiLocalAlgebra X R) :
    (BoundedSpreadHom.id 𝒜).baseChange σ = BoundedSpreadHom.id (𝒜.baseChange σ) := by
  ext1 T
  rw [baseChange_app, id_app, id_app]
  rfl

theorem baseChange_ofNetHom (η : 𝒜.net ⟶ 𝒜'.net) :
    (ofNetHom η).baseChange σ =
      ofNetHom (𝒜 := 𝒜.baseChange σ) (𝒜' := 𝒜'.baseChange σ)
        (Functor.whiskerRight η (SuperStarAlgCat.baseChange σ)) := by
  ext1 T
  rw [baseChange_app, ofNetHom_app, Functor.map_comp]
  rfl

theorem PreservesRegion.baseChange {α : BoundedSpreadHom l 𝒜 𝒜'} {T : RegionCat X}
    (hα : α.PreservesRegion T) : (α.baseChange σ).PreservesRegion T := by
  obtain ⟨γ, hγ⟩ := hα
  refine ⟨(SuperStarAlgCat.baseChange σ).map γ, ?_⟩
  rw [baseChange_app, hγ, Functor.map_comp]
  rfl

end BoundedSpreadHom

/-! ### The base change functor on systems -/

namespace BoundedSpreadCat

open BoundedSpreadHom

/-- Base change of systems along `σ`. -/
def baseChangeObj (A : BoundedSpreadCat X R) : BoundedSpreadCat X S :=
  ⟨A.1.baseChange σ, QuasiLocalAlgebra.baseChange_flat σ A.1 A.flat⟩

/-- Base change along `σ` as a functor between categories of systems with bounded-spread
morphisms. -/
def baseChange : BoundedSpreadCat X R ⥤ BoundedSpreadCat X S where
  obj := baseChangeObj σ
  map {A B} f := Quotient.map (sa := germSetoid A.1 B.1)
    (sb := germSetoid (baseChangeObj σ A).1 (baseChangeObj σ B).1)
    (fun a => ⟨a.1, a.2.baseChange σ⟩)
    (fun _ _ ⟨m, ha, hb, h⟩ => ⟨m, ha, hb,
      (BoundedSpreadHom.baseChange_weaken σ ha _).symm.trans
        ((congrArg (BoundedSpreadHom.baseChange σ) h).trans
          (BoundedSpreadHom.baseChange_weaken σ hb _))⟩) f
  map_id A := by
    rw [← homMk_id]
    exact congrArg homMk (BoundedSpreadHom.baseChange_id σ A.1)
  map_comp f g := by
    obtain ⟨l, α, rfl⟩ := homMk_surjective f
    obtain ⟨l', β, rfl⟩ := homMk_surjective g
    rw [← homMk_comp]
    exact (congrArg homMk (BoundedSpreadHom.baseChange_comp σ α β)).trans (homMk_comp _ _)

theorem baseChange_map_homMk {A B : BoundedSpreadCat X R} {l : ℝ≥0}
    (α : BoundedSpreadHom l A.1 B.1) :
    (baseChange σ).map (homMk α) =
      homMk (A := baseChangeObj σ A) (B := baseChangeObj σ B) (α.baseChange σ) :=
  rfl

theorem baseChange_map_homOfNet {A B : BoundedSpreadCat X R} (η : A.1.net ⟶ B.1.net) :
    (baseChange σ).map (homOfNet η) =
      homOfNet (A := baseChangeObj σ A) (A' := baseChangeObj σ B)
        (Functor.whiskerRight η (SuperStarAlgCat.baseChange σ)) := by
  rw [homOfNet, baseChange_map_homMk, BoundedSpreadHom.baseChange_ofNetHom]
  rfl

theorem baseChange_mapIso_isoOfNet {A B : BoundedSpreadCat X R} (η : A.1.net ≅ B.1.net) :
    (baseChange σ).mapIso (isoOfNet η) =
      isoOfNet (A := baseChangeObj σ A) (A' := baseChangeObj σ B)
        (Functor.isoWhiskerRight η (SuperStarAlgCat.baseChange σ)) :=
  Iso.ext (baseChange_map_homOfNet σ η.hom)

end BoundedSpreadCat

/-! ### QCAs and circuits -/

namespace QCA

open BoundedSpreadHom

variable {A B : BoundedSpreadCat X R}

variable (A) in
/-- Base change of QCAs along `σ`. -/
def baseChange : QCA A →* QCA (baseChangeObj σ A) := (BoundedSpreadCat.baseChange σ).mapAut A

/-- Base change maps a layer to a layer of the same range, with the same blocks. -/
theorem IsLayer.baseChange {u : QCA A} {r : ℝ≥0} (hu : u.IsLayer r) :
    (QCA.baseChange σ A u).IsLayer r := by
  obtain ⟨blocks, hd, α, β, hα, hβ, hR⟩ := hu
  refine ⟨blocks, hd, α.baseChange σ, β.baseChange σ, ?_, ?_,
    fun T hTs => ⟨(hR T hTs).1.baseChange σ, (hR T hTs).2.baseChange σ⟩⟩
  · change homMk _ = (BoundedSpreadCat.baseChange σ).map u.hom
    rw [← hα, baseChange_map_homMk]
    rfl
  · change homMk _ = (BoundedSpreadCat.baseChange σ).map u.inv
    rw [← hβ, baseChange_map_homMk]
    rfl

/-- Base change maps circuits to circuits. -/
theorem baseChange_mem_circuitSubgroup {u : QCA A} (hu : u ∈ circuitSubgroup A) :
    QCA.baseChange σ A u ∈ circuitSubgroup (baseChangeObj σ A) := by
  have h : circuitSubgroup A ≤ (circuitSubgroup (baseChangeObj σ A)).comap
      (QCA.baseChange σ A) := by
    rw [circuitSubgroup, Subgroup.closure_le]
    rintro w ⟨r, hw⟩
    exact Subgroup.subset_closure ⟨r, hw.baseChange σ⟩
  exact h hu

/-- Base change commutes with transport along net isomorphisms. -/
theorem baseChange_transport (η : A.1.net ≅ B.1.net) (u : QCA A) :
    QCA.baseChange σ B (transport η u) =
      transport (A := baseChangeObj σ A) (B := baseChangeObj σ B)
        (Functor.isoWhiskerRight η (SuperStarAlgCat.baseChange σ)) (QCA.baseChange σ A u) := by
  change (BoundedSpreadCat.baseChange σ).mapIso ((isoOfNet η).conjAut u) =
    (isoOfNet (Functor.isoWhiskerRight η (SuperStarAlgCat.baseChange σ))).conjAut
      ((BoundedSpreadCat.baseChange σ).mapIso u)
  rw [Functor.map_conjAut, baseChange_mapIso_isoOfNet]
  rfl

end QCA

/-! ### Classes modulo circuits -/

namespace QCAClass

variable (A : BoundedSpreadCat X R)

/-- Base change of QCAs modulo circuits on a fixed system. -/
def baseChange : QCAClass A → QCAClass (baseChangeObj σ A) :=
  Quotient.map (sa := QuotientGroup.leftRel (QCA.circuitSubgroup A))
    (sb := QuotientGroup.leftRel (QCA.circuitSubgroup (baseChangeObj σ A)))
    (QCA.baseChange σ A) fun u v h => by
      refine QuotientGroup.leftRel_apply.2 ?_
      rw [← map_inv, ← map_mul]
      exact QCA.baseChange_mem_circuitSubgroup σ (QuotientGroup.leftRel_apply.1 h)

end QCAClass

namespace QCAStackClass

/-- Base change of QCAs modulo circuits, across systems. -/
def baseChange : QCAStackClass X R → QCAStackClass X S :=
  Quotient.map (sa := setoid X R) (sb := setoid X S)
    (fun p => ⟨baseChangeObj σ p.1, QCA.baseChange σ p.1 p.2⟩)
    fun _ _ ⟨η, h⟩ => ⟨Functor.isoWhiskerRight η (SuperStarAlgCat.baseChange σ), by
      rw [← QCA.baseChange_transport, ← map_inv, ← map_mul]
      exact QCA.baseChange_mem_circuitSubgroup σ h⟩

theorem baseChange_mk (A : BoundedSpreadCat X R) (u : QCA A) :
    baseChange σ (mk A u) = mk (baseChangeObj σ A) (QCA.baseChange σ A u) :=
  rfl

end QCAStackClass

/-! ### Base change commutes with stacking -/

namespace SuperStarAlgCat

open SuperStarAlgebra MonoidalCategory

/-- Base change commutes with the super tensor product of super `*`-algebras. -/
def stackBaseChangeIso (A B : SuperStarAlgCat R) :
    (baseChange σ).obj (A ⊗ B) ≅ (baseChange σ).obj A ⊗ (baseChange σ).obj B :=
  letI := σ.toAlgebra
  haveI := σ.starModule
  isoOfStarAlgEquiv (stackBaseChange R A S B) stackBaseChangeₗ_mem stackBaseChange_symm_mem

theorem stackBaseChangeIso_naturality {A A' B B' : SuperStarAlgCat R} (f : A ⟶ A')
    (g : B ⟶ B') :
    (baseChange σ).map (f ⊗ₘ g) ≫ (stackBaseChangeIso σ A' B').hom =
      (stackBaseChangeIso σ A B).hom ≫ ((baseChange σ).map f ⊗ₘ (baseChange σ).map g) := by
  let _ := σ.toAlgebra
  have := σ.starModule
  refine hom_ext fun x => ?_
  induction x using baseChangeSuperTensor_induction with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
  | tmul s a b _ _ => rfl

/-- Base change of the unit is the unit. -/
def unitBaseChangeIso : (baseChange σ).obj (SuperStarAlgCat.of R) ≅ SuperStarAlgCat.of S :=
  letI := σ.toAlgebra
  haveI := σ.starModule
  isoOfStarAlgEquiv (unitBaseChange R S) unitBaseChange_mem unitBaseChange_symm_mem

end SuperStarAlgCat

namespace QuasiLocalAlgebra

open MonoidalCategory

variable {X' : Type u} [DecidableEq X']

/-- Base change of a stacked net is the stack of the base-changed nets. -/
def stackBaseChangeNetIso (𝒜 ℬ : RegionCat X' ⥤ SuperStarAlgCat R) :
    (𝒜 ⊗ ℬ) ⋙ SuperStarAlgCat.baseChange σ ≅
      (𝒜 ⋙ SuperStarAlgCat.baseChange σ) ⊗ (ℬ ⋙ SuperStarAlgCat.baseChange σ) :=
  NatIso.ofComponents (fun T => SuperStarAlgCat.stackBaseChangeIso σ (𝒜.obj T) (ℬ.obj T))
    fun f => SuperStarAlgCat.stackBaseChangeIso_naturality σ (𝒜.map f) (ℬ.map f)

/-- Base change of the trivial net is the trivial net. -/
def unitBaseChangeNetIso :
    (𝟙_ (RegionCat X' ⥤ SuperStarAlgCat R)) ⋙ SuperStarAlgCat.baseChange σ ≅
      𝟙_ (RegionCat X' ⥤ SuperStarAlgCat S) :=
  NatIso.ofComponents (fun _ => SuperStarAlgCat.unitBaseChangeIso σ) fun _ => by
    change (SuperStarAlgCat.baseChange σ).map (𝟙 (SuperStarAlgCat.of R)) ≫
      (SuperStarAlgCat.unitBaseChangeIso σ).hom =
        (SuperStarAlgCat.unitBaseChangeIso σ).hom ≫ 𝟙 (SuperStarAlgCat.of S)
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end QuasiLocalAlgebra

namespace QCA

open MonoidalCategory BoundedSpreadHom

variable {A B : BoundedSpreadCat X R}

/-- Base change of a stack of QCAs is, up to transport, the stack of the base-changed QCAs. -/
theorem baseChange_stack (u : QCA A) (v : QCA B) :
    transport (A := baseChangeObj σ (A ⊗ B)) (B := baseChangeObj σ A ⊗ baseChangeObj σ B)
        (QuasiLocalAlgebra.stackBaseChangeNetIso σ A.1.net B.1.net)
        (QCA.baseChange σ (A ⊗ B) (stackMonoidHom A B (u, v))) =
      stackMonoidHom _ _ (QCA.baseChange σ A u, QCA.baseChange σ B v) := by
  obtain ⟨l, α, β, hα, hβ⟩ := exists_common_spread u.hom v.hom
  apply Iso.ext
  change ((isoOfNet _).conjAut _).hom = _
  rw [Iso.conjAut_hom, Iso.conj_apply]
  change homOfNet _ ≫ (BoundedSpreadCat.baseChange σ).map (u.hom ⊗ₘ v.hom) ≫ homOfNet _ =
    (BoundedSpreadCat.baseChange σ).map u.hom ⊗ₘ (BoundedSpreadCat.baseChange σ).map v.hom
  rw [← hα, ← hβ]
  have h1 : homMk α ⊗ₘ homMk β = homMk (A := A ⊗ B) (B := A ⊗ B) (tensorBSH α β) :=
    homMk_stackHom α β
  have h3 : homMk (A := baseChangeObj σ A) (B := baseChangeObj σ A) (α.baseChange σ) ⊗ₘ
      homMk (A := baseChangeObj σ B) (B := baseChangeObj σ B) (β.baseChange σ) =
        homMk (A := baseChangeObj σ A ⊗ baseChangeObj σ B)
          (B := baseChangeObj σ A ⊗ baseChangeObj σ B)
          (tensorBSH (α.baseChange σ) (β.baseChange σ)) :=
    homMk_stackHom _ _
  have h2 : (BoundedSpreadCat.baseChange σ).map (homMk (A := A ⊗ B) (B := A ⊗ B) (tensorBSH α β)) =
      homMk (A := baseChangeObj σ (A ⊗ B)) (B := baseChangeObj σ (A ⊗ B))
        ((tensorBSH α β).baseChange σ) := rfl
  have hα' : (BoundedSpreadCat.baseChange σ).map (homMk α) =
      homMk (A := baseChangeObj σ A) (B := baseChangeObj σ A) (α.baseChange σ) := rfl
  have hβ' : (BoundedSpreadCat.baseChange σ).map (homMk β) =
      homMk (A := baseChangeObj σ B) (B := baseChangeObj σ B) (β.baseChange σ) := rfl
  rw [h1, h2, hα', hβ']
  refine ((congrArg _ (homMk_comp_homOfNet _ _)).trans ((homOfNet_comp_homMk _ _).trans
    (congrArg homMk (BoundedSpreadHom.ext fun T => ?_)))).trans h3.symm
  exact (congrArg
    (fun t => (SuperStarAlgCat.stackBaseChangeIso σ (A.1.net.obj T) (B.1.net.obj T)).inv ≫ t)
    (SuperStarAlgCat.stackBaseChangeIso_naturality σ (α.app T) (β.app T))).trans
    (Iso.inv_hom_id_assoc _ _)

end QCA

namespace QCAStackClass

/-- Base change of QCAs modulo circuits, as a homomorphism of commutative monoids under
stacking. -/
def baseChangeHom : QCAStackClass X R →* QCAStackClass X S where
  toFun := baseChange σ
  map_one' := by
    change mk _ (QCA.baseChange σ _ 1) = mk _ 1
    rw [map_one]
    exact mk_eq_mk_of_iso (A := baseChangeObj σ (MonoidalCategory.tensorUnit _))
      (B := MonoidalCategory.tensorUnit _) (QuasiLocalAlgebra.unitBaseChangeNetIso σ) 1 1
      (map_one _)
  map_mul' x y := by
    obtain ⟨A, u, rfl⟩ := exists_mk x
    obtain ⟨B, v, rfl⟩ := exists_mk y
    rw [mk_mul_mk, baseChange_mk, baseChange_mk, baseChange_mk, mk_mul_mk]
    exact mk_eq_mk_of_iso (A := baseChangeObj σ (MonoidalCategory.tensorObj A B))
      (B := MonoidalCategory.tensorObj (baseChangeObj σ A) (baseChangeObj σ B))
      (QuasiLocalAlgebra.stackBaseChangeNetIso σ A.1.net B.1.net) _ _ (QCA.baseChange_stack σ u v)

end QCAStackClass

/-! ### Functoriality in the coefficients -/

namespace SuperStarAlgCat

open SuperStarAlgebra

variable (R) in
/-- Base change along the identity is naturally isomorphic to the identity functor. -/
def baseChangeIdIso : baseChange (𝟙 R) ≅ 𝟭 (SuperStarAlgCat R) :=
  NatIso.ofComponents
    (fun A => isoOfStarAlgEquiv (lidBaseChange R A) lidBaseChange_mem lidBaseChange_symm_mem)
    fun f => hom_ext fun x => baseChangeHom_lid_naturality f.1 x

variable {T : FlatCommStarRingCat.{u}} (τ : S ⟶ T)

/-- Base change along a composite is naturally isomorphic to the composite of base changes. -/
def baseChangeCompIso : baseChange (σ ≫ τ) ≅ baseChange σ ⋙ baseChange τ :=
  letI := σ.toAlgebra
  letI := τ.toAlgebra
  letI := (σ ≫ τ).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := σ.starModule
  haveI := τ.starModule
  haveI := (σ ≫ τ).starModule
  NatIso.ofComponents
    (fun A => (isoOfStarAlgEquiv (cancelBaseChangeStar R A S T) cancelBaseChangeₗ_mem
      cancelBaseChangeStar_symm_mem).symm)
    fun {A B} f => hom_ext fun x => by
      induction x using TensorProduct.induction_on with
      | zero => exact (map_zero _).trans (map_zero _).symm
      | add x y hx hy =>
        exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
      | tmul t a => rfl

end SuperStarAlgCat

namespace QCAStackClass

open BoundedSpreadHom

variable (R) in
theorem baseChange_id_apply (x : QCAStackClass X R) : baseChange (𝟙 R) x = x := by
  obtain ⟨A, u, rfl⟩ := exists_mk x
  rw [baseChange_mk]
  refine mk_eq_mk_of_iso (A := baseChangeObj (𝟙 R) A) (B := A)
    (Functor.isoWhiskerLeft A.1.net (SuperStarAlgCat.baseChangeIdIso R)) _ _ ?_
  obtain ⟨l, α, hα⟩ := homMk_surjective u.hom
  apply Iso.ext
  change ((isoOfNet _).conjAut _).hom = _
  have hu : (QCA.baseChange (𝟙 R) A u).hom =
      homMk (A := baseChangeObj (𝟙 R) A) (B := baseChangeObj (𝟙 R) A) (α.baseChange (𝟙 R)) := by
    change (BoundedSpreadCat.baseChange (𝟙 R)).map u.hom = _
    rw [← hα]
    rfl
  rw [Iso.conjAut_hom, Iso.conj_apply, hu, ← hα]
  let η := Functor.isoWhiskerLeft A.1.net (SuperStarAlgCat.baseChangeIdIso R)
  refine ((congrArg ((isoOfNet (A := baseChangeObj (𝟙 R) A) (A' := A) η).inv ≫ ·)
    (homMk_comp_homOfNet (A := baseChangeObj (𝟙 R) A) (A' := baseChangeObj (𝟙 R) A) (A'' := A)
      (α.baseChange (𝟙 R)) η.hom)).trans
    ((homOfNet_comp_homMk (A := A) (A' := baseChangeObj (𝟙 R) A) (A'' := A) η.inv
      ((α.baseChange (𝟙 R)).postNet η.hom)).trans
    (congrArg homMk (BoundedSpreadHom.ext fun T => ?_))))
  exact NatIso.naturality_1 (SuperStarAlgCat.baseChangeIdIso R) (α.app T)

variable {T : FlatCommStarRingCat.{u}} (τ : S ⟶ T)

theorem baseChange_comp_apply (x : QCAStackClass X R) :
    baseChange (σ ≫ τ) x = baseChange τ (baseChange σ x) := by
  obtain ⟨A, u, rfl⟩ := exists_mk x
  rw [baseChange_mk, baseChange_mk, baseChange_mk]
  refine mk_eq_mk_of_iso (A := baseChangeObj (σ ≫ τ) A) (B := baseChangeObj τ (baseChangeObj σ A))
    (Functor.isoWhiskerLeft A.1.net (SuperStarAlgCat.baseChangeCompIso σ τ)) _ _ ?_
  obtain ⟨l, α, hα⟩ := homMk_surjective u.hom
  apply Iso.ext
  change ((isoOfNet _).conjAut _).hom = (BoundedSpreadCat.baseChange τ).map
    ((BoundedSpreadCat.baseChange σ).map u.hom)
  have hu : (QCA.baseChange (σ ≫ τ) A u).hom =
      homMk (A := baseChangeObj (σ ≫ τ) A) (B := baseChangeObj (σ ≫ τ) A)
        (α.baseChange (σ ≫ τ)) := by
    change (BoundedSpreadCat.baseChange (σ ≫ τ)).map u.hom = _
    rw [← hα]
    rfl
  have h' : (BoundedSpreadCat.baseChange τ).map ((BoundedSpreadCat.baseChange σ).map (homMk α)) =
      homMk (A := baseChangeObj τ (baseChangeObj σ A))
        (B := baseChangeObj τ (baseChangeObj σ A)) ((α.baseChange σ).baseChange τ) := rfl
  rw [Iso.conjAut_hom, Iso.conj_apply, hu, ← hα, h']
  let η := Functor.isoWhiskerLeft A.1.net (SuperStarAlgCat.baseChangeCompIso σ τ)
  refine ((congrArg ((isoOfNet (A := baseChangeObj (σ ≫ τ) A)
      (A' := baseChangeObj τ (baseChangeObj σ A)) η).inv ≫ ·)
    (homMk_comp_homOfNet (A := baseChangeObj (σ ≫ τ) A) (A' := baseChangeObj (σ ≫ τ) A)
      (A'' := baseChangeObj τ (baseChangeObj σ A)) (α.baseChange (σ ≫ τ)) η.hom)).trans
    ((homOfNet_comp_homMk (A := baseChangeObj τ (baseChangeObj σ A))
      (A' := baseChangeObj (σ ≫ τ) A) (A'' := baseChangeObj τ (baseChangeObj σ A)) η.inv
      ((α.baseChange (σ ≫ τ)).postNet η.hom)).trans
    (congrArg homMk (BoundedSpreadHom.ext fun T' => ?_))))
  exact NatIso.naturality_1 (SuperStarAlgCat.baseChangeCompIso σ τ) (α.app T')

variable (X) in
/-- QCAs modulo circuits under stacking, as a functor of the coefficients: from commutative
`*`-rings with flat star ring maps to commutative monoids. -/
def baseChangeFunctor : FlatCommStarRingCat.{u} ⥤ CommMonCat.{u + 1} where
  obj R := CommMonCat.of (QCAStackClass X R)
  map σ := CommMonCat.ofHom (baseChangeHom σ)
  map_id R := CommMonCat.hom_ext (MonoidHom.ext (baseChange_id_apply R))
  map_comp σ τ := CommMonCat.hom_ext (MonoidHom.ext (baseChange_comp_apply σ τ))

end QCAStackClass
