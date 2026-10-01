import Mathlib.CategoryTheory.Monoidal.Action.End
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Flat.Basic
import QuantumErrorCorrection.CommGrpInclCat
import QuantumErrorCorrection.FlatCommStarRingCat
import QuantumErrorCorrection.GroupAlgebraStar

/-!
# The group ring as a symmetric monoidal functor

`G ↦ ℤ[G]` sends a commutative group to its integral group ring, a commutative `*`-ring with
`star g = g⁻¹`. An injective homomorphism `f : G ↪ H` induces `ℤ[G] → ℤ[H]`, which is flat:
`ℤ[H]` is a *free* `ℤ[G]`-module, with one basis element per coset of `f(G)`
(`GroupRing.free_of_injective`). So the group ring is a functor
`CommGrpInclCat.groupRingFunctor` from commutative groups with injective homomorphisms
(`CommGrpInclCat`) to commutative `*`-rings with flat star ring maps (`FlatCommStarRingCat`).

It is symmetric monoidal, from products of groups to `⊗[ℤ]`:
- `ℤ[G] ⊗ ℤ[H] ≅ ℤ[G × H]`, `g ⊗ h ↦ (g, h)` (`GroupRing.tensorRingEquiv`), compatible with
  `star`;
- `ℤ ≅ ℤ[1]`;
- the swap `G × H ≃ H × G` goes to the swap of tensor factors (`groupRingFunctorBraided`).

All coherence conditions are checked on basis elements `g ⊗ h ⊗ k`: ring homomorphisms out of
tensor products of group rings are determined there (`GroupRing.tensor_ringHom_ext₂`, `…₃`).

Consequently `CommGrpInclCat` acts on `FlatCommStarRingCat` (an actegory,
`CommGrpInclCat.groupRingAction`): `G ⊙ₗ R = ℤ[G] ⊗[ℤ] R`, an injective `G ↪ H` acting by the
flat map `ℤ[G] ⊗ R → ℤ[H] ⊗ R`. It is the monoidal functor followed by the action of
`FlatCommStarRingCat` on itself.

## Freeness

Write `Q = H ⧸ f(G)` and choose coset representatives `out : Q → H`. Every `h : H` splits
uniquely as `out [h] * f g`; write `g = cosetPart h`. This gives `H ≃ Q × G`, and
`cosetPart (f g * h) = g * cosetPart h`, so the additive equivalence
`ℤ[H] ≃ (H →₀ ℤ) ≃ (Q × G →₀ ℤ) ≃ (Q →₀ G →₀ ℤ) ≃ (Q →₀ ℤ[G])` is `ℤ[G]`-linear.
-/

noncomputable section

open MonoidAlgebra

namespace GroupRing

section Flat

variable {G H : Type*} [CommGroup G] [CommGroup H] {f : G →* H} (hf : Function.Injective f)

local notation "Q" => H ⧸ f.range

private lemma out_inv_mul_mem (h : H) :
    (Quotient.out (QuotientGroup.mk h : Q))⁻¹ * h ∈ f.range :=
  QuotientGroup.eq.1 (QuotientGroup.out_eq' _)

/-- The `G`-component of `h` relative to the chosen coset representative of `[h]`. -/
def cosetPart (h : H) : G :=
  (MonoidHom.ofInjective hf).symm ⟨_, out_inv_mul_mem h⟩

theorem apply_cosetPart (h : H) :
    f (cosetPart hf h) = (Quotient.out (QuotientGroup.mk h : Q))⁻¹ * h := by
  rw [cosetPart, ← MonoidHom.ofInjective_apply hf, MulEquiv.apply_symm_apply]

theorem mk_mul_left (g : G) (h : H) : (QuotientGroup.mk (f g * h) : Q) = QuotientGroup.mk h := by
  rw [mul_comm]
  exact QuotientGroup.mk_mul_of_mem h (MonoidHom.mem_range.2 ⟨g, rfl⟩)

theorem cosetPart_mul (g : G) (h : H) : cosetPart hf (f g * h) = g * cosetPart hf h := by
  apply hf
  rw [apply_cosetPart, mk_mul_left, map_mul, apply_cosetPart]
  exact mul_left_comm _ _ _

/-- `H ≃ (H ⧸ f(G)) × G`, `h ↦ ([h], cosetPart h)`. -/
def cosetEquiv : H ≃ Q × G where
  toFun h := (QuotientGroup.mk h, cosetPart hf h)
  invFun p := Quotient.out p.1 * f p.2
  left_inv h := by
    change Quotient.out (QuotientGroup.mk h : Q) * f (cosetPart hf h) = h
    rw [apply_cosetPart, mul_inv_cancel_left]
  right_inv p := by
    obtain ⟨q, g⟩ := p
    have hq : (QuotientGroup.mk (Quotient.out q * f g) : Q) = q := by
      rw [QuotientGroup.mk_mul_of_mem _ (MonoidHom.mem_range.2 ⟨g, rfl⟩), QuotientGroup.out_eq']
    refine Prod.ext hq (hf ?_)
    change f (cosetPart hf (Quotient.out q * f g)) = f g
    rw [apply_cosetPart, hq, inv_mul_cancel_left]

/-- The additive equivalence `ℤ[H] ≃ (H ⧸ f(G) →₀ ℤ[G])`. -/
def cosetAddEquiv : MonoidAlgebra ℤ H ≃+ (Q →₀ MonoidAlgebra ℤ G) :=
  coeffAddEquiv.trans ((Finsupp.domCongr (cosetEquiv hf)).trans
    (Finsupp.curryAddEquiv.trans (Finsupp.mapRange.addEquiv coeffAddEquiv.symm)))

theorem cosetAddEquiv_single (h : H) (r : ℤ) :
    cosetAddEquiv hf (single h r) =
      Finsupp.single (QuotientGroup.mk h) (single (cosetPart hf h) r) := by
  simp [cosetAddEquiv, cosetEquiv, Finsupp.domCongr_apply, Finsupp.equivMapDomain_single,
    Finsupp.curry_single, Finsupp.mapRange_single]

variable (f) in
/-- The `ℤ[G]`-algebra structure on `ℤ[H]` induced by `f`. -/
abbrev algebraOfHom : Algebra (MonoidAlgebra ℤ G) (MonoidAlgebra ℤ H) :=
  (mapDomainRingHom ℤ f).toAlgebra

include hf in
/-- `ℤ[H]` is a free `ℤ[G]`-module when `f : G → H` is injective. -/
theorem free_of_injective :
    letI := algebraOfHom f
    Module.Free (MonoidAlgebra ℤ G) (MonoidAlgebra ℤ H) := by
  let := algebraOfHom f
  let φ : MonoidAlgebra ℤ H ≃ₗ[MonoidAlgebra ℤ G] (Q →₀ MonoidAlgebra ℤ G) :=
    { cosetAddEquiv hf with
      map_smul' := fun c x => by
        simp only [AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
          RingHom.id_apply]
        induction c using MonoidAlgebra.induction_linear with
        | zero => rw [zero_smul, map_zero, zero_smul]
        | add c c' hc hc' => rw [add_smul, map_add, hc, hc', add_smul]
        | single g r =>
          induction x using MonoidAlgebra.induction_linear with
          | zero => rw [smul_zero, map_zero, smul_zero]
          | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, smul_add]
          | single h r' =>
            rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mapDomainRingHom_apply,
              mapDomain_single, single_mul_single, cosetAddEquiv_single, cosetAddEquiv_single,
              Finsupp.smul_single, smul_eq_mul, single_mul_single, mk_mul_left,
              cosetPart_mul] }
  exact Module.Free.of_equiv φ.symm

include hf in
/-- An injective homomorphism of commutative groups induces a flat map of group rings. -/
theorem flat_of_injective : (mapDomainRingHom ℤ f).Flat := by
  let := algebraOfHom f
  have := free_of_injective hf
  exact Module.Flat.of_free

end Flat

section Tensor

open TensorProduct

/- `star` on `MonoidAlgebra 𝕜 G` needs `G` in the universe of `𝕜 = ℤ`. -/
variable {G H : Type} [CommGroup G] [CommGroup H]

/-- `mapDomain` along a group homomorphism commutes with `star g = g⁻¹`. -/
theorem mapDomainRingHom_star (f : G →* H) (x : MonoidAlgebra ℤ G) :
    mapDomainRingHom ℤ f (star x) = star (mapDomainRingHom ℤ f x) :=
  map_star (groupAlgebraMapStarAlgHom (𝕜 := ℤ) f) x

/-! ### The tensorator `ℤ[G] ⊗ ℤ[H] ≃ ℤ[G × H]` -/

variable (G H) in
/-- `ℤ[G] ⊗ ℤ[H] → ℤ[G × H]`, `g ⊗ h ↦ (g, h)`. -/
def tensorAlgHom : MonoidAlgebra ℤ G ⊗[ℤ] MonoidAlgebra ℤ H →ₐ[ℤ] MonoidAlgebra ℤ (G × H) :=
  Algebra.TensorProduct.lift (mapDomainAlgHom ℤ ℤ (MonoidHom.inl G H))
    (mapDomainAlgHom ℤ ℤ (MonoidHom.inr G H)) fun _ _ => Commute.all _ _

theorem tensorAlgHom_single (g : G) (r : ℤ) (h : H) (s : ℤ) :
    tensorAlgHom G H (single g r ⊗ₜ single h s) = single (g, h) (r * s) := by
  simp [tensorAlgHom, Algebra.TensorProduct.lift_tmul, mapDomain_single, single_mul_single]

theorem tensorAlgHom_eq_tensorEquiv (x : MonoidAlgebra ℤ G ⊗[ℤ] MonoidAlgebra ℤ H) :
    tensorAlgHom G H x = tensorEquiv ℤ x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    induction a using MonoidAlgebra.induction_linear with
    | zero => rw [zero_tmul, map_zero, map_zero]
    | add a a' ha ha' => rw [add_tmul, map_add, ha, ha', map_add]
    | single g r =>
      induction b using MonoidAlgebra.induction_linear with
      | zero => rw [tmul_zero, map_zero, map_zero]
      | add b b' hb hb' => rw [tmul_add, map_add, hb, hb', map_add]
      | single h s => rw [tensorAlgHom_single, tensorEquiv_single_tmul_single]
  | add x y hx hy => rw [map_add, hx, hy, map_add]

theorem tensorAlgHom_star (x : MonoidAlgebra ℤ G ⊗[ℤ] MonoidAlgebra ℤ H) :
    tensorAlgHom G H (star x) = star (tensorAlgHom G H x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.star_tmul]
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a a' ha ha' => rw [star_add, add_tmul, add_tmul, map_add, ha, ha', map_add, star_add]
    | single g r =>
      induction b using MonoidAlgebra.induction_linear with
      | zero => simp
      | add b b' hb hb' =>
        rw [star_add, tmul_add, tmul_add, map_add, hb, hb', map_add, star_add]
      | single h s =>
        rw [star_single, star_single, tensorAlgHom_single, tensorAlgHom_single, star_single,
          Prod.inv_mk, star_trivial, star_trivial, star_trivial]
  | add x y hx hy => rw [star_add, map_add, hx, hy, map_add, star_add]

variable (G H) in
/-- The ring isomorphism `ℤ[G] ⊗ ℤ[H] ≃ ℤ[G × H]`. -/
def tensorRingEquiv : MonoidAlgebra ℤ G ⊗[ℤ] MonoidAlgebra ℤ H ≃+* MonoidAlgebra ℤ (G × H) :=
  RingEquiv.ofBijective (tensorAlgHom G H) (by
    have : ⇑(tensorAlgHom G H) = ⇑(tensorEquiv ℤ (M := G) (N := H)) :=
      funext tensorAlgHom_eq_tensorEquiv
    rw [this]
    exact (tensorEquiv ℤ).bijective)

/-! ### Extensionality for ring homomorphisms out of (tensor products of) group rings -/

theorem ringHom_ext {S : Type*} [Ring S] {φ ψ : MonoidAlgebra ℤ G →+* S}
    (h : ∀ g, φ (single g 1) = ψ (single g 1)) : φ = ψ :=
  MonoidAlgebra.ringHom_ext' (RingHom.ext_int _ _) (MonoidHom.ext h)

theorem tensor_ringHom_ext {A B S : Type*} [CommRing A] [CommRing B] [Ring S]
    {φ ψ : A ⊗[ℤ] B →+* S} (hl : φ.comp Algebra.TensorProduct.includeLeftRingHom =
      ψ.comp Algebra.TensorProduct.includeLeftRingHom)
    (hr : ∀ b, φ (1 ⊗ₜ b) = ψ (1 ⊗ₜ b)) : φ = ψ := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    have hab : a ⊗ₜ[ℤ] b = (a ⊗ₜ 1) * (1 ⊗ₜ b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hab, map_mul, map_mul, hr]
    exact congrArg (· * ψ (1 ⊗ₜ b)) (RingHom.congr_fun hl a)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem tensor_ringHom_ext₂ {S : Type*} [Ring S]
    {φ ψ : MonoidAlgebra ℤ G ⊗[ℤ] MonoidAlgebra ℤ H →+* S}
    (h : ∀ g h, φ (single g 1 ⊗ₜ single h 1) = ψ (single g 1 ⊗ₜ single h 1)) : φ = ψ :=
  tensor_ringHom_ext (ringHom_ext fun g => by simpa [← MonoidAlgebra.one_def] using h g 1)
    (RingHom.congr_fun (ringHom_ext (φ := φ.comp Algebra.TensorProduct.includeRight.toRingHom)
      (ψ := ψ.comp Algebra.TensorProduct.includeRight.toRingHom)
      fun h' => by simpa [← MonoidAlgebra.one_def] using h 1 h'))

theorem tensor_ringHom_ext₃ {K : Type} {S : Type*} [CommGroup K] [Ring S]
    {φ ψ : (MonoidAlgebra ℤ G ⊗[ℤ] MonoidAlgebra ℤ H) ⊗[ℤ] MonoidAlgebra ℤ K →+* S}
    (h : ∀ g h k, φ ((single g 1 ⊗ₜ single h 1) ⊗ₜ single k 1) =
      ψ ((single g 1 ⊗ₜ single h 1) ⊗ₜ single k 1)) : φ = ψ :=
  tensor_ringHom_ext (tensor_ringHom_ext₂ fun g h' => by
      simpa [← MonoidAlgebra.one_def] using h g h' 1)
    (RingHom.congr_fun (ringHom_ext (φ := φ.comp Algebra.TensorProduct.includeRight.toRingHom)
      (ψ := ψ.comp Algebra.TensorProduct.includeRight.toRingHom)
      fun k => by
        have := h 1 1 k
        rwa [← MonoidAlgebra.one_def, ← MonoidAlgebra.one_def,
          ← Algebra.TensorProduct.one_def] at this))

theorem unit_tensor_ringHom_ext {S : Type*} [Ring S] {φ ψ : ℤ ⊗[ℤ] MonoidAlgebra ℤ G →+* S}
    (h : ∀ g, φ (1 ⊗ₜ single g 1) = ψ (1 ⊗ₜ single g 1)) : φ = ψ :=
  tensor_ringHom_ext (RingHom.ext_int _ _)
    (RingHom.congr_fun (ringHom_ext (φ := φ.comp Algebra.TensorProduct.includeRight.toRingHom)
      (ψ := ψ.comp Algebra.TensorProduct.includeRight.toRingHom) h))

theorem tensor_unit_ringHom_ext {S : Type*} [Ring S] {φ ψ : MonoidAlgebra ℤ G ⊗[ℤ] ℤ →+* S}
    (h : ∀ g, φ (single g 1 ⊗ₜ 1) = ψ (single g 1 ⊗ₜ 1)) : φ = ψ :=
  tensor_ringHom_ext (ringHom_ext h) fun n => by
    rw [show (1 : MonoidAlgebra ℤ G) ⊗ₜ[ℤ] n = n • ((1 : MonoidAlgebra ℤ G) ⊗ₜ[ℤ] (1 : ℤ)) by
      rw [← TensorProduct.tmul_smul, smul_eq_mul, mul_one], map_zsmul, map_zsmul,
      ← Algebra.TensorProduct.one_def, map_one, map_one]

end Tensor

end GroupRing

/-! ### The functor -/

namespace CommGrpInclCat

open CategoryTheory MonoidalCategory TensorProduct GroupRing FlatCommStarRingCat

/-- The integral group ring `G ↦ ℤ[G]`, with `star g = g⁻¹`, as a functor from commutative
groups with injective homomorphisms to commutative `*`-rings with flat star ring maps. -/
def groupRingFunctor : CommGrpInclCat.{0} ⥤ FlatCommStarRingCat.{0} where
  obj G := FlatCommStarRingCat.of (MonoidAlgebra ℤ G)
  map f := ⟨mapDomainRingHom ℤ f.1, mapDomainRingHom_star f.1, flat_of_injective f.2⟩
  map_id _ := FlatCommStarRingCat.hom_ext mapDomainRingHom_id
  map_comp f g := FlatCommStarRingCat.hom_ext (mapDomainRingHom_comp g.1 f.1)

private theorem mapDomainRingHom_single {G H : Type} [CommGroup G] [CommGroup H] (f : G →* H)
    (g : G) (r : ℤ) : mapDomainRingHom ℤ f (single g r) = single (f g) r :=
  mapDomain_single

/-- `ℤ ≅ ℤ[1]`. -/
def groupRingεIso : FlatCommStarRingCat.of ℤ ≅ FlatCommStarRingCat.of (MonoidAlgebra ℤ PUnit.{1}) :=
  isoOfStarRingEquiv (uniqueRingEquiv (R := ℤ) PUnit.{1}).symm fun n => by
    rw [uniqueRingEquiv_symm_apply, uniqueRingEquiv_symm_apply, star_single, inv_one,
      star_trivial]

/-- `ℤ[G] ⊗ ℤ[H] ≅ ℤ[G × H]`. -/
def groupRingμIso (G H : Type) [CommGroup G] [CommGroup H] :
    FlatCommStarRingCat.of (MonoidAlgebra ℤ G ⊗[ℤ] MonoidAlgebra ℤ H) ≅
      FlatCommStarRingCat.of (MonoidAlgebra ℤ (G × H)) :=
  isoOfStarRingEquiv (tensorRingEquiv G H) tensorAlgHom_star

/-- The group ring functor is monoidal: `ℤ[G] ⊗ ℤ[H] ≅ ℤ[G × H]` and `ℤ ≅ ℤ[1]`. -/
def groupRingCoreMonoidal : groupRingFunctor.CoreMonoidal where
  εIso := groupRingεIso
  μIso G H := groupRingμIso G H
  μIso_hom_natural_left {X Y} f X' :=
    FlatCommStarRingCat.hom_ext (tensor_ringHom_ext₂ (G := X) (H := X') fun g h => by
      show tensorAlgHom Y X' (mapDomainRingHom ℤ f.1 (single g 1) ⊗ₜ single h 1) =
        mapDomainRingHom ℤ (f.1.prodMap (MonoidHom.id X'))
          (tensorAlgHom X X' (single g 1 ⊗ₜ single h 1))
      rw [mapDomainRingHom_single, tensorAlgHom_single, tensorAlgHom_single,
        mapDomainRingHom_single]
      rfl)
  μIso_hom_natural_right {X Y} X' f :=
    FlatCommStarRingCat.hom_ext (tensor_ringHom_ext₂ (G := X') (H := X) fun g h => by
      show tensorAlgHom X' Y (single g 1 ⊗ₜ mapDomainRingHom ℤ f.1 (single h 1)) =
        mapDomainRingHom ℤ ((MonoidHom.id X').prodMap f.1)
          (tensorAlgHom X' X (single g 1 ⊗ₜ single h 1))
      rw [mapDomainRingHom_single, tensorAlgHom_single, tensorAlgHom_single,
        mapDomainRingHom_single]
      rfl)
  associativity X Y Z := FlatCommStarRingCat.hom_ext (tensor_ringHom_ext₃ (G := X) (H := Y) (K := Z)
    fun g h k => by
      show mapDomainRingHom ℤ (MulEquiv.prodAssoc : (X × Y) × Z ≃* X × (Y × Z)).toMonoidHom
          (tensorAlgHom (X × Y) Z (tensorAlgHom X Y (single g 1 ⊗ₜ single h 1) ⊗ₜ single k 1)) =
        tensorAlgHom X (Y × Z) (single g 1 ⊗ₜ tensorAlgHom Y Z (single h 1 ⊗ₜ single k 1))
      rw [tensorAlgHom_single, tensorAlgHom_single, tensorAlgHom_single, tensorAlgHom_single,
        mapDomainRingHom_single]
      rfl)
  left_unitality X := FlatCommStarRingCat.hom_ext (unit_tensor_ringHom_ext (G := X) fun g => by
    show Algebra.TensorProduct.lid ℤ (MonoidAlgebra ℤ X) (1 ⊗ₜ single g 1) =
      mapDomainRingHom ℤ (unitProdEquiv X).toMonoidHom
        (tensorAlgHom PUnit X ((uniqueRingEquiv (R := ℤ) PUnit.{1}).symm 1 ⊗ₜ single g 1))
    rw [Algebra.TensorProduct.lid_tmul, one_smul, uniqueRingEquiv_symm_apply,
      tensorAlgHom_single, mapDomainRingHom_single, one_mul]
    rfl)
  right_unitality X := FlatCommStarRingCat.hom_ext (tensor_unit_ringHom_ext (G := X) fun g => by
    show Algebra.TensorProduct.rid ℤ ℤ (MonoidAlgebra ℤ X) (single g 1 ⊗ₜ 1) =
      mapDomainRingHom ℤ (prodUnitEquiv X).toMonoidHom
        (tensorAlgHom X PUnit (single g 1 ⊗ₜ (uniqueRingEquiv (R := ℤ) PUnit.{1}).symm 1))
    rw [Algebra.TensorProduct.rid_tmul, one_smul, uniqueRingEquiv_symm_apply,
      tensorAlgHom_single, mapDomainRingHom_single, one_mul]
    rfl)

/-- The group ring functor is monoidal. -/
instance groupRingFunctorMonoidal : groupRingFunctor.Monoidal :=
  groupRingCoreMonoidal.toMonoidal

/-- The group ring functor is braided, hence symmetric monoidal: it sends the swap
`G × H ≃ H × G` to the swap of tensor factors. -/
instance groupRingFunctorBraided : groupRingFunctor.Braided :=
  { groupRingCoreMonoidal.toMonoidal with
    braided X Y := FlatCommStarRingCat.hom_ext (tensor_ringHom_ext₂ (G := X) (H := Y) fun g h => by
      show mapDomainRingHom ℤ (MulEquiv.prodComm : X × Y ≃* Y × X).toMonoidHom
          (tensorAlgHom X Y (single g 1 ⊗ₜ single h 1)) =
        tensorAlgHom Y X (single h 1 ⊗ₜ single g 1)
      rw [tensorAlgHom_single, tensorAlgHom_single, mapDomainRingHom_single]
      rfl) }

/-! ### The actegory: abelian groups act on commutative `*`-rings -/

open MonoidalLeftAction in
/-- Commutative groups with injective homomorphisms act on commutative `*`-rings with flat star
ring maps by `G ⊙ₗ R = ℤ[G] ⊗[ℤ] R`, through the monoidal functor `groupRingFunctor` followed
by the left action of `FlatCommStarRingCat` on itself. -/
instance groupRingAction : MonoidalLeftAction CommGrpInclCat.{0} FlatCommStarRingCat.{0} :=
  actionOfMonoidalFunctorToEndofunctorMop
    (groupRingFunctor ⋙ curriedActionMop FlatCommStarRingCat.{0} FlatCommStarRingCat.{0})

open MonoidalLeftAction

theorem groupRingAction_obj (G : CommGrpInclCat.{0}) (R : FlatCommStarRingCat.{0}) :
    G ⊙ₗ R = groupRingFunctor.obj G ⊗ R :=
  rfl

theorem groupRingAction_homLeft {G H : CommGrpInclCat.{0}} (f : G ⟶ H)
    (R : FlatCommStarRingCat.{0}) : f ⊵ₗ R = groupRingFunctor.map f ▷ R :=
  rfl

theorem groupRingAction_homRight (G : CommGrpInclCat.{0}) {R S : FlatCommStarRingCat.{0}}
    (σ : R ⟶ S) : G ⊴ₗ σ = groupRingFunctor.obj G ◁ σ :=
  rfl

end CommGrpInclCat
