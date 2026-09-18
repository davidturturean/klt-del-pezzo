import KltDP.Geometry.AffineModuleTildePullbackUnit
import KltDP.Geometry.PrincipalKernelSheaf
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# The original equation frame of a regular principal ideal tilde

The pinned singleton-span map and regular cancellation identify the ring
with the actual principal ideal. The original tilde functor carries this
equivalence to the actual ideal sheaf. Its inclusion is multiplication by
the same original defining equation, under the original unit comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffinePrincipalIdealTildeFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {A : Type u} [CommRing A] (J : Ideal A) (d : J)

abbrev idealModule : ModuleCat.{u} A := ModuleCat.of A J

/-- The pinned singleton-span map retains the original generator as an element of the ideal. -/
def equationMap : A →ₗ[A] J := LinearMap.toSpanSingleton A J d

theorem equationMap_val (r : A) : (equationMap J d r : A) = r * (d : A) := rfl

theorem equationMap_injective (hregular : (d : A) ∈ nonZeroDivisors A) :
    Function.Injective (equationMap J d) := by
  intro r s h
  exact (mul_cancel_right_mem_nonZeroDivisors hregular).mp (congrArg Subtype.val h)

theorem equationMap_surjective (hJ : Ideal.span {(d : A)} = J) :
    Function.Surjective (equationMap J d) := by
  intro x
  have hx : (x : A) ∈ Ideal.span {(d : A)} := hJ.symm ▸ x.property
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hx
  exact ⟨r, Subtype.ext hr⟩

/-- The actual regular equation gives an equivalence onto the original ideal. -/
def equationEquiv (hJ : Ideal.span {(d : A)} = J)
    (hregular : (d : A) ∈ nonZeroDivisors A) : A ≃ₗ[A] J :=
  LinearEquiv.ofBijective (equationMap J d)
    ⟨equationMap_injective J d hregular, equationMap_surjective J d hJ⟩

/-- The original ideal inclusion, followed by the original tilde-unit comparison. -/
def inclusion : (idealModule J).tilde ⟶
    _root_.SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf :=
  AffineModuleTilde.map (ModuleCat.ofHom J.subtype) ≫ (AffineModuleTilde.unitIso A).hom

variable (hJ : Ideal.span {(d : A)} = J) (hregular : (d : A) ∈ nonZeroDivisors A)

/-- Its original affine tilde isomorphism, still normalized by the defining equation. -/
def frameIso :
    _root_.SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ≅
      (idealModule J).tilde :=
  (AffineModuleTilde.unitIso A).symm ≪≫
    AffineModuleTilde.linearEquivIso
      (M := ModuleCat.of A A) (N := idealModule J) (equationEquiv J d hJ hregular)

private theorem affineHomEquiv_apply (M : ModuleCat.{u} A)
    (N : (Spec (CommRingCat.of A)).Modules) (a : M.tilde ⟶ N) (m : M) :
    (AffineModuleTilde.adjunction A).homEquiv M N a m =
      a.val.app (op ⊤) (ModuleCat.Tilde.toOpen M ⊤ m) := by
  change (AffineModuleTilde.globalSectionsFunctor A).map a
    ((AffineModuleTilde.unitNatIso A).hom.app M m) = _
  simpa only [AffineModuleTilde.unitNatIso_hom_app] using
    AffineModuleTilde.globalSectionsFunctor_map_apply a (ModuleCat.Tilde.toOpen M ⊤ m)

/-- Before cancelling the original unit, the whole tilde map multiplies by the original equation. -/
theorem tilde_equation_factor :
    (AffineModuleTilde.linearEquivIso
      (M := ModuleCat.of A A) (N := idealModule J) (equationEquiv J d hJ hregular)).hom ≫
        inclusion J =
      (AffineModuleTilde.unitIso A).hom ≫
        schemeScalarEnd (Y := Spec (CommRingCat.of A))
        (StructureSheaf.toOpen A ⊤ (d : A)) := by
  apply ((AffineModuleTilde.adjunction A).homEquiv (ModuleCat.of A A) _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  rw [affineHomEquiv_apply, affineHomEquiv_apply]
  change (AffineModuleTilde.unitIso A).hom.val.app (op ⊤)
      ((AffineModuleTilde.map (ModuleCat.ofHom J.subtype)).val.app (op ⊤)
        ((AffineModuleTilde.map (equationEquiv J d hJ hregular).toModuleIso.hom).val.app
          (op ⊤) (ModuleCat.Tilde.toOpen (ModuleCat.of A A) ⊤ r))) =
    (schemeScalarEnd (Y := Spec (CommRingCat.of A))
        (StructureSheaf.toOpen A ⊤ (d : A))).val.app (op ⊤)
      ((AffineModuleTilde.unitIso A).hom.val.app (op ⊤)
        (ModuleCat.Tilde.toOpen (ModuleCat.of A A) ⊤ r))
  rw [AffineModuleTilde.map_app_toOpen, AffineModuleTilde.map_app_toOpen,
    AffineModuleTildePullbackUnit.unitIso_hom_toOpen,
    AffineModuleTildePullbackUnit.unitIso_hom_toOpen, schemeScalarEnd_appTop]
  change StructureSheaf.toOpen A ⊤ (r * (d : A)) =
    StructureSheaf.toOpen A ⊤ r * StructureSheaf.toOpen A ⊤ (d : A)
  exact (StructureSheaf.toOpen A ⊤).hom.map_mul r (d : A)

/-- The actual ideal inclusion preserves the original equation under this frame. -/
theorem frameIso_inclusion :
    (frameIso J d hJ hregular).hom ≫ inclusion J =
      schemeScalarEnd (Y := Spec (CommRingCat.of A))
        (StructureSheaf.toOpen A ⊤ (d : A)) := by
  change ((AffineModuleTilde.unitIso A).inv ≫
    (AffineModuleTilde.linearEquivIso
      (M := ModuleCat.of A A) (N := idealModule J) (equationEquiv J d hJ hregular)).hom) ≫
        inclusion J = _
  rw [Category.assoc, tilde_equation_factor, Iso.inv_hom_id_assoc]

end KltDP.Geometry.AffinePrincipalIdealTildeFrame
