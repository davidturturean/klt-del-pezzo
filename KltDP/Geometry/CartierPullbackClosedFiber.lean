import KltDP.Geometry.CartierPullbackKernelFactorization
import KltDP.Geometry.GluedIdealSheafLift
import KltDP.Geometry.SchematicImageToImageIso

/-!
The original pulled Cartier zero scheme is the actual inverse image of
an original reduced closed subscheme having the target Cartier ideal.
In particular this applies to an actual rational point, retaining the
original point map and the original morphism being pulled back.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.CartierPullbackClosedFiber

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsReduced Z]
  (π : X ⟶ Y) [GenericPointPreserving π] [QuasiCompact π]
  (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D)
  (i : Z ⟶ Y) [IsClosedImmersion i]
  (hI : effectiveCartierIdealDataOfRegularEquations Y D hD = i.ker)

include hI

/-- The actual pulled ideal is killed by the actual fiber inclusion. -/
theorem ideal_le_fiber_ker :
    pullbackIdealData π D hD ≤ (pullback.fst π i).ker := by
  apply (CartierPullbackKernelFactorization.le_ker_iff π D hD (pullback.fst π i)).mpr
  rw [hI, pullback.condition]
  exact Scheme.Hom.le_ker_comp (pullback.snd π i) i

/-- The pulled zero scheme maps to the original reduced center. -/
def toCenter : (pullbackIdealData π D hD).glueData.glued ⟶ Z :=
  GluedIdealSheafLift.liftGlued i.ker ((pullbackIdealData π D hD).gluedTo ≫ π)
    (by
      rw [← hI]
      apply (CartierPullbackKernelFactorization.le_ker_iff π D hD
        (pullbackIdealData π D hD).gluedTo).mp
      rw [Scheme.IdealSheafData.ker_gluedTo]) ≫
    (SchematicImageToImageIso.toImageIso i).inv

@[reassoc] theorem toCenter_comp :
    toCenter π D hD i hI ≫ i = (pullbackIdealData π D hD).gluedTo ≫ π := by
  rw [toCenter, Category.assoc, SchematicImageToImageIso.toImageIso_inv_comp]
  exact GluedIdealSheafLift.liftGlued_gluedTo _ _ _

/-- The actual factorization into the original categorical fiber. -/
def toFiber : (pullbackIdealData π D hD).glueData.glued ⟶ pullback π i :=
  pullback.lift (pullbackIdealData π D hD).gluedTo (toCenter π D hD i hI)
    (toCenter_comp π D hD i hI).symm

@[simp] theorem toFiber_fst :
    toFiber π D hD i hI ≫ pullback.fst π i = (pullbackIdealData π D hD).gluedTo :=
  pullback.lift_fst _ _ _

/-- The actual fiber factors back through the original Cartier zero scheme. -/
def fromFiber : pullback π i ⟶ (pullbackIdealData π D hD).glueData.glued :=
  GluedIdealSheafLift.liftGlued (pullbackIdealData π D hD) (pullback.fst π i)
    (ideal_le_fiber_ker π D hD i hI)

@[simp] theorem fromFiber_gluedTo :
    fromFiber π D hD i hI ≫ (pullbackIdealData π D hD).gluedTo = pullback.fst π i :=
  GluedIdealSheafLift.liftGlued_gluedTo _ _ _

/-- The original zero scheme and original point fiber are canonically
isomorphic over the original source scheme. -/
def iso : (pullbackIdealData π D hD).glueData.glued ≅ pullback π i where
  hom := toFiber π D hD i hI
  inv := fromFiber π D hD i hI
  hom_inv_id := by
    rw [← cancel_mono (pullbackIdealData π D hD).gluedTo]
    rw [Category.assoc, fromFiber_gluedTo, toFiber_fst, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (pullback.fst π i)]
    rw [Category.assoc, toFiber_fst, fromFiber_gluedTo, Category.id_comp]

@[simp] theorem iso_hom_fst :
    (iso π D hD i hI).hom ≫ pullback.fst π i = (pullbackIdealData π D hD).gluedTo :=
  toFiber_fst π D hD i hI

/-- Equality of the actual ideal sheaves, including all nilpotents in the
fiber. Reducedness was required only of the original center. -/
theorem ideal_eq_fiber_ker :
    pullbackIdealData π D hD = (pullback.fst π i).ker := by
  apply (ideal_le_fiber_ker π D hD i hI).antisymm
  have h := Scheme.Hom.le_ker_comp (toFiber π D hD i hI) (pullback.fst π i)
  rwa [toFiber_fst, Scheme.IdealSheafData.ker_gluedTo] at h

#check KltDP.Geometry.CartierPullbackClosedFiber.iso
#check KltDP.Geometry.CartierPullbackClosedFiber.ideal_eq_fiber_ker
#print axioms KltDP.Geometry.CartierPullbackClosedFiber.iso
#print axioms KltDP.Geometry.CartierPullbackClosedFiber.ideal_eq_fiber_ker

end KltDP.Geometry.CartierPullbackClosedFiber
