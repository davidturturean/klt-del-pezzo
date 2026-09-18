import KltDP.Geometry.RationalCurveClosedImage
import KltDP.Geometry.RationalTreePicardComponentPartition

/-!
# Prime-curve images of the original reduced rational components

Every component uses its original reduced component scheme and original
inclusion. The source comparison is the proved closed-image isomorphism.
Composing it with any actual map of the whole curve produces maps from
the original prime-curve schemes, retaining the original projections.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.RationalComponentPrimeCurves

open NormalProjectiveSurface RationalTreePicard PrimeCurveOfClosedImmersion

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)
    {C : Scheme.{u}} [NoetherianSpace C]
    (f : C ⟶ S.toScheme) [IsClosedImmersion f]
    (eC : ∀ D : ↥(irreducibleComponents C), componentUnionScheme C {D} ≅ projectiveSpace k 1)

/-- The original component's actual prime-curve image. -/
def curve (D : ↥(irreducibleComponents C)) : S.PrimeCurve :=
  primeCurveOfIsoProjectiveLine S (componentUnionInclusion C {D} ≫ f) (eC D)

/-- The actual prime-curve scheme is the original reduced component scheme. -/
def sourceIso (D : ↥(irreducibleComponents C)) :
    (curve S f eC D).toScheme ≅ componentUnionScheme C {D} :=
  RationalCurveClosedImage.sourceIso S (componentUnionInclusion C {D} ≫ f) (eC D)

@[reassoc]
theorem sourceIso_hom_toBase (D : ↥(irreducibleComponents C)) :
    (sourceIso S f eC D).hom ≫ (componentUnionInclusion C {D} ≫ f) =
      (curve S f eC D).inclusion :=
  RationalCurveClosedImage.sourceIso_hom_map S (componentUnionInclusion C {D} ≫ f) (eC D)

/-- An unchanged whole-curve map expressed on the original prime-curve scheme. -/
def liftThrough {Z : Scheme.{u}} (j : C ⟶ Z) (D : ↥(irreducibleComponents C)) :
    (curve S f eC D).toScheme ⟶ Z :=
  (sourceIso S f eC D).hom ≫ (componentUnionInclusion C {D} ≫ j)

instance liftThrough_isClosedImmersion {Z : Scheme.{u}} (j : C ⟶ Z)
    [IsClosedImmersion j] (D : ↥(irreducibleComponents C)) :
    IsClosedImmersion (liftThrough S f eC j D) := by
  dsimp only [liftThrough]
  infer_instance

@[reassoc]
theorem liftThrough_projection {Z : Scheme.{u}} (j : C ⟶ Z) (π : Z ⟶ S.toScheme)
    (hj : j ≫ π = f) (D : ↥(irreducibleComponents C)) :
    liftThrough S f eC j D ≫ π = (curve S f eC D).inclusion := by
  rw [liftThrough, Category.assoc, Category.assoc, hj]
  exact sourceIso_hom_toBase S f eC D

/-- The transported component map remains inside the original whole-curve image. -/
theorem range_liftThrough_subset {Z : Scheme.{u}} (j : C ⟶ Z)
    (D : ↥(irreducibleComponents C)) :
    Set.range (liftThrough S f eC j D).base ⊆ Set.range j.base := by
  rintro x ⟨y, rfl⟩
  exact ⟨(componentUnionInclusion C {D}).base ((sourceIso S f eC D).hom.base y), rfl⟩

/-- Source transport preserves the actual component prime curve in the target surface. -/
theorem closedImage_liftThrough (T : NormalProjectiveSurface k) (j : C ⟶ T.toScheme)
    [IsClosedImmersion j] (D : ↥(irreducibleComponents C)) :
    (curve S f eC D).closedImage (T := T) (liftThrough S f eC j D) = curve T j eC D :=
  RationalCurveClosedImage.closedImage_precomp_iso T (componentUnionInclusion C {D} ≫ j)
    (eC D) (curve S f eC D) (sourceIso S f eC D)

end KltDP.Geometry.RationalComponentPrimeCurves

#print axioms KltDP.Geometry.RationalComponentPrimeCurves.liftThrough_projection
#print axioms KltDP.Geometry.RationalComponentPrimeCurves.closedImage_liftThrough
