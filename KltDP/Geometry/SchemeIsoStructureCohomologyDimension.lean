import KltDP.Geometry.PointBlowupCohomologyConditional

/-!
# Original structure-sheaf dimensions across an isomorphism over the field

The original base-field linear equivalence gives equality of finranks
before the original field triangle is rewritten. Keeping that dimension
comparison separate avoids unfolding the base functor inside an indexed
point-blowup induction. This lemma has no literature hypothesis.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ModuleCohomology

/-- The native dimension comparison retains both original structure maps
and uses their actual commuting triangle. -/
theorem schemeIsoStructure_cohomologyDimension_eq
    {k : Type u} [Field k] {X Y : Scheme.{u}} (e : X ≅ Y)
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (h : e.hom ≫ g = f) (n : ℕ) :
    cohomologyDimension f (_root_.SheafOfModules.unit X.ringCatSheaf) n =
      cohomologyDimension g (_root_.SheafOfModules.unit Y.ringCatSheaf) n := by
  have he : cohomologyDimension (e.hom ≫ g)
      (_root_.SheafOfModules.unit X.ringCatSheaf) n =
      cohomologyDimension g (_root_.SheafOfModules.unit Y.ringCatSheaf) n :=
    (schemeIsoStructureHLinearEquiv e g n).finrank_eq.symm
  rwa [h] at he

end KltDP.Geometry.ModuleCohomology

#print axioms KltDP.Geometry.ModuleCohomology.schemeIsoStructure_cohomologyDimension_eq
