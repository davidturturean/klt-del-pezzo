import KltDP.Geometry.ActualExceptionalComponents
import KltDP.Geometry.ProperBirationalStructureSheaf

/-!
# Bounding actual singular points by actual exceptional connected components

The original resolution supplies its properness, birationality, regular
source, and structure-sheaf isomorphism. The exceptional locus is the actual
non-isomorphism locus, rather than an independently supplied curve list.
Connectedness of its original point fibers remains an explicit hypothesis.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

/-- A resolution with connected original fibers has finitely many actual
exceptional connected components, and these bound the distinct singular points.
The structure-sheaf isomorphism and finite counting sets are derived internally. -/
theorem IsResolution.singularPoints_card_le_exceptional_components
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    {π : S.toScheme ⟶ X.toScheme} (hπ : IsResolution S X π)
    (hconnected : ∀ y : X.toScheme, IsConnected (π.base ⁻¹' {y})) :
    Finite (ConnectedComponents (exceptionalLocus π)) ∧
      X.singularPoints.card ≤ Nat.card (ConnectedComponents (exceptionalLocus π)) := by
  letI : IsProper π := hπ.isProper
  letI : IsIso π.c := ProperBirationalStructureSheaf.resolution_c_isIso π hπ
  have hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hπ.birational
  rw [ActualExceptionalLocus.exceptionalLocus_eq_primeSupport
    π hbir hπ.over_base hconnected]
  exact ⟨ActualExceptionalLocus.finite_connectedComponents
      π hbir hπ.over_base hconnected,
    ActualExceptionalLocus.singularPoints_card_le_components
      π hbir hπ.over_base hconnected hπ.regular⟩

end KltDP.Geometry

#print axioms KltDP.Geometry.IsResolution.singularPoints_card_le_exceptional_components
