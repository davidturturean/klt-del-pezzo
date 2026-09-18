import KltDP.Geometry.NonpositiveExceptionalImages
import KltDP.Geometry.ActualResolutionSingularComponentBound

/-!
# Exact singular-point count from original nonpositive discrepancies

The actual resolution bounds singular points by its exceptional connected
components. The original canonical difference identifies every contracted
image as singular when its coefficients are nonpositive, giving equality.
Proving this coefficient condition from general minimality remains separate.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open NormalProjectiveSurface NormalModelCanonical

/-- Nonpositive coefficients of the original compatible canonical difference
make the number of actual singular points equal to the number of actual
exceptional connected components. Finiteness is proved before counting. -/
theorem IsResolution.singularPoints_card_eq_exceptional_components_of_nonpositive
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {π : S.toScheme ⟶ X.toScheme} (hres : IsResolution S X π)
    (hconnected : ∀ y : X.toScheme, IsConnected (π.base ⁻¹' {y}))
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (KX : X.WeilDivisor) (hcanonical : IsCanonicalWeilDivisor X KX)
    (hK : X.QCartier (rationalizeWeilDivisor X KX))
    (hpush : letI : IsProper π := hres.isProper
      BirationalWeilPushforward.pushforward π
      ((isBirational_iff_isBirationalScheme π).mp hres.birational)
      (S.cartierToWeilHom KS) = KX) :
    letI : GenericPointPreserving π :=
      ⟨((isBirational_iff_isBirationalScheme π).mp hres.birational).map_genericPoint⟩
    (∀ C : S.PrimeCurve, IsExceptionalCurve π C →
      (S.rationalCartierToWeilHom KS -
        QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hK) C ≤ 0) →
      Finite (ConnectedComponents (exceptionalLocus π)) ∧
        X.singularPoints.card = Nat.card (ConnectedComponents (exceptionalLocus π)) := by
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hres.birational
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI : IsProper π := hres.isProper
  letI : IsIso π.c := ProperBirationalStructureSheaf.resolution_c_isIso π hres
  intro hnonpositive
  obtain ⟨hfinite, hle⟩ := hres.singularPoints_card_le_exceptional_components hconnected
  refine ⟨hfinite, le_antisymm hle ?_⟩
  have hsub := NonpositiveExceptionalImages.imagePoints_subset_singularPoints
    S X π hbir hres.over_base KS eKS KX hcanonical hK hpush hnonpositive
  rw [ActualExceptionalLocus.exceptionalLocus_eq_primeSupport
    π hbir hres.over_base hconnected,
    ActualExceptionalLocus.component_count π hbir hres.over_base hconnected]
  calc
    (ActualExceptionalLocus.imagePoints π).ncard ≤
        (X.singularPoints : Set X.Point).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet X.singularPoints)
    _ = X.singularPoints.card := Set.ncard_coe_Finset X.singularPoints

end KltDP.Geometry

#print axioms KltDP.Geometry.IsResolution.singularPoints_card_eq_exceptional_components_of_nonpositive
