import KltDP.Geometry.PointBlowupCenterFiber
import KltDP.Geometry.ReducedClosedImmersionRangeIso

/-!
# The original reduced closed center is independent of its affine neighborhood

Both center sources are the actual quotients by the selected maximal ideals.
Their spectra are reduced, and their original closed immersions have the
same singleton range. The isomorphism consequently preserves the whole
center morphisms. No equality of nonreduced schemes is inferred from support.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PointBlowupGluing

variable {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}
    (jR : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion jR]
    (jS : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion jS]
    (qR : PrimeSpectrum R) [qR.asIdeal.IsMaximal]
    (qS : PrimeSpectrum S) [qS.asIdeal.IsMaximal]
    (hR : IsClosed ({jR.base qR} : Set X))
    (hS : IsClosed ({jS.base qS} : Set X))
    (hpoint : jR.base qR = jS.base qS)

include hpoint in
private theorem closedCenter_range_eq :
    Set.range (closedCenterInclusion jR qR).base =
      Set.range (closedCenterInclusion jS qS).base := by
  rw [range_closedCenterInclusion, range_closedCenterInclusion, hpoint]

/-- The actual quotient centers are isomorphic over the original ambient scheme. -/
def closedCenterIso : Spec (CommRingCat.of (R ⧸ qR.asIdeal)) ≅
    Spec (CommRingCat.of (S ⧸ qS.asIdeal)) := by
  letI : Field (R ⧸ qR.asIdeal) := Ideal.Quotient.field _
  letI : Field (S ⧸ qS.asIdeal) := Ideal.Quotient.field _
  letI := closedCenterInclusion_isClosedImmersion jR qR hR
  letI := closedCenterInclusion_isClosedImmersion jS qS hS
  exact ReducedClosedImmersionRangeIso.iso _ _ (closedCenter_range_eq jR jS qR qS hpoint)

theorem closedCenterIso_hom_comp :
    (closedCenterIso jR jS qR qS hR hS hpoint).hom ≫ closedCenterInclusion jS qS =
      closedCenterInclusion jR qR := by
  letI : Field (R ⧸ qR.asIdeal) := Ideal.Quotient.field _
  letI : Field (S ⧸ qS.asIdeal) := Ideal.Quotient.field _
  letI := closedCenterInclusion_isClosedImmersion jR qR hR
  letI := closedCenterInclusion_isClosedImmersion jS qS hS
  exact ReducedClosedImmersionRangeIso.iso_hom_comp _ _
    (closedCenter_range_eq jR jS qR qS hpoint)

end KltDP.Geometry.PointBlowupGluing
