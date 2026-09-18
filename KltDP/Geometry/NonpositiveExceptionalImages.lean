import KltDP.Geometry.ActualExceptionalComponents
import KltDP.Geometry.RegularTargetCanonicalDiscrepancy

/-!
# Nonpositive original exceptional discrepancies force singular images

This general adapter connects the original canonical-divisor comparison
with the actual exceptional-image counting set. The coefficient inequality
is explicit; deriving it for a general minimal resolution remains separate.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.NonpositiveExceptionalImages

open NormalProjectiveSurface NormalModelCanonical

/-- Every actual exceptional image is singular when the original compatible
canonical difference has nonpositive coefficients on contracted prime curves. -/
theorem imagePoints_subset_singularPoints
    {k : Type u} [Field k] [IsAlgClosed k]
    (S X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (KX : X.WeilDivisor) (hcanonical : IsCanonicalWeilDivisor X KX)
    (hK : X.QCartier (rationalizeWeilDivisor X KX))
    (hpush : BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom KS) = KX) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    (∀ C : S.PrimeCurve, IsExceptionalCurve π C →
      (S.rationalCartierToWeilHom KS -
        QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hK) C ≤ 0) →
      ActualExceptionalLocus.imagePoints π ⊆ (X.singularPoints : Set X.Point) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  intro hnonpositive y hy
  have hy' : y ∈ ActualExceptionalLocus.imagePoints π := hy
  obtain ⟨x, hx, hxy⟩ := hy
  obtain ⟨C, hC, hxC⟩ := (ActualExceptionalLocus.mem_primeSupport π x).mp hx
  obtain ⟨z, hCz⟩ := hC
  have hxz : π.base x = z := by
    have h := Set.mem_image_of_mem π.base hxC
    rwa [hCz] at h
  have hgenz : π.base C.genericPoint = z := by
    have h := Set.mem_image_of_mem π.base C.genericPoint_mem
    rwa [hCz] at h
  have hCy : π.base C.genericPoint = y := hgenz.trans (hxz.symm.trans hxy)
  have hclosed : IsClosed ({π.base C.genericPoint} : Set X.toScheme) := by
    rw [hCy]
    exact ActualExceptionalLocus.imagePoint_isClosed π ⟨y, hy'⟩
  apply (X.mem_singularPoints y).mpr
  intro hregular
  have hregularC : RegularPoint X.toScheme (π.base C.genericPoint) := by
    rwa [hCy]
  have hpositive :=
    RegularTargetCanonicalDiscrepancy.coefficient_pos_of_regular_closed_image
      S X π hbir hπ KS eKS KX hcanonical hK hpush C hclosed hregularC
  exact (not_lt_of_ge (hnonpositive C ⟨z, hCz⟩)) hpositive

end KltDP.Geometry.NonpositiveExceptionalImages

#print axioms KltDP.Geometry.NonpositiveExceptionalImages.imagePoints_subset_singularPoints
