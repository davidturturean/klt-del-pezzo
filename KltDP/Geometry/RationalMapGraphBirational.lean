import KltDP.Geometry.RationalMapGraphClosure
import KltDP.Geometry.ProperBirationalCodimensionOne

/-!
# Birationality and valuation-point isomorphisms of the original graph projection

The constructed graph projection is birational because it is already an
isomorphism over the nonempty original domain. The existing proper-birational
valuation theorem therefore applies to this actual map. No finite bad locus
or regularity hypothesis on every stalk is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.RationalMapGraphClosure

attribute [local instance] integralSchemeStalk_isDomain

variable {T V X : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
  (t : T ⟶ X) (v : V ⟶ X) [IsProper v]
  (φ : T.PartialMap V) (hφ : φ.hom ≫ v = φ.domain.ι ≫ t)

/-- The actual proper graph projection is birational on the original schemes. -/
theorem projection_isBirationalScheme : IsBirationalScheme (projection t v φ hφ) := by
  letI : Nonempty φ.domain.toScheme := by
    obtain ⟨x, hx⟩ := φ.dense_domain.nonempty
    exact ⟨⟨x, hx⟩⟩
  letI := projection_restrict_isIso t v φ hφ
  exact isBirationalScheme_of_isIso_restrict (projection t v φ hφ) φ.domain

/-- This specific graph modification is an isomorphism near each original
point whose original stalk is a valuation ring. -/
theorem projection_iso_near_valuation_point (x : T) [ValuationRing (T.presheaf.stalk x)] :
    ∃ U : T.Opens, x ∈ U ∧ IsIso (projection t v φ hφ ∣_ U) :=
  ProperBirationalCodimensionOne.exists_isomorphism_open_at_valuation_stalk
    (projection t v φ hφ) (projection_isBirationalScheme t v φ hφ) x

end KltDP.Geometry.RationalMapGraphClosure
