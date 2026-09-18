import KltDP.Geometry.MinimalResolutionExteriorDiscrepancy
import KltDP.Geometry.AmpleQCartierPullbackDegrees
import KltDP.Geometry.CanonicalWeilBirationalRepresentative
import KltDP.Geometry.DelPezzoType

/-!
# Negative canonical degree on every original exterior prime

The same canonical Weil divisor from the klt del Pezzo condition supplies
the ample anticanonical numerator. An exactly compatible canonical Cartier
divisor on the original resolution is constructed internally. Its actual
exceptional discrepancy and the positive anticanonical pullback degree give
strict negativity. The original supplied canonical isomorphism then
transfers the degree to the original supplied Cartier divisor.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsMinimalResolution

open NormalProjectiveSurface SmoothCanonicalExteriorComparison RationalWeilIntersection

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

local instance exteriorCanonicalIntegral (T : NormalProjectiveSurface k) :
    IsIntegral T.toScheme := T.integral

/-- Every original exterior integral prime has negative degree for every
actual canonical Cartier representative on the original minimal resolution
of the actual klt del Pezzo surface. -/
theorem canonical_degree_neg_of_kltDelPezzo
    (hmin : IsMinimalResolution S X π) (hDP : IsKltDelPezzo X)
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (C : S.PrimeCurve) (hC : ¬ IsExceptionalCurve π C) :
    C.intersectionNumber K < 0 := by
  letI : IsProper π := hmin.toIsResolution.isProper
  letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hmin.birational
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  obtain ⟨KX, hKX, n, hn, A, hA, hample⟩ := (isLogDelPezzoPair_zero_iff X).mp hDP
  obtain ⟨KS, ⟨eKS⟩, hpush⟩ :=
    IsCanonicalWeilDivisor.exists_compatible_canonical_cartier
      S X π hmin.over_base hbir KX hKX.1
  have hcanonical := hmin.canonical_degree_le_pullback_of_klt KS eKS KX hKX hpush C hC
  have hanti : X.QCartier (-rationalizeWeilDivisor X KX) :=
    X.rationalCartierSubmodule.neg_mem hKX.2.1
  have hpositive := degreeLinearMap_pullback_pos_of_ample_numerator
    hmin.regular π (-rationalizeWeilDivisor X KX) hanti n hn A hA hample C hC
  have hnegative : degreeLinearMap S hmin.regular C
      (QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hKX.2.1) < 0 := by
    change 0 < degreeLinearMap S hmin.regular C
      (QCartierPullback.pullbackToWeil π
        (-⟨rationalizeWeilDivisor X KX, hKX.2.1⟩)) at hpositive
    rw [map_neg, map_neg] at hpositive
    exact neg_pos.mp hpositive
  have hKS : C.intersectionNumber KS < 0 := by
    exact_mod_cast lt_of_le_of_lt hcanonical hnegative
  have heq : C.intersectionNumber K = C.intersectionNumber KS :=
    C.restrictionDegree_eq_of_iso (eK ≪≫ eKS.symm)
  rw [heq]
  exact hKS

/-- The degree is an original integer, so strict negativity gives the
uniform canonical bound at most minus one on every exterior prime. -/
theorem canonical_degree_le_neg_one_of_kltDelPezzo
    (hmin : IsMinimalResolution S X π) (hDP : IsKltDelPezzo X)
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (C : S.PrimeCurve) (hC : ¬ IsExceptionalCurve π C) :
    C.intersectionNumber K ≤ -1 := by
  have h := hmin.canonical_degree_neg_of_kltDelPezzo hDP K eK C hC
  omega

end KltDP.Geometry.IsMinimalResolution

#check @KltDP.Geometry.IsMinimalResolution.canonical_degree_neg_of_kltDelPezzo
#check @KltDP.Geometry.IsMinimalResolution.canonical_degree_le_neg_one_of_kltDelPezzo
#print axioms KltDP.Geometry.IsMinimalResolution.canonical_degree_neg_of_kltDelPezzo
#print axioms KltDP.Geometry.IsMinimalResolution.canonical_degree_le_neg_one_of_kltDelPezzo
