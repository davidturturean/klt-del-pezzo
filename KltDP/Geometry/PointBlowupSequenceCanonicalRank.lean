import KltDP.Geometry.RegularResolutionNoetherSum
import KltDP.Geometry.SurfacePointBlowupSequenceBirational

/-!
# Canonical-square change along the same original blowdown sequence

The original sequence is an actual resolution. Its proved Noether invariant
and an exact rank drop determine the square increment without choosing a
different blowdown or assuming that every exceptional curve was counted.
-/
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry
open SmoothCanonicalExteriorComparison

/-- The square increment uses the exact original rank difference. -/
theorem IsPointBlowupSequence.canonical_square_eq_add_of_picardRank
    {k : Type u} [Field k] [IsAlgClosed k]
    {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
    (hb : IsPointBlowupSequence S T b)
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ x : T.Point, RegularPoint T.toScheme x)
    (KS : CartierDivisor S.toScheme) (KT : CartierDivisor T.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (eKT : cartierDivisorModule T.toScheme KT ≅
      relativeDifferentialExterior T.structureMorphism 2)
    (n : ℕ) (hrank : S.picardRank = T.picardRank + n) :
    T.intersectionPairing hT KT KT = S.intersectionPairing hS KS KS + (n : ℤ) := by
  let hres : IsResolution S T b :=
    ⟨hb.over_base, hS, (isBirational_iff_isBirationalScheme b).mpr hb.isBirationalScheme⟩
  have hsum := hres.canonical_square_add_picardRank_eq hT KS KT eKS eKT
  have hrankZ : (S.picardRank : ℤ) = (T.picardRank : ℤ) + (n : ℤ) := by
    exact_mod_cast hrank
  change S.intersectionPairing hS KS KS + (S.picardRank : ℤ) =
    T.intersectionPairing hT KT KT + (T.picardRank : ℤ) at hsum
  omega

end KltDP.Geometry
#print axioms KltDP.Geometry.IsPointBlowupSequence.canonical_square_eq_add_of_picardRank
