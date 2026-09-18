import KltDP.Geometry.ActualExceptionalNumericalComplement
import KltDP.Geometry.AmpleQCartierPullbackDegrees
import KltDP.Geometry.KltResolutionPicardRank
import KltDP.Geometry.DelPezzoType
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The original exceptional classes and one exterior prime span numerically

An actual ample anticanonical numerator pulls back with degree zero on
every original exceptional prime and positive degree on the exterior prime.
The exterior class is therefore outside the exceptional span. Existing
exceptional independence and the original klt resolution rank equality
make the enlarged family span the entire original numerical space.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open NormalProjectiveSurface DisjointNegativeCurvesRank

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}

/-- An exterior prime cannot lie in the original exceptional numerical span:
the actual ample pullback separates it from every exceptional class. -/
theorem exterior_curveClass_not_mem_exceptionalSpan
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] [GenericPointPreserving π]
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (A : CartierDivisor X.toScheme)
    (hA : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A))
    (P : S.PrimeCurve) (hP : ¬ IsExceptionalCurve π P) :
    curveClass S hS P ∉ ActualExceptionalNumerical.exceptionalSpan π hS := by
  let H := DominantCartierPullback.pullbackHom π A
  have hnull : ∀ C : ActualExceptionalIncidence.Vertices π,
      C.val.intersectionNumber H = 0 := fun C =>
    C.property.intersectionNumber_pullback_eq_zero π hπ C.val A
  intro hmem
  have hz := NullCurveNumericalSpan.span_le_ker S hS H
    (fun C : ActualExceptionalIncidence.Vertices π => C.val) hnull hmem
  change S.numericalIntersectionBilinForm hS
    (NefNullCurveNegativeSquare.cartierClass S H) (curveClass S hS P) = 0 at hz
  rw [NullCurveNumericalSpan.cartierClass_curveClass] at hz
  have hpositive : (0 : ℚ) < (P.intersectionNumber H : ℚ) := by
    exact_mod_cast AmplePullbackCurvePositive.intersectionNumber_pos π A hA P hP
  exact (ne_of_gt hpositive) hz

/-- All original exceptional classes together with any one original exterior
prime span the full numerical space of the rank-one klt del Pezzo resolution. -/
theorem IsMinimalResolution.exceptional_exterior_numerical_span_eq_top
    {π : S.toScheme ⟶ X.toScheme} (hmin : IsMinimalResolution S X π)
    (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1)
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : S.PrimeCurve) (hP : ¬ IsExceptionalCurve π P) :
    Submodule.span ℚ (insert (curveClass S hmin.regular P)
      (Set.range (fun C : ActualExceptionalIncidence.Vertices π =>
        curveClass S hmin.regular C.val))) = ⊤ := by
  classical
  letI : IsProper π := hmin.toIsResolution.isProper
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hmin.birational
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI : Fintype (ActualExceptionalIncidence.Vertices π) :=
    (exceptionalCurves_finite_of_proper_birational π hbir).fintype
  letI : FiniteDimensional ℚ S.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalSpaceFiniteDimensional S hmin.regular
  obtain ⟨KX, hKX, n, hn, A, hA, hample⟩ :=
    (isLogDelPezzoPair_zero_iff X).mp hDP
  have hnot := exterior_curveClass_not_mem_exceptionalSpan
    π hmin.over_base hmin.regular A hample P hP
  have hli := ActualExceptionalNegativeDefinite.linearIndependent
    π hmin.over_base hbir hmin.regular
  have hext := hli.option hnot
  have hcard : Fintype.card (Option (ActualExceptionalIncidence.Vertices π)) =
      Module.finrank ℚ S.NumericalClassGroup := by
    change Fintype.card (Option (ActualExceptionalIncidence.Vertices π)) = S.picardRank
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card]
    have h := hmin.picardRank_eq_of_klt ⟨KX, hKX⟩ p hp
    rw [hrank] at h
    omega
  simpa only [Option.range_eq, Function.comp_def] using
    hext.span_eq_top_of_card_eq_finrank' hcard

end KltDP.Geometry

#check @KltDP.Geometry.exterior_curveClass_not_mem_exceptionalSpan
#print axioms KltDP.Geometry.exterior_curveClass_not_mem_exceptionalSpan
#check @KltDP.Geometry.IsMinimalResolution.exceptional_exterior_numerical_span_eq_top
#print axioms KltDP.Geometry.IsMinimalResolution.exceptional_exterior_numerical_span_eq_top
