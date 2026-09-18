import KltDP.Geometry.ExceptionalExteriorNumericalSpan
import KltDP.Geometry.KltResolutionPicardCohomologyInvariants
import KltDP.Geometry.MinimalResolutionQuadraticRegular
import KltDP.Geometry.UnimodularPicardFiniteFree
import KltDP.Geometry.IsolatedNodePicardPairing
import KltDP.Lattices.RationalSpanFiniteIndex

/-!
# Finite index of the original exceptional and exterior Picard span

The original unimodularity theorem makes the original Picard-to-numerical
map injective and supplies finite generation. All exceptional prime classes
and the given exterior prime span numerically by the original rank theorem
and ample pullback positivity. Native localization then proves finite index
for their actual integer span. The smooth Weil-class formulation is identified
with that same span for use with the original node-code interface.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open NormalProjectiveSurface DisjointNegativeCurvesRank

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The actual integer span of all exceptional prime Picard classes and
one specified original exterior prime class. -/
def NormalProjectiveSurface.exceptionalExteriorPicardSpan
    (S : NormalProjectiveSurface k) {X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s) (P : S.PrimeCurve) :
    Submodule ℤ (Additive S.toScheme.Pic) :=
  Submodule.span ℤ (insert
    (Additive.ofMul (cartierPicardClass S.toScheme (S.primeCurveCartier hS P)))
    (Set.range (fun C : ActualExceptionalIncidence.Vertices π =>
      Additive.ofMul (cartierPicardClass S.toScheme (S.primeCurveCartier hS C.val)))))

/-- The actual Picard-to-numerical map is injective under original unimodularity. -/
theorem NormalProjectiveSurface.picardNumericalMap_injective_of_picardUnimodular
    (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hU : S.PicardUnimodular hS) : Function.Injective S.picardNumericalMap := by
  intro a b hab
  apply S.picardIntegralNumericalMap_injective_of_picardUnimodular hS hU
  apply S.integralNumericalRationalization_injective
  simpa only [S.integralNumericalRationalization_picard] using hab

variable {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

/-- The canonical numerical image of this same integer Picard span spans
the whole original rational numerical space. -/
theorem IsMinimalResolution.exceptional_exterior_picard_span_image_eq_top
    (hmin : IsMinimalResolution S X π) (hDP : IsKltDelPezzo X)
    (hrank : X.picardRank = 1) (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : S.PrimeCurve) (hP : ¬ IsExceptionalCurve π P) :
    Submodule.span ℚ (S.picardNumericalMap ''
      (S.exceptionalExteriorPicardSpan π hmin.regular P : Set (Additive S.toScheme.Pic))) = ⊤ := by
  apply top_unique
  rw [← hmin.exceptional_exterior_numerical_span_eq_top hDP hrank p hp P hP]
  apply Submodule.span_le.mpr
  rintro v (rfl | ⟨C, rfl⟩)
  · apply Submodule.subset_span
    refine ⟨Additive.ofMul
      (cartierPicardClass S.toScheme (S.primeCurveCartier hmin.regular P)), ?_, rfl⟩
    exact Submodule.subset_span (Set.mem_insert _ _)
  · apply Submodule.subset_span
    refine ⟨Additive.ofMul
      (cartierPicardClass S.toScheme (S.primeCurveCartier hmin.regular C.val)), ?_, rfl⟩
    exact Submodule.subset_span (Or.inr ⟨C, rfl⟩)

/-- Finite index is proved for the actual span, with no basis, determinant,
rank, numerical fullness, or unimodularity supplied as an input. -/
theorem IsMinimalResolution.exceptional_exterior_picard_span_finiteIndex
    (hmin : IsMinimalResolution S X π) (hDP : IsKltDelPezzo X)
    (hrank : X.picardRank = 1) (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : S.PrimeCurve) (hP : ¬ IsExceptionalCurve π P) :
    (S.exceptionalExteriorPicardSpan π hmin.regular P).toAddSubgroup.FiniteIndex := by
  have hU := (hmin.picard_and_structure_invariants_of_kltDelPezzo hDP hrank p hp).1
  letI : Module.Finite ℤ (Additive S.toScheme.Pic) :=
    (S.picard_free_and_finite_of_picardUnimodular hmin.regular hU).2
  exact KltDP.Lattices.RationalSpanFiniteIndex.finiteIndex_of_span_eq_top
    S.picardNumericalMap
    (S.picardNumericalMap_injective_of_picardUnimodular hmin.regular hU)
    (S.exceptionalExteriorPicardSpan π hmin.regular P)
    (hmin.exceptional_exterior_picard_span_image_eq_top hDP hrank p hp P hP)

/-- The same finite-index statement in the original smooth Weil-to-Picard
prime-class interface used by the node code and its orthogonal splitting. -/
theorem IsMinimalResolution.exceptional_exterior_smoothPicard_span_finiteIndex
    (hmin : IsMinimalResolution S X π) (hDP : IsKltDelPezzo X)
    (hrank : X.picardRank = 1) (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : S.PrimeCurve) (hP : ¬ IsExceptionalCurve π P) :
    letI : IsSmooth S.structureMorphism :=
      MinimalResolutionQuadraticRegular.source_isSmooth π hmin;
    (Submodule.span ℤ (insert
      (S.smoothWeilClassPicardEquiv (S.weilClassMap (Finsupp.single P 1)))
      (Set.range (fun C : ActualExceptionalIncidence.Vertices π =>
        S.smoothWeilClassPicardEquiv
          (S.weilClassMap (Finsupp.single C.val 1)))))).toAddSubgroup.FiniteIndex := by
  letI : IsSmooth S.structureMorphism :=
    MinimalResolutionQuadraticRegular.source_isSmooth π hmin
  have hclass (C : S.PrimeCurve) :
      S.smoothWeilClassPicardEquiv (S.weilClassMap (Finsupp.single C 1)) =
        Additive.ofMul (cartierPicardClass S.toScheme (S.primeCurveCartier hmin.regular C)) :=
    congrArg Additive.ofMul (S.smoothWeilClassPicardEquiv_single_toMul hmin.regular C)
  simpa only [hclass, NormalProjectiveSurface.exceptionalExteriorPicardSpan] using
    hmin.exceptional_exterior_picard_span_finiteIndex hDP hrank p hp P hP

end KltDP.Geometry

#check @KltDP.Geometry.IsMinimalResolution.exceptional_exterior_picard_span_finiteIndex
#print axioms KltDP.Geometry.IsMinimalResolution.exceptional_exterior_picard_span_finiteIndex
#check @KltDP.Geometry.IsMinimalResolution.exceptional_exterior_smoothPicard_span_finiteIndex
#print axioms KltDP.Geometry.IsMinimalResolution.exceptional_exterior_smoothPicard_span_finiteIndex
