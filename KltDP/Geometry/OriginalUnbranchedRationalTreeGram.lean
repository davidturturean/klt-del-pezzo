import KltDP.Geometry.OriginalUnbranchedRationalTreeIntersectionMatrix
import KltDP.Geometry.DisjointNegativeCurvesRank
import KltDP.LinearAlgebra.OrthogonalCopyGram

/-!
# The original numerical classes of the actual coherent tree copies

The numerical classes are those of the actual prime Cartier divisors on
the unchanged quadratic surface. The compiled pairing comparison turns
the geometric component-intersection formulas into equality with the
original numerical Gram matrix on each sheet and zero between sheets.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

open NormalProjectiveSurface RationalTreePicard DisjointNegativeCurvesRank
open KltDP.LinearAlgebra.CanonicalCorrection

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]

local instance originalUnbranchedTreeGramSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedTreeGramMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable {C : Scheme.{u}} [NoetherianSpace C] [IsLocallyNoetherian C] [IsReduced C]
    [ConnectedSpace C] [C.IsSeparated]
    (sC : C ⟶ Spec (CommRingCat.of k)) [IsProper sC]
    (hdim : topologicalKrullDim C ≤ 1)
    (hTree : (componentPointIncidenceGraph C).IsTree)
    (htrans : HasTransverseComponentBranches C)
    (eC : ∀ D : ↥(irreducibleComponents C), componentUnionScheme C {D} ≅ projectiveSpace k 1)
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hsm : IsSmooth
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism))
    (f : C ⟶ S.toScheme) [IsClosedImmersion f]
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo.base))

local notation "CoverSurface" =>
  OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "CoverRegular" =>
  OriginalCartierRamificationSmooth.regularPoints_of_smooth_base_and_branch
    S E hE L e h2 hred hne hsm
local notation "baseCurve" => RationalComponentPrimeCurves.curve S f eC
local notation "copyCurve" => liftedCurve S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj

/-- The actual numerical Cartier class of the unchanged coherent component prime curve. -/
def numericalCopy (ε : Bool) (D : ↥(irreducibleComponents C)) : (CoverSurface).NumericalClassGroup :=
  curveClass CoverSurface CoverRegular (copyCurve ε D)

local notation "copyClass" =>
  numericalCopy S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj

/-- Same-sheet actual numerical pairings equal the original component numerical pairings. -/
theorem numericalCopy_pairing_same (ε : Bool) (D F : ↥(irreducibleComponents C)) :
    (CoverSurface).numericalIntersectionBilinForm CoverRegular (copyClass ε D) (copyClass ε F) =
      S.numericalIntersectionBilinForm S.regularPoints_of_isSmooth
        (curveClass S S.regularPoints_of_isSmooth (baseCurve D))
        (curveClass S S.regularPoints_of_isSmooth (baseCurve F)) := by
  change (CoverSurface).numericalIntersectionBilinForm CoverRegular
    (curveClass CoverSurface CoverRegular (copyCurve ε D))
    (curveClass CoverSurface CoverRegular (copyCurve ε F)) = _
  rw [curveClass_pairing, curveClass_pairing,
    PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber
      CoverSurface CoverRegular (copyCurve ε D) (copyCurve ε F),
    PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber
      S S.regularPoints_of_isSmooth (baseCurve D) (baseCurve F)]
  exact_mod_cast liftedCurve_intersection_same
    S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj ε D F

/-- Opposite coherent sheets are orthogonal in the actual numerical class group. -/
theorem numericalCopy_pairing_opposite (ε : Bool) (D F : ↥(irreducibleComponents C)) :
    (CoverSurface).numericalIntersectionBilinForm CoverRegular (copyClass ε D) (copyClass (!ε) F) = 0 :=
  curveClass_pairing_eq_zero_of_disjoint CoverSurface CoverRegular (copyCurve ε D) (copyCurve (!ε) F)
    (liftedCurve_disjoint_opposite S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj ε D F)

/-- Each actual coherent sheet has exactly the original negative numerical Gram matrix. -/
theorem negativeGram_numericalCopy (ε : Bool) :
    negativeGram ((CoverSurface).numericalIntersectionBilinForm CoverRegular) (copyClass ε) =
      negativeGram (S.numericalIntersectionBilinForm S.regularPoints_of_isSmooth)
        (fun D => curveClass S S.regularPoints_of_isSmooth (baseCurve D)) := by
  ext D F
  change -(CoverSurface).numericalIntersectionBilinForm CoverRegular (copyClass ε D) (copyClass ε F) = _
  rw [numericalCopy_pairing_same S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj ε D F]
  rfl

end KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

#print axioms KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry.negativeGram_numericalCopy
#print axioms KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry.numericalCopy_pairing_opposite
