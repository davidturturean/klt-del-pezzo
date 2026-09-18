import KltDP.Geometry.PicardWeilClassHom
import KltDP.Geometry.SmoothCanonicalCartierPicard
import KltDP.Examples.FrobeniusMultiCentreCanonicalIntegralRelation
import KltDP.Examples.FrobeniusMultiCentreSpecialNullCurves

/-!
# Actual Weil representatives of the original Frobenius source classes

The canonical Cartier divisor represents the independently constructed
atlas canonical line. The graph and special fibres use the original
embedded prime curves; their Cartier-to-Weil images are the actual singleton
prime divisors. M uses its previously constructed actual Cartier divisor.
The source normal-surface packaging and all geometric producers are retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRepresentatives

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open PrimeCurveOfClosedImmersion PrimeCurveTransversalPoint
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreCanonicalOpenComparison
open FrobeniusMultiCentreGraphCartierStrict FrobeniusMultiCentreFiberGlobalClass
open FrobeniusMultiCentreGraphExceptionalPairing
open FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreFiberProjectiveLine
open FrobeniusMultiCentreContractingClass FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreSpecialNullCurves

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The existing original normal projective surface, unchanged. -/
abbrev sourceSurface : NormalProjectiveSurface k :=
  multiSurfaceSurface (q + 1) n a ha hproj

/-- The established Cartier representative of the actual smooth canonical sheaf. -/
def canonicalCartier : CartierDivisor (sourceSurface q n a ha hproj).toScheme := by
  letI := multiSurface_isIntegral (q + 1) n a ha
  letI := multiStructure_smoothTwo (q + 1) n a ha
  exact SmoothCanonicalCartierRepresentative.cartierRepresentative
    (multiStructure (q + 1) n a)

/-- Its original divisor module is the original atlas canonical line. -/
def canonicalCartierIso :
    cartierDivisorModule (sourceSurface q n a ha hproj).toScheme
        (canonicalCartier q n a ha hproj) ≅
      (multiCanonicalLine (q + 1) n a ha).obj := by
  letI := multiSurface_isIntegral (q + 1) n a ha
  letI := multiStructure_smoothTwo (q + 1) n a ha
  exact SmoothCanonicalCartierRepresentative.cartierRepresentativeIso
    (multiStructure (q + 1) n a)

/-- The original canonical Picard class, obtained from the actual sheaf comparison. -/
theorem canonicalCartier_picard :
    cartierPicardHom (sourceSurface q n a ha hproj).toScheme
        (canonicalCartier q n a ha hproj) = multiCanonicalClass (q + 1) n a ha := by
  letI := multiSurface_isIntegral (q + 1) n a ha
  letI := multiStructure_smoothTwo (q + 1) n a ha
  exact SmoothCanonicalCartierPicard.cartierPicardHom_representative
    (multiStructure (q + 1) n a)

/-- The actual Weil divisor of that canonical Cartier representative. -/
def canonicalWeil : (sourceSurface q n a ha hproj).WeilDivisor :=
  (sourceSurface q n a ha hproj).cartierToWeilHom (canonicalCartier q n a ha hproj)

/-- The actual Weil divisor of the previously constructed Cartier representative of M. -/
def contractingWeil : (sourceSurface q n a ha hproj).WeilDivisor :=
  (sourceSurface q n a ha hproj).cartierToWeilHom (contractingDivisor q n a ha hproj)

/-- The source canonical class maps to the actual canonical Weil representative. -/
theorem canonical_picardToWeil :
    (sourceSurface q n a ha hproj).picardToWeilClassHom
        (multiCanonicalClass (q + 1) n a ha) =
      (sourceSurface q n a ha hproj).weilClassMap (canonicalWeil q n a ha hproj) := by
  rw [← canonicalCartier_picard q n a ha hproj]
  exact (sourceSurface q n a ha hproj).picardToWeilClassHom_cartierPicardHom _

/-- The graph term maps to the singleton of the original embedded graph prime. -/
theorem graph_picardToWeil :
    (sourceSurface q n a ha hproj).picardToWeilClassHom
        (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) =
      (sourceSurface q n a ha hproj).weilClassMap
        (Finsupp.single (graphPrimeCurve q n a ha hproj) 1) := by
  have h := (sourceSurface q n a ha hproj).picardToWeilClassHom_cartierPicardHom
    ((sourceSurface q n a ha hproj).primeCurveCartier
      (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
      (graphPrimeCurve q n a ha hproj))
  rw [graphPrimeCurve_cartierClass q n a ha hproj,
    (sourceSurface q n a ha hproj).cartierToWeilHom_primeCurveCartier
      (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
      (graphPrimeCurve q n a ha hproj)] at h
  exact h

/-- The intrinsic Cartier divisor of the original strict fibre has its original kernel class. -/
theorem fiberCartier_picard (i : Fin n) :
    cartierPicardHom (sourceSurface q n a ha hproj).toScheme
      ((sourceSurface q n a ha hproj).primeCurveCartier
        (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
        (fiberPrimeCurve q n a ha hproj i)) =
      -Additive.ofMul (fiberKernelLine q n a ha i).toPic := by
  letI := isIntegral_of_iso_projectiveLine (globalFiberIsoProjectiveLine q n a ha i)
  exact cartierPicardHom_primeCurveCartier_of_kernel
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (fiberPrimeCurve q n a ha hproj i) (fiberStrictι (q + 1) n a i)
    (coe_fiberPrimeCurve q n a ha hproj i) (fiberKernelLine q n a ha i) rfl

/-- Each fibre term maps to the singleton of that same original embedded prime. -/
theorem fiber_picardToWeil (i : Fin n) :
    (sourceSurface q n a ha hproj).picardToWeilClassHom
        (-Additive.ofMul (fiberKernelLine q n a ha i).toPic) =
      (sourceSurface q n a ha hproj).weilClassMap
        (Finsupp.single (fiberPrimeCurve q n a ha hproj i) 1) := by
  have h := (sourceSurface q n a ha hproj).picardToWeilClassHom_cartierPicardHom
    ((sourceSurface q n a ha hproj).primeCurveCartier
      (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
      (fiberPrimeCurve q n a ha hproj i))
  rw [fiberCartier_picard q n a ha hproj i,
    (sourceSurface q n a ha hproj).cartierToWeilHom_primeCurveCartier
      (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
      (fiberPrimeCurve q n a ha hproj i)] at h
  exact h

/-- The M term uses the actual existing Cartier divisor, not a chosen Weil inverse. -/
theorem contracting_picardToWeil :
    (sourceSurface q n a ha hproj).picardToWeilClassHom (contractingClass q n a ha) =
      (sourceSurface q n a ha hproj).weilClassMap (contractingWeil q n a ha hproj) := by
  rw [← contractingDivisor_class q n a ha hproj]
  exact (sourceSurface q n a ha hproj).picardToWeilClassHom_cartierPicardHom _

end KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRepresentatives
