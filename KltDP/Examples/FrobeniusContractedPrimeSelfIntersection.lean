import KltDP.Examples.FrobeniusMultiCentreSpecialNullCurves
import KltDP.Examples.FrobeniusMultiCentreGraphFiberNumericalValues
import KltDP.Examples.FrobeniusMultiCentreExceptionalChainNumerics

/-!
The compiled original kernel-class squares are transported to the
intrinsic self-intersection numbers of the original graph, special
strict fibers and old exceptional primes. No intersection value is
assumed, and the actual prime Cartier divisor and curve degree are retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusContractedPrimeSelfIntersection

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open PrimeCurveClassPairing PrimeCurveTransversalPoint PrimeCurveOfClosedImmersion
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreGraphProjectiveLine
open FrobeniusMultiCentreGraphCartierStrict FrobeniusMultiCentreGraphExceptionalPairing
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreFiberProjectiveLine FrobeniusMultiCentreFiberGlobalClass
open FrobeniusMultiCentreExceptional FrobeniusMultiCentreExceptionalPrime
open FrobeniusMultiCentreExceptionalGlobalClasses
open FrobeniusMultiCentreGraphFiberNumericalValues FrobeniusMultiCentreExceptionalChainNumerics

private theorem selfIntersectionNumber_eq_kernel_pairing
    {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) (C : X.PrimeCurve)
    {Z : Scheme.{u}} (ι : Z ⟶ X.toScheme) [IsClosedImmersion ι] [IsReduced Z]
    (hC : (C : Set X.toScheme) = Set.range ι.base) (L : InvertibleSheaf X.toScheme)
    (hL : L.obj = schemeKernelIdeal ι) :
    C.selfIntersectionNumber hregular =
      pairing X hregular (-Additive.ofMul L.toPic) (-Additive.ofMul L.toPic) := by
  change C.intersectionNumber (X.primeCurveCartier hregular C) = _
  rw [← C.picardRestrictionDegreeHom_cartierPicardHom,
    cartierPicardHom_primeCurveCartier_of_kernel hregular C ι hC L hL]
  exact (pairing_kernelLine_left X hregular C ι hC L hL (-Additive.ofMul L.toPic)).symm

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The original graph prime has intrinsic square `2p − np`, where `p=q+1`. -/
theorem graph_selfIntersectionNumber :
    (graphPrimeCurve q n a ha hproj).selfIntersectionNumber
      (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj) =
        2 * (q + 1 : ℕ) - (n : ℤ) * (q + 1 : ℕ) := by
  letI := isIntegral_of_iso_projectiveLine (globalGraphIsoProjectiveLine (q + 1) n a)
  exact (selfIntersectionNumber_eq_kernel_pairing
    (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (graphPrimeCurve q n a ha hproj) (graphStrictι (q + 1) n a)
    (coe_graphPrimeCurve q n a ha hproj) (multiGraphStrictKernelLine q n a ha) rfl).trans
      (graphKernel_self_pairing q n a ha hproj)

/-- Each original special strict-fiber prime has intrinsic square `−p`. -/
theorem fiber_selfIntersectionNumber (i : Fin n) :
    (fiberPrimeCurve q n a ha hproj i).selfIntersectionNumber
      (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj) = -((q + 1 : ℕ) : ℤ) := by
  letI := isIntegral_of_iso_projectiveLine (globalFiberIsoProjectiveLine q n a ha i)
  exact (selfIntersectionNumber_eq_kernel_pairing
    (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (fiberPrimeCurve q n a ha hproj i) (fiberStrictι (q + 1) n a i)
    (coe_fiberPrimeCurve q n a ha hproj i) (fiberKernelLine q n a ha i) rfl).trans
      (fiberKernel_self_pairing q n a ha hproj i)

/-- Each original old exceptional prime has intrinsic square `−2`. -/
theorem old_selfIntersectionNumber (i : Fin n) (j : Fin q) :
    (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj).selfIntersectionNumber
      (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj) = -2 := by
  letI := exceptionalCurve_isIntegral q n a ha i (.inl j)
  have hpair := chainKernel_pairing_old_self q n a ha hproj i j
  rw [chainKernelClass_castSucc] at hpair
  exact (selfIntersectionNumber_eq_kernel_pairing
    (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj) (exceptionalCurveι q n a i (.inl j))
    (coe_exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj)
    (exceptionalKernelLine q n a ha i (.inl j)) rfl).trans hpair

/-- For at least three centers every labeled contracted prime has square
at most minus two. The inequalities follow from `p` prime and `n>2`. -/
theorem selfIntersectionNumber_le_neg_two_of_labels (hn : 2 < n)
    (C : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve)
    (hlabels : C = graphPrimeCurve q n a ha hproj ∨
      (∃ i : Fin n, C = fiberPrimeCurve q n a ha hproj i) ∨
      ∃ (i : Fin n) (j : Fin q), C = exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj) :
    C.selfIntersectionNumber (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj) ≤ -2 := by
  have hpNat : 2 ≤ q + 1 := (Fact.out : (q + 1).Prime).two_le
  have hp : (2 : ℤ) ≤ (q + 1 : ℕ) := by exact_mod_cast hpNat
  rcases hlabels with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · rw [graph_selfIntersectionNumber]
    have hnNat : 3 ≤ n := by omega
    have hnInt : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnNat
    have hprod := mul_le_mul_of_nonneg_right hnInt
      (show (0 : ℤ) ≤ (q + 1 : ℕ) by omega)
    linarith
  · rw [fiber_selfIntersectionNumber]
    linarith
  · rw [old_selfIntersectionNumber]

end KltDP.Examples.FrobeniusContractedPrimeSelfIntersection
