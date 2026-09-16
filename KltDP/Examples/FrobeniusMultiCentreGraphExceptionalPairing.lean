import KltDP.Examples.FrobeniusMultiCentreGraphPicardClass
import KltDP.Examples.FrobeniusMultiCentreExceptionalPrime
import KltDP.Examples.FrobeniusMultiCentreGraphContacts
import KltDP.Geometry.PrimeCurveClassPairing
import KltDP.Geometry.SmoothSurfaceRegularity

/-!
# The global strict graph pairs to zero with every old exceptional component

The original global strict graph misses every old exceptional component.
Its actual kernel line therefore restricts to a trivial line on that
component. The accepted restriction-degree and symmetric-pairing adapters
give the numerical row for the original curves and, using their proved
Picard classes, for the corresponding total-transform class expressions.

The original multi-centre surface's projectivity remains explicit, as
required by the existing numerical API. Its regularity is proved from
the accepted smooth structure morphism. No degree, DVR, disjointness,
regularity, class identity, or intersection value is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreGraphExceptionalPairing

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
  KltDP.Geometry.PrimeCurveClassPairing
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreExceptionalPrime
  FrobeniusMultiCentreExceptionalGlobalClasses FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreGraphContacts FrobeniusMultiCentreGraphCartierStrict
  FrobeniusMultiCentreGraphPicardClass

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- All points of the actual multi-centre surface are regular, by its proved smoothness. -/
theorem multiSurfaceSurface_regularPoints (p n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (hproj : IsProjectiveOverField (multiStructure p n a)) :
    ∀ x : (multiSurfaceSurface p n a ha hproj).Point,
      RegularPoint (multiSurfaceSurface p n a ha hproj).toScheme x := by
  letI : IsSmoothOfRelativeDimension 2 (multiStructure p n a) :=
    multiStructure_smoothTwo p n a ha
  letI : IsSmooth (multiSurfaceSurface p n a ha hproj).structureMorphism :=
    IsSmoothOfRelativeDimension.isSmooth 2 (multiStructure p n a)
  exact (multiSurfaceSurface p n a ha hproj).regularPoints_of_isSmooth

/-- The existing symmetric pairing on the original multi-centre surface. -/
def multiPairing (p n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure p n a))
    (x y : Additive (multiSurface p n a).Pic) : ℤ :=
  pairing (multiSurfaceSurface p n a ha hproj)
    (multiSurfaceSurface_regularPoints p n a ha hproj) x y

set_option maxHeartbeats 800000 in
theorem multiPairing_symm (p n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure p n a))
    (x y : Additive (multiSurface p n a).Pic) :
    multiPairing p n a ha hproj x y = multiPairing p n a ha hproj y x :=
  pairing_symm (multiSurfaceSurface p n a ha hproj)
    (multiSurfaceSurface_regularPoints p n a ha hproj) x y

variable (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  [Fact (q + 1).Prime] [CharP k (q + 1)]
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The inverse original strict-graph kernel has degree zero on every original old component. -/
theorem graphStrictRestrictionDegree_old_eq_zero (i : Fin n) (j : Fin q) :
    (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom
      (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj)
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = 0 := by
  apply restrictionDegreeHom_neg_kernel_zero (multiSurfaceSurface (q + 1) n a ha hproj)
    (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj)
    (graphStrictι (q + 1) n a) (multiGraphStrictKernelLine q n a ha) rfl
  rw [PrimeCurve.range_inclusion, coe_exceptionalPrimeCurveSPn]
  exact (graphStrict_disjoint_exceptional_same q n a i j).symm

/-- `C_{ij} · B = 0` for the negative classes of the original embedded kernel lines. -/
theorem oldKernel_graphKernel_pairing_eq_zero (i : Fin n) (j : Fin q) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inl j)).toPic)
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = 0 := by
  letI := exceptionalCurve_isIntegral q n a ha i (.inl j)
  exact (pairing_kernelLine_left (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj)
    (exceptionalCurveι q n a i (.inl j)) (coe_exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj)
    (exceptionalKernelLine q n a ha i (.inl j)) rfl
    (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic)).trans
    (graphStrictRestrictionDegree_old_eq_zero q n a ha hproj i j)

/-- `B · C_{ij} = 0` for the original embedded kernel lines. -/
theorem graphKernel_oldKernel_pairing_eq_zero (i : Fin n) (j : Fin q) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic)
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inl j)).toPic) = 0 := by
  rw [multiPairing_symm]
  exact oldKernel_graphKernel_pairing_eq_zero q n a ha hproj i j

/-- The same original graph pairing with the proved consecutive-total-class difference. -/
theorem graphKernel_oldTotalDifference_pairing_eq_zero (i : Fin n) (j : Fin q) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic)
      (exceptionalClass (q + 1) n a i j.castSucc - exceptionalClass (q + 1) n a i j.succ) = 0 := by
  have h : -Additive.ofMul (exceptionalKernelLine q n a ha i (.inl j)).toPic =
      exceptionalClass (q + 1) n a i j.castSucc - exceptionalClass (q + 1) n a i j.succ :=
    chainClass_SPn q n a ha i j
  rw [← h]
  exact graphKernel_oldKernel_pairing_eq_zero q n a ha hproj i j

/-- Substitute the proved global graph row into the actual zero intersection calculation. -/
theorem globalRow_oldTotalDifference_pairing_eq_zero (i : Fin n) (j : Fin q) :
    multiPairing (q + 1) n a ha hproj
      ((q + 1) • multiFirstFiberClass (q + 1) n a + multiSecondFiberClass (q + 1) n a -
        ∑ i' : Fin n, ∑ j' : Fin (q + 1), exceptionalClass (q + 1) n a i' j')
      (exceptionalClass (q + 1) n a i j.castSucc - exceptionalClass (q + 1) n a i j.succ) = 0 := by
  rw [← strictGraphKernelLine_picard_row q n a ha]
  exact graphKernel_oldTotalDifference_pairing_eq_zero q n a ha hproj i j

end KltDP.Examples.FrobeniusMultiCentreGraphExceptionalPairing
