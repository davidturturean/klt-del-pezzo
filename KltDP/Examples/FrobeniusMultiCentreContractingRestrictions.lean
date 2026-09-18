import KltDP.Examples.FrobeniusMultiCentreContractingNef
import KltDP.Examples.FrobeniusMultiCentreFiberProjectiveLine
import KltDP.Examples.FrobeniusExceptionalEulerDegrees
import KltDP.Geometry.KernelPairingRationalRestrictionFrame

/-!
# The original contracting line is trivial on its original rational null curves

The computed graph, strict-fibre and old-exceptional kernel pairings of the
actual contracting line are zero. Their existing projective-line isomorphisms
respect the original field structures, so the degree-zero frame construction
applies to each original closed immersion and its actual pullback sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreContractingRestrictions

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreGraphProjectiveLine
  FrobeniusMultiCentreGraphCartierStrict FrobeniusMultiCentreFiberGlobalClass
  FrobeniusMultiCentreFiberProjectiveLine FrobeniusMultiCentreExceptional
  FrobeniusMultiCentreExceptionalGlobalClasses FrobeniusMultiCentreGraphExceptionalPairing
  FrobeniusMultiCentreContractingClass FrobeniusMultiCentreContractingNef
  FrobeniusExceptionalFinalConfiguration FrobeniusExceptionalEulerDegrees

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The actual contracting line has a frame on the independently constructed
original global strict graph. -/
def graphRestrictionUnitIso :
    (pullbackInvertibleSheaf (graphStrictι (q + 1) n a)
      (contractingLine q n a ha hproj)).obj ≅
        _root_.SheafOfModules.unit (graphStrict (q + 1) n a).ringCatSheaf := by
  refine rationalRestrictionUnitIsoOfKernelPairingZero
    (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (graphStrictι (q + 1) n a) (globalGraphIsoProjectiveLine (q + 1) n a)
    (globalGraphIsoProjectiveLine_hom_structure (q + 1) n a)
    (multiGraphStrictKernelLine q n a ha) (contractingLine q n a ha hproj) rfl ?_
  change multiPairing (q + 1) n a ha hproj
    (Additive.ofMul (contractingLine q n a ha hproj).toPic)
    (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = 0
  have hclass :
      (Additive.ofMul (contractingLine q n a ha hproj).toPic :
        Additive (multiSurface (q + 1) n a).Pic) = contractingClass q n a ha :=
    contractingLine_class q n a ha hproj
  exact (congrArg (fun c : Additive (multiSurface (q + 1) n a).Pic =>
    multiPairing (q + 1) n a ha hproj c
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic)) hclass).trans
        (contractingClass_graph_pairing q n a ha hproj)

/-- The actual contracting line has a frame on every original strict special fibre. -/
def fiberRestrictionUnitIso (i : Fin n) :
    (pullbackInvertibleSheaf (fiberStrictι (q + 1) n a i)
      (contractingLine q n a ha hproj)).obj ≅
        _root_.SheafOfModules.unit (fiberStrict (q + 1) n a i).ringCatSheaf := by
  refine rationalRestrictionUnitIsoOfKernelPairingZero
    (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (fiberStrictι (q + 1) n a i) (globalFiberIsoProjectiveLine q n a ha i)
    (globalFiberIsoProjectiveLine_hom_structure q n a ha i)
    (fiberKernelLine q n a ha i) (contractingLine q n a ha hproj) rfl ?_
  change multiPairing (q + 1) n a ha hproj
    (Additive.ofMul (contractingLine q n a ha hproj).toPic)
    (-Additive.ofMul (fiberKernelLine q n a ha i).toPic) = 0
  have hclass :
      (Additive.ofMul (contractingLine q n a ha hproj).toPic :
        Additive (multiSurface (q + 1) n a).Pic) = contractingClass q n a ha :=
    contractingLine_class q n a ha hproj
  exact (congrArg (fun c : Additive (multiSurface (q + 1) n a).Pic =>
    multiPairing (q + 1) n a ha hproj c
      (-Additive.ofMul (fiberKernelLine q n a ha i).toPic)) hclass).trans
        (contractingClass_fiber_pairing q n a ha hproj i)

/-- The existing original exceptional-curve isomorphism respects the original
field structure, through its proved tower projection. -/
theorem exceptionalCurveIso_hom_structure (i : Fin n) (idx : FinalIndex.{0} q) :
    (FrobeniusMultiCentreChainPicard.curveIso q n a ha i idx).hom ≫
        projectiveSpaceToSpec k 1 =
      exceptionalCurveι q n a i idx ≫ multiStructure (q + 1) n a := by
  simp only [FrobeniusMultiCentreChainPicard.curveIso, Iso.trans_hom, Category.assoc]
  rw [← componentIso_hom_comp_structure]
  exact (exceptionalCurveι_comp_structure q n a i idx).symm

/-- The actual contracting line has a frame on every original old exceptional
component, with its original inclusion into the multi-centre surface. -/
def oldExceptionalRestrictionUnitIso (i : Fin n) (j : Fin q) :
    (pullbackInvertibleSheaf (exceptionalCurveι q n a i (.inl j))
      (contractingLine q n a ha hproj)).obj ≅
        _root_.SheafOfModules.unit (exceptionalCurve q n a i (.inl j)).ringCatSheaf := by
  refine rationalRestrictionUnitIsoOfKernelPairingZero
    (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (exceptionalCurveι q n a i (.inl j))
    (FrobeniusMultiCentreChainPicard.curveIso q n a ha i (.inl j))
    (exceptionalCurveIso_hom_structure q n a ha i (.inl j))
    (exceptionalKernelLine q n a ha i (.inl j)) (contractingLine q n a ha hproj) rfl ?_
  change multiPairing (q + 1) n a ha hproj
    (Additive.ofMul (contractingLine q n a ha hproj).toPic)
    (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inl j)).toPic) = 0
  have hclass :
      (Additive.ofMul (contractingLine q n a ha hproj).toPic :
        Additive (multiSurface (q + 1) n a).Pic) = contractingClass q n a ha :=
    contractingLine_class q n a ha hproj
  exact (congrArg (fun c : Additive (multiSurface (q + 1) n a).Pic =>
    multiPairing (q + 1) n a ha hproj c
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inl j)).toPic)) hclass).trans
        (contractingClass_old_pairing q n a ha hproj i j)

end KltDP.Examples.FrobeniusMultiCentreContractingRestrictions
