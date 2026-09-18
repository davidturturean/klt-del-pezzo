import KltDP.Geometry.KltExceptionalBlockTransversal
import KltDP.Geometry.KltExceptionalBlockTree
import KltDP.Geometry.ExceptionalForestBlockDimension
import KltDP.Geometry.RationalTreeConfigurationFrames
import KltDP.Geometry.KltExceptionalDegreeZeroRestriction

/-!
# Frames on the original exceptional null restriction

The actual minimal klt resolution supplies the original transverse rational
tree in each exceptional block. Degree zero on its original prime curves
gives actual unit frames, transported through the original curve inclusions.
The finite disjoint block cover then trivializes the same original null
restriction used by Keel's theorem.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ExceptionalForestClosedBlocks

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
  (b : (ActualExceptionalIncidence.graph π).ConnectedComponent)

/-- Vanishing degrees on the original exceptional primes give a frame on
the actual reduced closed block, with all tree geometry derived from klt. -/
theorem blockRestriction_trivial_of_klt
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
    (L : InvertibleSheaf S.toScheme)
    (hdegree : ∀ C : S.PrimeCurve, IsExceptionalCurve π C → C.restrictionDegree L = 0) :
    Nonempty ((pullbackInvertibleSheaf (blockInclusion π hbir b) L).obj ≅
      _root_.SheafOfModules.unit (blockScheme π hbir b).ringCatSheaf) := by
  classical
  letI : Finite (ActualExceptionalIncidence.Vertices π) :=
    ActualExceptionalIncidence.finite_vertices π hbir
  letI : Fintype b.supp := Fintype.ofFinite _
  letI : LocallyOfFiniteType S.structureMorphism := S.projective.locallyOfFiniteType
  refine RationalTreePicard.trivial_of_curve_frames_of_configuration
    (blockScheme π hbir b) (blockInclusion π hbir b) S.structureMorphism
    (block_transversalConfiguration π hbir b hmin hklt)
    (blockScheme_dimension_le_one π hbir b)
    (block_componentPointIncidenceGraph_isTree π hbir b hmin hklt)
    (fun E : b.supp => E.val.val.toScheme) (blockCurve π hbir b)
    (fun _ => inferInstance) (blockCurve_cover π hbir b)
    (blockCurve_incomparable π hbir b)
    (fun E => (hmin.toIsResolution.exceptional_projectiveLine_iso_of_klt
      hklt E.val.val E.val.property).choose)
    (pullbackInvertibleSheaf (blockInclusion π hbir b) L) ?_
  intro E
  obtain ⟨e⟩ := hmin.toIsResolution.exceptional_restriction_trivial_of_klt
    hklt L E.val.val E.val.property (hdegree E.val.val E.val.property)
  exact ⟨(schemeModulePullbackCompIso (blockCurve π hbir b E)
    (blockInclusion π hbir b)).app L.obj ≪≫
      eqToIso (congrArg (fun f => (schemeModulePullback f).obj L.obj)
        (blockCurve_inclusion π hbir b E)) ≪≫ e⟩

end KltDP.Geometry.ExceptionalForestClosedBlocks

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  {π : S.toScheme ⟶ X.toScheme}

/-- The whole original null restriction is trivial when its literal support
is the original exceptional locus and its original exceptional degrees vanish.
No curve coordinates, frames, tree dictionary, or finite cover are supplied. -/
theorem IsMinimalResolution.exceptional_nullRestriction_trivial_of_klt
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
    (L : InvertibleSheaf S.toScheme)
    (hnull : Positivity.nullLocus S.structureMorphism L = ActualExceptionalLocus.primeSupport π)
    (hdegree : ∀ C : S.PrimeCurve, IsExceptionalCurve π C → C.restrictionDegree L = 0) :
    Nonempty ((Positivity.nullLocusRestrict S.structureMorphism L).obj ≅
      _root_.SheafOfModules.unit
        (Positivity.nullLocusScheme S.structureMorphism L).ringCatSheaf) := by
  classical
  letI : IsProper π := hmin.toIsResolution.isProper
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hmin.birational
  exact ⟨ExceptionalForestClosedBlocks.nullRestrictionUnitIsoOfBlocks π hbir L hnull
    (fun b => (ExceptionalForestClosedBlocks.blockRestriction_trivial_of_klt
      π hbir b hmin hklt L hdegree).some)⟩

end KltDP.Geometry

#check @KltDP.Geometry.ExceptionalForestClosedBlocks.blockRestriction_trivial_of_klt
#check @KltDP.Geometry.IsMinimalResolution.exceptional_nullRestriction_trivial_of_klt
#print axioms KltDP.Geometry.ExceptionalForestClosedBlocks.blockRestriction_trivial_of_klt
#print axioms KltDP.Geometry.IsMinimalResolution.exceptional_nullRestriction_trivial_of_klt
