import KltDP.Geometry.ProperCurveDegreeZeroNonvanishing
import KltDP.Geometry.FiniteGeneratingSections
import KltDP.Geometry.RationalTreePicardMultidegree

/-!
# A globally generated degree-zero line on an original integral proper curve

An actual finite generating family has a section nonvanishing at the
original generic point. The compiled zero-section nonvanishing lemma
proves that its value on the original top open is nonzero. The accepted effective-Cartier
degree-zero theorem then proves triviality of the original Picard class
and supplies an actual unit isomorphism. The field need not be algebraically closed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.CurveGloballyGeneratedDegreeZero

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
  (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]

include f

/-- Original global generation supplies a nonzero section on the actual top open. -/
theorem exists_nonzero_section_of_globallyGenerated (L : InvertibleSheaf Y)
    (hL : Positivity.IsGloballyGenerated L.obj) :
    ∃ s : sections L.obj, s ≠ 0 := by
  letI : CompactSpace Y := (quasiCompact_over_affine_iff f).mp inferInstance
  obtain ⟨G, _⟩ := FiniteGeneratingSections.exists_finite_generatingSections L isCompact_univ hL
  obtain ⟨a, ha⟩ := FiniteNonvanishingGenerators.exists_mem_nonvanishing L G (genericPoint Y)
  refine ⟨(G.s a).val (op ⊤), ?_⟩
  intro hz
  rw [ProperCurveDegreeZeroNonvanishing.nonvanishingOpen_eq_bot_of_top_eq_zero
    L (G.s a) hz] at ha
  exact ha

variable (hdim : topologicalKrullDim Y ≤ 1)
include hdim

/-- An actually globally generated line of original Euler degree zero is trivial in Picard. -/
theorem toPic_eq_one_of_globallyGenerated_degree_zero (L : InvertibleSheaf Y)
    (hdeg : eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0)
    (hL : Positivity.IsGloballyGenerated L.obj) : L.toPic = 1 := by
  obtain ⟨s, hs⟩ := exists_nonzero_section_of_globallyGenerated f L hL
  exact CurveDegreeZeroNotBig.toPic_eq_one_of_nonzero_section_of_degree_zero f hdim L hdeg s hs

/-- The actual module sheaf of that original degree-zero line has an actual global unit frame. -/
def unitIso_of_globallyGenerated_degree_zero (L : InvertibleSheaf Y)
    (hdeg : eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0)
    (hL : Positivity.IsGloballyGenerated L.obj) :
    L.obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf :=
  ((RationalTreePicard.toPic_eq_one_iff_iso_unit L).mp
    (toPic_eq_one_of_globallyGenerated_degree_zero f hdim L hdeg hL)).some

end KltDP.Geometry.CurveGloballyGeneratedDegreeZero
