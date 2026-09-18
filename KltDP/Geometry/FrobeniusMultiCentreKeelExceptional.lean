import KltDP.Geometry.KeelSurfaceExceptionalComparison
import KltDP.Examples.FrobeniusMultiCentreContractingBig
import KltDP.Examples.FrobeniusContractingNullRestriction
import KltDP.Geometry.TrivialInvertibleSheafSemiample

/-!
# The original contracting line on Keel's actual exceptional scheme

The source complete-system support equals the independently constructed
growth null locus for the original Frobenius surface. The canonical
reduced-scheme comparison transports the already constructed whole-locus
unit frame. This proves semiampleness of the restriction to the actual
source exceptional scheme, without applying or assuming Keel's theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreKeelExceptional

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreContractingNef NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The complete-system exceptional support of the original M is its original null locus. -/
theorem contractingLine_exceptionalSupport_eq_nullLocus (hn : 2 < n) :
    letI : IsProper (multiStructure (q + 1) n a) := hproj.isProper
    KeelCompleteSystem.exceptionalSupport (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj) =
      Positivity.nullLocus (multiStructure (q + 1) n a) (contractingLine q n a ha hproj) := by
  letI : IsProper (multiStructure (q + 1) n a) := hproj.isProper
  let S := multiSurfaceSurface (q + 1) n a ha hproj
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    multiStructure_smoothTwo (q + 1) n a ha
  letI : IsSmooth S.structureMorphism := IsSmoothOfRelativeDimension.isSmooth 2 _
  have hpositive : 0 < S.selfIntersection S.regularPoints_of_isSmooth
      (contractingLine q n a ha hproj) := by
    change 0 < S.picardPairing S.regularPoints_of_isSmooth
      (cartierPicardClass S.toScheme (contractingDivisor q n a ha hproj))
      (cartierPicardClass S.toScheme (contractingDivisor q n a ha hproj))
    rw [S.picardPairing_class, contractingDivisor_square]
    have hn' : (2 : ℤ) < n := by exact_mod_cast hn
    exact mul_pos (by positivity) (sub_pos.mpr hn')
  exact KeelSurfaceExceptionalComparison.exceptionalSupport_eq_nullLocus
    S S.regularPoints_of_isSmooth (SmoothCanonicalCartierRepresentative.weilRepresentative S)
    (SurfaceRiemannRochSource.constructedCanonical_isCanonical S)
    (contractingLine q n a ha hproj) (contractingLine_isNef q n a ha hproj hn.le) hpositive

/-- The actual source exceptional scheme is canonically isomorphic to the actual null scheme. -/
def contractingLine_exceptionalSchemeIso (hn : 2 < n) :
    letI : IsProper (multiStructure (q + 1) n a) := hproj.isProper
    KeelCompleteSystem.exceptionalScheme (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj) ≅
      Positivity.nullLocusScheme (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj) := by
  letI : IsProper (multiStructure (q + 1) n a) := hproj.isProper
  exact KeelCompleteSystem.exceptionalSchemeIso _ _
    (contractingLine_exceptionalSupport_eq_nullLocus q n a ha hproj hn)

/-- The previously constructed whole-locus frame gives a frame on the actual source restriction. -/
def contractingLine_exceptionalRestrictionUnitIso (hn : 2 < n) :
    letI : IsProper (multiStructure (q + 1) n a) := hproj.isProper
    (KeelCompleteSystem.exceptionalRestrict (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj)).obj ≅
      _root_.SheafOfModules.unit
        (KeelCompleteSystem.exceptionalScheme (multiStructure (q + 1) n a)
          (contractingLine q n a ha hproj)).ringCatSheaf := by
  letI : IsProper (multiStructure (q + 1) n a) := hproj.isProper
  let h := contractingLine_exceptionalSupport_eq_nullLocus q n a ha hproj hn
  let j := (KeelCompleteSystem.exceptionalSchemeIso _ _ h).hom
  exact (KeelCompleteSystem.exceptionalRestrictIso _ _ h).symm ≪≫
    (schemeModulePullback j).mapIso
      (FrobeniusContractingNullRestriction.contractingNullRestrictionUnitIso q n a ha hproj hn) ≪≫
        schemeModulePullbackUnitIso j

/-- M is semiample on the whole actual source exceptional scheme. -/
theorem contractingLine_exceptionalRestriction_semiample (hn : 2 < n) :
    letI : IsProper (multiStructure (q + 1) n a) := hproj.isProper
    Positivity.IsSemiample (KeelCompleteSystem.exceptionalRestrict
      (multiStructure (q + 1) n a) (contractingLine q n a ha hproj)) := by
  letI : IsProper (multiStructure (q + 1) n a) := hproj.isProper
  exact Positivity.isSemiample_of_unitIso _
    (contractingLine_exceptionalRestrictionUnitIso q n a ha hproj hn)

end KltDP.Geometry.FrobeniusMultiCentreKeelExceptional
