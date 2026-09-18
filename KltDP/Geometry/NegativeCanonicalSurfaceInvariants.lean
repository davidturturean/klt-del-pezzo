import KltDP.Geometry.NegativeNefMinimalClassification
import KltDP.Geometry.ProjectivePlaneRationalInvariants
import KltDP.Geometry.RationalSurfaceStructureCohomology
import KltDP.Geometry.RuledSurfaceNumerics
import KltDP.Geometry.RegularResolutionNoetherSum
import KltDP.Geometry.RegularResolutionStructureCohomology
import KltDP.Geometry.SurfacePointBlowupSequenceBirational

/-!
# Original surface invariants from a negative canonical nef pairing

The actual contraction sequence produces a rational or ruled minimal target.
Its original canonical divisor is constructed from the original differential
line. The two classification branches compute the same native quantities,
which the original resolution transports back to the supplied surface.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open SmoothCanonicalExteriorComparison SmoothCanonicalCartierRepresentative
  SmoothCanonicalCartierExterior

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance negativeInvariantsIntegral (X : NormalProjectiveSurface k) :
    IsIntegral X.toScheme := X.integral

/-- A negative canonical pairing with an actual nef line determines the
original Noether sum and Euler characteristic in terms of the original H1.
No classification, numerical formula or target nefness is supplied as input. -/
theorem noether_euler_relations_of_negative_nef
    (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (H : InvertibleSheaf S.toScheme)
    (hH : Positivity.IsNef S.structureMorphism H)
    (hnegative : S.picardPairing hS (cartierPicardClass S.toScheme K) H.toPic < 0) :
    S.intersectionPairing hS K K + (S.picardRank : ℤ) =
        10 - 8 * (cohomologyDimension S.structureMorphism
          (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 : ℤ) ∧
      eulerCharacteristic S.structureMorphism
          (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) =
        1 - (cohomologyDimension S.structureMorphism
          (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 : ℤ) := by
  obtain ⟨V, hV, b, hseq, hover, hsmooth, _hrank, hclassification⟩ :=
    S.exists_rational_or_ruled_minimalModel_of_negative_nef hS K eK H hH hnegative
  letI : IsSmoothOfRelativeDimension 2 V.structureMorphism := hsmooth
  let KV := cartierRepresentative V.structureMorphism
  let eKV : cartierDivisorModule V.toScheme KV ≅
      relativeDifferentialExterior V.structureMorphism 2 :=
    representativeIsoExterior V.structureMorphism
  have htarget :
      V.intersectionPairing hV KV KV + (V.picardRank : ℤ) =
          10 - 8 * (cohomologyDimension V.structureMorphism
            (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf) 1 : ℤ) ∧
        eulerCharacteristic V.structureMorphism
            (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf) =
          1 - (cohomologyDimension V.structureMorphism
            (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf) 1 : ℤ) := by
    rcases hclassification with hrational | hruled
    · have hnoether : V.intersectionPairing hV KV KV + (V.picardRank : ℤ) = 10 :=
        (V.rational_surface_invariants_of_birationalOver_projectivePlane
          hV hrational KV eKV).2.2
      have hcoh := V.structureCohomology_of_rational hV
        ((ProjectiveChart.birationalOver_projectiveSpace_iff k 2 V.structureMorphism).mp hrational)
      constructor
      · simpa only [hcoh.2.1, Nat.cast_zero, mul_zero, sub_zero] using hnoether
      · simpa only [hcoh.2.1, Nat.cast_zero, sub_zero] using hcoh.1
    · obtain ⟨C, c, hCintegral, hCfiniteType, hCquasiCompact, hCseparated,
        hCdim, hCregular, π, hbase, hsurj, hfibers, σ, hsection⟩ := hruled
      letI : IsIntegral C := hCintegral
      letI : LocallyOfFiniteType c := hCfiniteType
      letI : QuasiCompact c := hCquasiCompact
      letI : IsSeparated c := hCseparated
      exact ⟨(RuledSurfaceNumerics.invariants V hV C c hCdim hCregular
          π hbase hsurj hfibers σ hsection KV eKV).2.2,
        RuledSurfaceNumerics.eulerCharacteristic_eq_one_sub_h1 V hV C c hCdim hCregular
          π hbase hsurj hfibers σ hsection⟩
  have hres : IsResolution S V b :=
    ⟨hover, hS, (isBirational_iff_isBirationalScheme b).mpr hseq.isBirationalScheme⟩
  have hsum := hres.canonical_square_add_picardRank_eq hV K KV eK eKV
  have hOne := hres.structureSheaf_cohomologyDimension_eq_of_regular_target hV 1
  have hEuler := hres.structureSheaf_eulerCharacteristic_eq_of_regular_target hV
  constructor
  · calc
      S.intersectionPairing hS K K + (S.picardRank : ℤ) =
          V.intersectionPairing hV KV KV + (V.picardRank : ℤ) := hsum
      _ = 10 - 8 * (cohomologyDimension V.structureMorphism
          (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf) 1 : ℤ) := htarget.1
      _ = 10 - 8 * (cohomologyDimension S.structureMorphism
          (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 : ℤ) := by rw [hOne]
  · calc
      eulerCharacteristic S.structureMorphism
          (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) =
        eulerCharacteristic V.structureMorphism
          (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf) := hEuler
      _ = 1 - (cohomologyDimension V.structureMorphism
          (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf) 1 : ℤ) := htarget.2
      _ = 1 - (cohomologyDimension S.structureMorphism
          (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 : ℤ) := by rw [hOne]

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.noether_euler_relations_of_negative_nef
#print axioms KltDP.Geometry.NormalProjectiveSurface.noether_euler_relations_of_negative_nef
