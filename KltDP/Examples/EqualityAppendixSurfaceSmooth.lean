import KltDP.Examples.EqualityAppendixSurface
import KltDP.Examples.FrobeniusMultiCentreIntegral

/-!
# Smoothness of the original three-centre appendix surface

The complements of the finite centres and of the infinity centre cover the
original product. On the corresponding pullback pieces one projection is an
isomorphism, so the mixed surface is locally an open part of one of the two
original smooth towers. All maps and centres are those of `EqualityAppendixSurface`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.EqualityAppendixSurface

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusMultiCentreSurface
  FrobeniusMultiCentreIntegral FrobeniusContactTowerInfinity
  FrobeniusStageComplement.PlaneChartedScheme

variable {k : Type u} [Field k] [CharP k 3]

theorem finiteParameters_injective : Function.Injective (finiteParameters (k := k)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [finiteParameters]

abbrev finiteComplement : (projectiveProduct k).Opens :=
  earlierComplement 3 2 (finiteParameters (k := k))

abbrev infinityComplement : (projectiveProduct k).Opens :=
  initialPuncture (infinityInitial k)

theorem complements_cover (x : projectiveProduct k) :
    x ∈ infinityComplement ∨ x ∈ finiteComplement := by
  by_cases hx : x = infinityCenter k
  · right
    rw [finiteComplement, mem_earlierComplement_iff, hx]
    exact fun i => infinityCenter_ne_graphPoint 3 (finiteParameters i)
  · left
    change x ≠ infinityCenter k
    exact hx

theorem finiteProjection_on_finiteComplement_isIso :
    IsIso (finiteProjection (k := k) ∣_ finiteComplement) :=
  multiProjection_restrict_isIso 3 2 finiteParameters finiteComplement
    (not_mem_earlierComplement 3 2 finiteParameters)

theorem infinityProjection_on_infinityComplement_isIso :
    IsIso (infinityProjection (k := k) 3 ∣_ infinityComplement) :=
  toInitial_restrict_isIso (infinityInitial k) 3

abbrev supportCover : Scheme.OpenCover.{u} (surface (k := k)) :=
  Scheme.Pullback.openCoverOfBase
    (twoOpenCover infinityComplement finiteComplement complements_cover)
    finiteProjection (infinityProjection 3)

theorem structureMap_smoothTwo [IsAlgClosed k] :
    IsSmoothOfRelativeDimension 2 (structureMap (k := k)) := by
  letI : IsSmoothOfRelativeDimension 2
      (finiteProjection (k := k) ≫ projectiveProductToSpec) :=
    multiStructure_smoothTwo 3 2 finiteParameters finiteParameters_injective
  letI : IsSmoothOfRelativeDimension 2
      (infinityProjection (k := k) 3 ≫ projectiveProductToSpec) := by
    rw [infinityProjection_structure]
    infer_instance
  letI := finiteProjection_on_finiteComplement_isIso (k := k)
  letI := infinityProjection_on_infinityComplement_isIso (k := k)
  letI : IsIso (pullback.snd (finiteProjection (k := k)) finiteComplement.ι) :=
    isIso_pullback_snd_ι_of_restrict _ _
  letI : IsIso (pullback.snd (infinityProjection (k := k) 3) infinityComplement.ι) :=
    isIso_pullback_snd_ι_of_restrict _ _
  change IsSmoothOfRelativeDimension 2
    ((pullback.fst finiteProjection (infinityProjection 3) ≫ finiteProjection) ≫
      projectiveProductToSpec)
  apply IsLocalAtSource.of_openCover (P := @IsSmoothOfRelativeDimension 2) supportCover
  rintro ⟨b⟩
  cases b
  · rw [Scheme.Pullback.openCoverOfBase_map]
    exact pieceRight_smoothTwo finiteProjection (infinityProjection 3)
      projectiveProductToSpec finiteComplement
  · rw [Scheme.Pullback.openCoverOfBase_map]
    exact pieceLeft_smoothTwo finiteProjection (infinityProjection 3)
      projectiveProductToSpec infinityComplement

end KltDP.Examples.EqualityAppendixSurface
