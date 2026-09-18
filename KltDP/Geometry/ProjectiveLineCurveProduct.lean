import KltDP.Geometry.ProjectiveSegreGeneralRange
import KltDP.Geometry.ProjectiveSpaceIntegral
import KltDP.Examples.FrobeniusGlobalBlowupSmooth
import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Geometry.ClosedPoints
import Mathlib.AlgebraicGeometry.Fiber

/-!
# Original projective-line products, sections and closed fibers

All objects below use the actual pullback of the original curve structure
morphism with the original projective-line structure morphism. Projectivity,
relative smoothness, a section and every closed scheme-theoretic fiber are
proved with their original maps. Global integrality and Krull dimension
of the product are not asserted here or supplied as assumptions.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.ProjectiveLineCurveProduct

variable {k : Type u} [Field k] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k))

/-- The literal original product over the original field. -/
abbrev scheme : Scheme.{u} := pullback (projectiveSpaceToSpec k 1) c

def firstProjection : scheme c ⟶ projectiveSpace k 1 :=
  pullback.fst (projectiveSpaceToSpec k 1) c

def projection : scheme c ⟶ C := pullback.snd (projectiveSpaceToSpec k 1) c

def structureMorphism : scheme c ⟶ Spec (CommRingCat.of k) :=
  firstProjection c ≫ projectiveSpaceToSpec k 1

@[reassoc] theorem projection_over_base :
    projection c ≫ c = structureMorphism c := pullback.condition.symm

/-- The original product is projective when the original curve is projective. -/
theorem isProjective (hc : IsProjectiveOverField c) :
    IsProjectiveOverField (structureMorphism c) :=
  ProjectiveSegreGeneral.isProjectiveOverField_pullback
    k (projectiveSpaceToSpec k 1) c (KltDP.Geometry.projectiveSpace_isProjectiveOverField k 1) hc

instance projection_isProper : IsProper (projection c) := by
  letI : IsProper (projectiveSpaceToSpec k 1) :=
    (KltDP.Geometry.projectiveSpace_isProjectiveOverField k 1).isProper
  exact MorphismProperty.pullback_snd (P := @IsProper)
    (projectiveSpaceToSpec k 1) c inferInstance

instance projection_smoothOne : IsSmoothOfRelativeDimension 1 (projection c) := by
  letI : MorphismProperty.IsStableUnderBaseChange (@IsSmoothOfRelativeDimension 1) :=
    isSmoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.pullback_snd (P := @IsSmoothOfRelativeDimension 1)
    (projectiveSpaceToSpec k 1) c inferInstance

/-- Relative dimensions add on the same original structure morphisms. -/
instance structure_smoothTwo [IsSmoothOfRelativeDimension 1 c] :
    IsSmoothOfRelativeDimension 2 (structureMorphism c) := by
  rw [← projection_over_base]
  change IsSmoothOfRelativeDimension (1 + 1) (projection c ≫ c)
  infer_instance

/-- The section corresponding to the fixed original point `[1:0]`. -/
def sectionMap : C ⟶ scheme c :=
  pullback.lift (c ≫ Examples.FrobeniusProjectivePoints.pointMorphism (0 : k)) (𝟙 C)
    (by rw [Category.assoc, Examples.FrobeniusProjectivePoints.pointMorphism_over_base,
      Category.comp_id, Category.id_comp])

@[reassoc] theorem sectionMap_projection : sectionMap c ≫ projection c = 𝟙 C :=
  pullback.lift_snd _ _ _

@[reassoc] theorem sectionMap_firstProjection :
    sectionMap c ≫ firstProjection c =
      c ≫ Examples.FrobeniusProjectivePoints.pointMorphism (0 : k) :=
  pullback.lift_fst _ _ _

@[reassoc] theorem sectionMap_over_base :
    sectionMap c ≫ structureMorphism c = c := by
  rw [← projection_over_base, ← Category.assoc, sectionMap_projection, Category.id_comp]

instance projection_surjective : Surjective (projection c) := by
  constructor
  intro y
  refine ⟨(sectionMap c).base y, ?_⟩
  change (sectionMap c ≫ projection c).base y = y
  rw [sectionMap_projection]
  rfl

instance sectionMap_isClosedImmersion : IsClosedImmersion (sectionMap c) := by
  letI : IsClosedImmersion (sectionMap c ≫ projection c) := by
    rw [sectionMap_projection]
    infer_instance
  exact IsClosedImmersion.of_comp (sectionMap c) (projection c)

/-- The first projection restricted to the original scheme-theoretic fiber. -/
def fiberToLine (y : C) : (projection c).fiber y ⟶ projectiveSpace k 1 :=
  (projection c).fiberι y ≫ firstProjection c

/-- Pasting the two original pullback squares retains the actual residue field. -/
theorem fiber_isPullback (y : C) :
    IsPullback (fiberToLine c y) ((projection c).fiberToSpecResidueField y)
      (projectiveSpaceToSpec k 1) (C.fromSpecResidueField y ≫ c) :=
  (IsPullback.of_hasPullback (projection c) (C.fromSpecResidueField y)).paste_horiz
    (IsPullback.of_hasPullback (projectiveSpaceToSpec k 1) c)

variable [IsAlgClosed k] [LocallyOfFiniteType c]

/-- At an original closed point, the canonical base-to-residue-field map
is an isomorphism, so the original fiber projection to P1 is an isomorphism. -/
theorem fiberToLine_isIso (y : C) (hy : IsClosed ({y} : Set C)) :
    IsIso (fiberToLine c y) := by
  letI : IsIso (C.fromSpecResidueField y ≫ c) := by
    rw [← Spec_map_baseToResidueFieldMap c y,
      ← closedPointResidueFieldIso_hom c y hy]
    infer_instance
  exact (fiber_isPullback c y).isIso_fst_of_isIso

def fiberIso (y : C) (hy : IsClosed ({y} : Set C)) :
    (projection c).fiber y ≅ projectiveSpace k 1 :=
  letI := fiberToLine_isIso c y hy
  asIso (fiberToLine c y)

@[simp] theorem fiberIso_hom (y : C) (hy : IsClosed ({y} : Set C)) :
    (fiberIso c y hy).hom = (projection c).fiberι y ≫ firstProjection c := rfl

/-- The closed-fiber isomorphism is over the original field via its original inclusion. -/
@[reassoc] theorem fiberIso_over_base (y : C) (hy : IsClosed ({y} : Set C)) :
    (fiberIso c y hy).hom ≫ projectiveSpaceToSpec k 1 =
      (projection c).fiberι y ≫ structureMorphism c := by
  rw [fiberIso_hom, Category.assoc]
  rfl

theorem fiberι_isClosedImmersion (y : C) (hy : IsClosed ({y} : Set C)) :
    IsClosedImmersion ((projection c).fiberι y) := by
  letI : IsClosedImmersion (C.fromSpecResidueField y) :=
    fromSpecResidueField_isClosedImmersion C y hy
  exact MorphismProperty.pullback_fst (P := @IsClosedImmersion)
    (projection c) (C.fromSpecResidueField y) inferInstance

/-- The original fiber inclusion has exactly the original point-fiber range. -/
theorem range_fiberι (y : C) :
    Set.range ((projection c).fiberι y).base = (projection c).base ⁻¹' {y} :=
  (projection c).range_fiberι y

end KltDP.Geometry.ProjectiveLineCurveProduct

#print axioms KltDP.Geometry.ProjectiveLineCurveProduct.isProjective
#print axioms KltDP.Geometry.ProjectiveLineCurveProduct.sectionMap_projection
#print axioms KltDP.Geometry.ProjectiveLineCurveProduct.fiberIso_over_base
