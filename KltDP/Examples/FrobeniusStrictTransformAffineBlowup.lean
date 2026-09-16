import KltDP.Examples.FrobeniusStrictTransformContact
import KltDP.Geometry.AffineBlowupProper
import KltDP.Compatibility.SchemeTwoOpenCoverIso
import KltDP.Geometry.GluedIdealSheafKernel
import KltDP.Geometry.SchemeKernelOpenPullback

/-!
# The original strict transform over the complete affine blowup

The residual affine curve is closed in the entire Rees blowup: its
composite with the separated blowdown is the original closed monomial
curve. The existing residual chart of the whole strict transform is
therefore exactly its inverse image over the complete affine blowup.
The resulting actual pullback square retains the original closed
inclusion and gives the original ideal's section-ring restriction.

The selected chart and the complement of this closed affine curve cover
the complete affine blowup. On the image of that complement, the original
global strict-transform source is empty and its kernel is framed by one,
with its inclusion normalized. This does not assert a total-transform
factorization: its exceptional multiplicities remain a separate equation
and ideal-sheaf obligation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStrictTransformAffineBlowup

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusStrictTransformClosure
open FrobeniusGlobalStrictTransform FrobeniusStrictTransformContact

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- Closedness holds in the complete Rees blowup, by its separated projection. -/
instance residualCurveMorphism_isClosedImmersion (m : ℕ) :
    IsClosedImmersion (residualCurveMorphism (k := k) m) := by
  letI : IsClosedImmersion
      (residualCurveMorphism (k := k) m ≫ AffineBlowup.toSpec centerIdeal) := by
    rw [residualCurveMorphism_toSpec]
    change IsClosedImmersion (curveInPlane (k := k) (m + 1))
    infer_instance
  exact IsClosedImmersion.of_comp (residualCurveMorphism (k := k) m)
    (AffineBlowup.toSpec centerIdeal)

/-- The original global ideal is the kernel of this actual affine residual lift. -/
theorem strictTransformIdeal_succ_eq (n m : ℕ) :
    strictTransformIdeal (k := k) (n + 1) (m + (n + 1)) =
      (residualCurveMorphism m ≫
        ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup).ker := by
  rw [strictTransformIdeal_eq_local, liftedGraphClosureIdeal_eq,
    PlaneChartedScheme.residualCurve_succ]

/-- The actual closed source has the closure of the original affine lift as its range. -/
theorem strictTransform_succ_range (n m : ℕ) :
    Set.range (strictTransformι (k := k) (n + 1) (m + (n + 1))).base =
      closure (Set.range (residualCurveMorphism m ≫
        ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup).base) := by
  rw [strictTransformι, Scheme.IdealSheafData.range_gluedTo, strictTransformIdeal_succ_eq]
  exact Scheme.Hom.support_ker _

/-- The existing strict-transform chart preserves both original ambient maps. -/
@[reassoc] theorem residualChart_affine_ι (n m : ℕ) :
    residualChart (k := k) (n + 1) m ≫ strictTransformι (n + 1) (m + (n + 1)) =
      residualCurveMorphism m ≫
        ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup := by
  rw [residualChart_ι, PlaneChartedScheme.residualCurve_succ]

/-- Its range is exactly the inverse image of the complete affine blowup piece. -/
theorem range_residualChart_affine (n m : ℕ) :
    Set.range (residualChart (k := k) (n + 1) m).base =
      (strictTransformι (n + 1) (m + (n + 1))).base ⁻¹'
        Set.range (((projectiveProductInitial (k := k)).stage n).nextAffineBlowup).base := by
  let c := residualCurveMorphism (k := k) m
  let j := ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup
  let f := residualChart (k := k) (n + 1) m
  let i := strictTransformι (k := k) (n + 1) (m + (n + 1))
  have hw : f ≫ i = c ≫ j := residualChart_affine_ι n m
  have hr : Set.range i.base = closure (Set.range (c ≫ j).base) :=
    strictTransform_succ_range n m
  change Set.range f.base = i.base ⁻¹' Set.range j.base
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨c.base t, congrArg (fun h => h.base t) hw.symm⟩
  · rintro ⟨a, ha⟩
    have hmem : a ∈ j.base ⁻¹' closure (Set.range (c ≫ j).base) := by
      change j.base a ∈ closure (Set.range (c ≫ j).base)
      rw [ha, ← hr]
      exact ⟨z, rfl⟩
    rw [ReducedClosedImageChart.preimage_closure_range c j] at hmem
    obtain ⟨t, ht⟩ := hmem
    refine ⟨t, i.isClosedEmbedding.injective ?_⟩
    change (f ≫ i).base t = i.base z
    rw [hw]
    exact (congrArg j.base ht).trans ha

/-- This is the actual scheme pullback, with the original strict-transform inclusion. -/
theorem strictTransform_affine_isPullback (n m : ℕ) :
    IsPullback (residualCurveMorphism (k := k) m) (residualChart (n + 1) m)
      (((projectiveProductInitial (k := k)).stage n).nextAffineBlowup)
      (strictTransformι (n + 1) (m + (n + 1))) :=
  (KltDP.SchemeTwoOpenGluing.isPullback_of_range
    (residualChart (k := k) (n + 1) m) (residualCurveMorphism m)
    (strictTransformι (n + 1) (m + (n + 1)))
    (((projectiveProductInitial (k := k)).stage n).nextAffineBlowup)
    (residualChart_affine_ι n m) (range_residualChart_affine n m)).flip

/-- The entire original affine ideal restriction, through its original section-ring map. -/
theorem strictTransform_ideal_affine (n m : ℕ)
    (U : (AffineBlowup.scheme (centerIdeal (k := k))).affineOpens) :
    (residualCurveMorphism m).ker.ideal U =
      ((strictTransformIdeal (k := k) (n + 1) (m + (n + 1))).ideal
        ⟨((projectiveProductInitial (k := k)).stage n).nextAffineBlowup ''ᵁ U,
          U.2.image_of_isOpenImmersion _⟩).comap
        ((((projectiveProductInitial (k := k)).stage n).nextAffineBlowup).appIso U).inv.hom := by
  have h := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (strictTransformι (k := k) (n + 1) (m + (n + 1))) (residualCurveMorphism m)
    (residualChart (n + 1) m)
    (((projectiveProductInitial (k := k)).stage n).nextAffineBlowup)
    (strictTransform_affine_isPullback n m) U
  simpa only [strictTransformι, Scheme.IdealSheafData.ker_gluedTo] using h

/-- The complement of the original closed affine residual curve in the complete Rees blowup. -/
def affineResidualComplement (m : ℕ) :
    (AffineBlowup.scheme (centerIdeal (k := k))).Opens :=
  ⟨(Set.range (residualCurveMorphism (k := k) m).base)ᶜ,
    (residualCurveMorphism (k := k) m).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The selected original chart and this actual complement cover the complete affine blowup. -/
theorem affineResidual_cover (m : ℕ)
    (x : AffineBlowup.scheme (centerIdeal (k := k))) :
    x ∈ (coordinateChart (k := k)).opensRange ∨ x ∈ affineResidualComplement m := by
  classical
  by_cases hx : x ∈ Set.range (residualCurveMorphism (k := k) m).base
  · obtain ⟨t, rfl⟩ := hx
    left
    exact ⟨(curveInPlane m).base t,
      congrArg (fun h => h.base t) (curveInPlane_intoBlowup (k := k) m)⟩
  · exact Or.inr hx

/-- The same complement as an actual open in the entire successor stage. -/
def strictAffineComplement (n m : ℕ) : (projectiveContactStage (k := k) (n + 1)).Opens :=
  ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup ''ᵁ
    affineResidualComplement m

/-- These actual whole-stage opens cover its complete affine blowup piece. -/
theorem firstChart_or_strictAffineComplement (n m : ℕ)
    (x : projectiveContactStage (k := k) (n + 1))
    (hx : x ∈ (((projectiveProductInitial (k := k)).stage n).nextAffineBlowup).opensRange) :
    x ∈ (((projectiveProductInitial (k := k)).stage (n + 1)).chart).opensRange ∨
      x ∈ strictAffineComplement n m := by
  obtain ⟨a, rfl⟩ := hx
  rcases affineResidual_cover m a with ha | ha
  · obtain ⟨t, ht⟩ := ha
    left
    refine ⟨t, ?_⟩
    change (coordinateChart (k := k) ≫
      ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup).base t = _
    exact congrArg (((projectiveProductInitial (k := k)).stage n).nextAffineBlowup).base ht
  · exact Or.inr ⟨a, ha, rfl⟩

/-- The original whole strict-transform source is empty over this actual complementary open. -/
instance strictTransform_affineComplement_isEmpty (n m : ℕ) :
    IsEmpty ((strictTransformι (k := k) (n + 1) (m + (n + 1)) ⁻¹ᵁ
      strictAffineComplement n m).toScheme) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨a, ha, heq⟩ := z.property
  have hz : z.val ∈ Set.range (residualChart (k := k) (n + 1) m).base := by
    rw [range_residualChart_affine]
    exact ⟨a, heq⟩
  obtain ⟨t, ht⟩ := hz
  change a ∉ Set.range (residualCurveMorphism (k := k) m).base at ha
  apply ha
  refine ⟨t, ?_⟩
  apply (((projectiveProductInitial (k := k)).stage n).nextAffineBlowup).isOpenEmbedding.injective
  have hw := congrArg (fun h => h.base t) (residualChart_affine_ι (k := k) n m)
  exact hw.symm.trans
    ((congrArg (strictTransformι (k := k) (n + 1) (m + (n + 1))).base ht).trans heq.symm)

private theorem emptyKernelGenerator_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsEmpty X] :
    IsIso (schemeKernelGenerator f 1 (Subsingleton.elim _ _)) := by
  apply KltDP.SheafOfModules.isIso_of_bijective_on_basis
    (B := fun U : Y.Opens => U) _
    (Opens.isBasis_iff_nbhd.mpr (fun {U x} hx => ⟨U, ⟨U, rfl⟩, hx, le_rfl⟩))
  intro U
  apply schemeKernelGenerator_app_bijective f 1 (Subsingleton.elim _ _) U
  · rw [map_one, Ideal.span_singleton_one]
    apply top_unique
    intro r _
    exact Subsingleton.elim _ _
  · rw [map_one]
    exact one_mem _

/-- The frame is a frame of the original global strict kernel, not a replacement ideal. -/
def strictAffineComplementFrame (n m : ℕ) :
    _root_.SheafOfModules.unit (strictAffineComplement (k := k) n m).toScheme.ringCatSheaf ≅
      (schemeModulePullback (strictAffineComplement (k := k) n m).ι).obj
        (schemeKernelIdeal (strictTransformι (k := k) (n + 1) (m + (n + 1)))) := by
  let f := strictTransformι (k := k) (n + 1) (m + (n + 1)) ∣_ strictAffineComplement n m
  letI := emptyKernelGenerator_isIso f
  exact asIso (schemeKernelGenerator f 1 (Subsingleton.elim _ _)) ≪≫
    localKernelToGlobalPullbackIso (strictTransformι (k := k) (n + 1) (m + (n + 1)))
      (strictAffineComplement n m)

/-- Its original ambient inclusion is exactly multiplication by one. -/
theorem strictAffineComplementFrame_inclusion (n m : ℕ) :
    (strictAffineComplementFrame (k := k) n m).hom ≫
        pulledKernelInclusion (strictTransformι (k := k) (n + 1) (m + (n + 1)))
          (strictAffineComplement (k := k) n m).ι =
      (schemeScalarEnd (Y := (strictAffineComplement (k := k) n m).toScheme) 1 :
        _root_.SheafOfModules.unit (strictAffineComplement (k := k) n m).toScheme.ringCatSheaf ⟶
          _root_.SheafOfModules.unit (strictAffineComplement (k := k) n m).toScheme.ringCatSheaf) :=
  localKernelGlobalEquation_inclusion
    (strictTransformι (k := k) (n + 1) (m + (n + 1)))
    (strictAffineComplement (k := k) n m) 1 (Subsingleton.elim _ _)

end KltDP.Examples.FrobeniusStrictTransformAffineBlowup
