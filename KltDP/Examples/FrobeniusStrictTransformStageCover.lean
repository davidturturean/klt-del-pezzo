import KltDP.Examples.FrobeniusStrictTransformContact
import KltDP.Geometry.SchemeKernelOpenPullback
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# An actual open cover of the entire strict-transform stage

The residual curve is closed in the inverse image of the entire original
affine plane: its composite with the separated projection to that plane
is the original closed monomial curve. The actual strict-transform ideal
is already proved to be the kernel of this residual curve. Consequently
every strict-transform point over the original plane lies in the current
first chart. Points outside that inverse image avoid the original center.

This proves the whole-stage cover by the current first chart, the actual
strict-curve complement, and the original stage puncture. The complement
has empty restricted strict source, so the original strict kernel has a
unit frame there, normalized by its original ambient inclusion.

The first-chart and stage-puncture frames can be assembled on this cover
separately. This module asserts no whole-stage invertibility, exceptional
multiplicity, tensor factorization, or divisor-class formula.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStrictTransformStageCover

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusStrictTransformClosure FrobeniusGlobalStrictTransform
open FrobeniusStageComplement.PlaneChartedScheme

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The inverse image of the whole original plane under the actual stage projection. -/
def initialPlaneOpen (A : PlaneChartedScheme k) (n : ℕ) : (A.stage n).carrier.Opens :=
  A.toInitial n ⁻¹ᵁ A.chart.opensRange

/-- The original restricted projection, with the original plane-chart isomorphism. -/
def initialPlaneProjection (A : PlaneChartedScheme k) (n : ℕ) :
    (initialPlaneOpen A n).toScheme ⟶ plane k :=
  (A.toInitial n ∣_ A.chart.opensRange) ≫ A.chart.isoOpensRange.inv

/-- This map retains the actual morphism to the initial whole scheme. -/
@[reassoc] theorem initialPlaneProjection_chart (A : PlaneChartedScheme k) (n : ℕ) :
    initialPlaneProjection A n ≫ A.chart = (initialPlaneOpen A n).ι ≫ A.toInitial n := by
  rw [initialPlaneProjection, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp,
    morphismRestrict_ι]
  rfl

/-- Separatedness is inherited from the proved proper finite-stage projection. -/
instance initialPlaneProjection_isSeparated (A : PlaneChartedScheme k) (n : ℕ) :
    IsSeparated (initialPlaneProjection A n) := by
  letI : IsSeparated (A.toInitial n ∣_ A.chart.opensRange) :=
    IsLocalAtTarget.restrict (inferInstance : IsSeparated (A.toInitial n)) _
  unfold initialPlaneProjection
  infer_instance

private theorem residualCurve_range_initialPlane (A : PlaneChartedScheme k) (n m : ℕ) :
    Set.range (A.residualCurve n m).base ⊆ Set.range (initialPlaneOpen A n).ι.base := by
  rintro _ ⟨t, rfl⟩
  refine ⟨⟨(A.residualCurve n m).base t, ?_⟩, rfl⟩
  change (A.residualCurve n m ≫ A.toInitial n).base t ∈ A.chart.opensRange
  rw [A.residualCurve_toInitial]
  exact ⟨(curveInPlane (m + n)).base t, rfl⟩

/-- The actual residual curve factored through that entire inverse-image open. -/
def initialPlaneResidual (A : PlaneChartedScheme k) (n m : ℕ) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ (initialPlaneOpen A n).toScheme :=
  IsOpenImmersion.lift (initialPlaneOpen A n).ι (A.residualCurve n m)
    (residualCurve_range_initialPlane A n m)

@[reassoc] theorem initialPlaneResidual_ι (A : PlaneChartedScheme k) (n m : ℕ) :
    initialPlaneResidual A n m ≫ (initialPlaneOpen A n).ι = A.residualCurve n m :=
  IsOpenImmersion.lift_fac _ _ _

/-- The original residual lift projects to the original closed monomial curve. -/
@[reassoc] theorem initialPlaneResidual_projection (A : PlaneChartedScheme k) (n m : ℕ) :
    initialPlaneResidual A n m ≫ initialPlaneProjection A n = curveInPlane (m + n) := by
  apply (cancel_mono A.chart).mp
  rw [Category.assoc, initialPlaneProjection_chart, ← Category.assoc,
    initialPlaneResidual_ι, A.residualCurve_toInitial]

/-- Closedness holds over the whole original affine plane, including all its Rees pieces. -/
instance initialPlaneResidual_isClosedImmersion (A : PlaneChartedScheme k) (n m : ℕ) :
    IsClosedImmersion (initialPlaneResidual A n m) := by
  letI : IsClosedImmersion (initialPlaneResidual A n m ≫ initialPlaneProjection A n) := by
    rw [initialPlaneResidual_projection]
    infer_instance
  exact IsClosedImmersion.of_comp (initialPlaneResidual A n m) (initialPlaneProjection A n)

/-- This support identity is derived from the original strict ideal's proved kernel equality. -/
private theorem strictTransform_range_residual (n m : ℕ) :
    Set.range (strictTransformι (k := k) n (m + n)).base =
      closure (Set.range ((projectiveProductInitial (k := k)).residualCurve n m).base) := by
  change Set.range (strictTransformIdeal (k := k) n (m + n)).gluedTo.base = _
  rw [Scheme.IdealSheafData.range_gluedTo, strictTransformIdeal_eq_local,
    liftedGraphClosureIdeal_eq]
  exact Scheme.Hom.support_ker _

/-- Every original strict-transform point over the initial plane is in the current first chart. -/
theorem strictTransform_initialPlane_mem_chart (n m : ℕ)
    (x : projectiveContactStage (k := k) n)
    (hx : x ∈ Set.range (strictTransformι n (m + n)).base)
    (hplane : x ∈ initialPlaneOpen (projectiveProductInitial (k := k)) n) :
    x ∈ ((projectiveProductInitial (k := k)).stage n).chart.opensRange := by
  let A := projectiveProductInitial (k := k)
  let z : (initialPlaneOpen A n).toScheme := ⟨x, hplane⟩
  have hz : z ∈ (initialPlaneOpen A n).ι.base ⁻¹'
      closure (Set.range (initialPlaneResidual A n m ≫ (initialPlaneOpen A n).ι).base) := by
    change x ∈ closure
      (Set.range (initialPlaneResidual A n m ≫ (initialPlaneOpen A n).ι).base)
    rw [initialPlaneResidual_ι, ← strictTransform_range_residual]
    exact hx
  rw [ReducedClosedImageChart.preimage_closure_range] at hz
  obtain ⟨t, ht⟩ := hz
  refine ⟨(curveInPlane m).base t, ?_⟩
  change (A.residualCurve n m).base t = x
  rw [← initialPlaneResidual_ι A n m]
  exact congrArg (initialPlaneOpen A n).ι.base ht

/-- Every point of the original strict curve is in the current chart or the proved puncture. -/
theorem strictTransform_chart_or_puncture (n m : ℕ)
    (x : projectiveContactStage (k := k) n)
    (hx : x ∈ Set.range (strictTransformι n (m + n)).base) :
    x ∈ ((projectiveProductInitial (k := k)).stage n).chart.opensRange ∨
      x ∈ stagePuncture (projectiveProductInitial (k := k)) n := by
  by_cases hplane : x ∈ initialPlaneOpen (projectiveProductInitial (k := k)) n
  · exact Or.inl (strictTransform_initialPlane_mem_chart n m x hx hplane)
  · right
    change ((projectiveProductInitial (k := k)).toInitial n).base x ≠
      (projectiveProductInitial (k := k)).chart.base originPoint
    intro heq
    apply hplane
    change ((projectiveProductInitial (k := k)).toInitial n).base x ∈
      (projectiveProductInitial (k := k)).chart.opensRange
    exact ⟨originPoint, heq.symm⟩

/-- The complement of the original closed strict curve in the entire stage. -/
def strictCurveComplement (n m : ℕ) : (projectiveContactStage (k := k) n).Opens :=
  ⟨(Set.range (strictTransformι n (m + n)).base)ᶜ,
    (strictTransformι n (m + n)).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The three actual opens cover the entire stage, not only its affine blowup piece. -/
theorem strictStage_cover (n m : ℕ) (x : projectiveContactStage (k := k) n) :
    x ∈ ((projectiveProductInitial (k := k)).stage n).chart.opensRange ∨
      x ∈ strictCurveComplement n m ∨
        x ∈ stagePuncture (projectiveProductInitial (k := k)) n := by
  by_cases hx : x ∈ Set.range (strictTransformι (k := k) n (m + n)).base
  · rcases strictTransform_chart_or_puncture n m x hx with hc | hp
    · exact Or.inl hc
    · exact Or.inr (Or.inr hp)
  · exact Or.inr (Or.inl hx)

/-- The same cover as equality of the actual ambient opens. -/
theorem strictStage_opens_sup (n m : ℕ) :
    ((projectiveProductInitial (k := k)).stage n).chart.opensRange ⊔
      strictCurveComplement n m ⊔ stagePuncture (projectiveProductInitial (k := k)) n = ⊤ := by
  apply top_unique
  intro x _
  rcases strictStage_cover n m x with hc | hs | hp
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hs)
  · exact Or.inr hp

instance strictTransform_curveComplement_isEmpty (n m : ℕ) :
    IsEmpty ((strictTransformι (k := k) n (m + n) ⁻¹ᵁ strictCurveComplement n m).toScheme) := by
  refine ⟨fun z => ?_⟩
  exact z.property ⟨z.val, rfl⟩

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

/-- The unit frame is a frame of the original global strict kernel on its actual complement. -/
def strictCurveComplementFrame (n m : ℕ) :
    _root_.SheafOfModules.unit (strictCurveComplement (k := k) n m).toScheme.ringCatSheaf ≅
      (schemeModulePullback (strictCurveComplement (k := k) n m).ι).obj
        (schemeKernelIdeal (strictTransformι n (m + n))) := by
  let f := strictTransformι (k := k) n (m + n) ∣_ strictCurveComplement n m
  letI := emptyKernelGenerator_isIso f
  exact asIso (schemeKernelGenerator f 1 (Subsingleton.elim _ _)) ≪≫
    localKernelToGlobalPullbackIso (strictTransformι n (m + n)) (strictCurveComplement n m)

/-- Its actual inclusion is multiplication by one under the canonical unit comparison. -/
theorem strictCurveComplementFrame_inclusion (n m : ℕ) :
    (strictCurveComplementFrame (k := k) n m).hom ≫
        pulledKernelInclusion (strictTransformι n (m + n)) (strictCurveComplement n m).ι =
      (schemeScalarEnd (Y := (strictCurveComplement (k := k) n m).toScheme) 1 :
        _root_.SheafOfModules.unit (strictCurveComplement (k := k) n m).toScheme.ringCatSheaf ⟶
          _root_.SheafOfModules.unit (strictCurveComplement (k := k) n m).toScheme.ringCatSheaf) :=
  localKernelGlobalEquation_inclusion (strictTransformι n (m + n))
    (strictCurveComplement n m) 1 (Subsingleton.elim _ _)

end KltDP.Examples.FrobeniusStrictTransformStageCover
