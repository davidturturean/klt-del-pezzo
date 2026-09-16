import KltDP.Geometry.PrimeCurveRestrictionPicardClass
import KltDP.Geometry.CartierFrames

/-!
# The cocycle identity of the Picard-class bridge, reduced to frame coordinates

The two atlases of `i^*O_X(D)` and `O_C(D|_C)` on the cover `(i⁻¹U_c)_c` come with
frames: the pulled-back frames `i^*(1/f_c)` (`pullbackFrame`) and the restricted frames
`1/(f_c|_C)` (`restrictedFrame`). Both families transform by the image cocycle
`i.app g_cd` (`pullbackFrame_transition`, and `cartierFrame_transition` with the task-5
identity `cartierTransitionUnit_restrictCartier`). By `transitionUnits_eq_of_frames`, if
each frame has chart coordinate `1` in its atlas, the two extracted cocycles both equal the
image cocycle, and `toPic_eq_of_transitionUnits_eq` gives `[O_C(D|_C)] = [i^*O_X(D)]`.

The two frame-coordinate facts are stated as hypotheses here (`hres`, `hpull`); they are the
remaining obligations of the bridge, see `F03_RESTRICTION_ADAPTERS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

open KltDP.Geometry.TransitionUnitGluing KltDP.Geometry.TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
  (hC : C.NotInSupport D hD)

/-- The frame `1/(f_c|_C)` of `O_C(D|_C)` on a restricted chart. -/
def restrictedFrame (c : C.GenericChart D) :
    (cartierDivisorModule C.toScheme (C.restrictCartier D hD hC)).val.obj
      (op (C.chartPreimage D c.1)) :=
  cartierFrame C.toScheme (C.restrictCartier D hD hC) (C.restrictedChart D hD hC c).chart

/-- The image cocycle `i.app g_cd` on the cover `(i⁻¹U_c)_c`. -/
def imageCocycle (c d : C.GenericChart D) :
    Γ(C.toScheme, C.chartPreimage D c.1 ⊓ C.chartPreimage D d.1)ˣ :=
  Units.map (C.inclusion.app (c.1.chart.openSet ⊓ d.1.chart.openSet)).hom.toMonoidHom
    (C.chartTransitionUnit D c d)

/-- The restricted frames transform by the image cocycle. -/
theorem restrictedFrame_transition (c d : C.GenericChart D) :
    (cartierDivisorModule C.toScheme (C.restrictCartier D hD hC)).val.map
        (homOfLE (inf_le_right : C.chartPreimage D c.1 ⊓ C.chartPreimage D d.1 ≤
          C.chartPreimage D d.1)).op (C.restrictedFrame D hD hC d) =
      (C.imageCocycle D c d : Γ(C.toScheme, C.chartPreimage D c.1 ⊓ C.chartPreimage D d.1)) •
        (cartierDivisorModule C.toScheme (C.restrictCartier D hD hC)).val.map
          (homOfLE (inf_le_left : C.chartPreimage D c.1 ⊓ C.chartPreimage D d.1 ≤
            C.chartPreimage D c.1)).op (C.restrictedFrame D hD hC c) := by
  letI : Nonempty ((C.restrictedChart D hD hC c).chart.openSet ⊓
      (C.restrictedChart D hD hC d).chart.openSet : C.toScheme.Opens) :=
    ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2,
      C.genericLift_mem_chartPreimage D d.1 d.2⟩⟩
  have h := cartierFrame_transition C.toScheme (C.restrictCartier D hD hC)
    (C.restrictedChart D hD hC c).chart (C.restrictedChart D hD hC d).chart
    (C.restrictedEquation_class_eq D hD hC c d)
  refine h.trans ?_
  exact congrArg (fun u : Γ(C.toScheme, C.chartPreimage D c.1 ⊓ C.chartPreimage D d.1) =>
      u • (cartierDivisorModule C.toScheme (C.restrictCartier D hD hC)).val.map
        (homOfLE (inf_le_left : C.chartPreimage D c.1 ⊓ C.chartPreimage D d.1 ≤
          C.chartPreimage D c.1)).op (C.restrictedFrame D hD hC c))
    (congrArg Units.val (C.cartierTransitionUnit_restrictCartier D hD hC c d))

/-- If the restricted frames have chart coordinate `1`, the restricted atlas has the image
cocycle. -/
theorem transitionUnits_restricted_of_frames
    (hres : ∀ c : C.GenericChart D,
      chartEquiv C.toScheme _ (C.restrictedLocalTrivializations D hD hC) c le_rfl
        (C.restrictedFrame D hD hC c) = 1) (c d : C.GenericChart D) :
    transitionUnits C.toScheme _ (C.restrictedLocalTrivializations D hD hC) c d =
      C.imageCocycle D c d :=
  transitionUnits_eq_of_frames C.toScheme _ (C.restrictedLocalTrivializations D hD hC)
    (C.restrictedFrame D hD hC) hres (C.imageCocycle D) (C.restrictedFrame_transition D hD hC) c d

/-- If the pulled-back frames have chart coordinate `1`, the pulled-back atlas has the image
cocycle. -/
theorem transitionUnits_pullback_of_frames
    (hpull : ∀ c : C.GenericChart D,
      chartEquiv C.toScheme _ (C.pullbackLocalTrivializations D hD) c le_rfl
        (C.pullbackFrame D c) = 1) (c d : C.GenericChart D) :
    transitionUnits C.toScheme _ (C.pullbackLocalTrivializations D hD) c d =
      C.imageCocycle D c d :=
  transitionUnits_eq_of_frames C.toScheme _ (C.pullbackLocalTrivializations D hD)
    (C.pullbackFrame D) hpull (C.imageCocycle D) (C.pullbackFrame_transition D) c d

/-- **The Picard-class bridge, conditional on the two frame-coordinate facts.** -/
theorem picardClass_restrict_eq_pullback_of_frames
    (hres : ∀ c : C.GenericChart D,
      chartEquiv C.toScheme _ (C.restrictedLocalTrivializations D hD hC) c le_rfl
        (C.restrictedFrame D hD hC c) = 1)
    (hpull : ∀ c : C.GenericChart D,
      chartEquiv C.toScheme _ (C.pullbackLocalTrivializations D hD) c le_rfl
        (C.pullbackFrame D c) = 1) :
    (cartierDivisorInvertibleSheaf C.toScheme (C.restrictCartier D hD hC)).toPic =
      (pullbackInvertibleSheaf C.inclusion (cartierDivisorInvertibleSheaf X.toScheme D)).toPic := by
  symm
  apply C.toPic_eq_of_transitionUnits_eq D hD hC
  funext c d
  rw [C.transitionUnits_pullback_of_frames D hD hpull c d,
    C.transitionUnits_restricted_of_frames D hD hC hres c d]

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
