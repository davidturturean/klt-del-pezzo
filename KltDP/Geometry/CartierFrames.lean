import KltDP.Geometry.PrimeCurveCartierRestriction
import KltDP.Geometry.SchemeModuleFunctorial
import KltDP.Geometry.TransitionUnitExtraction
import KltDP.Geometry.CartierEquationUnits

/-!
# Frames of `O(D)`, their pullbacks, and transition units from frames

The frame of `O(D)` on an equation chart `(U, f)` is the section `1/f`
(`cartierFrame`, the accepted coordinate map applied to `1`). Two frames differ on the
overlap of their charts by the accepted `cartierTransitionUnit` (`cartierFrame_transition`).

Along any morphism `f : Y ⟶ X`, sections of a module sheaf `M` pull back to sections of
`f^*M` through the unit of the accepted pullback/pushforward adjunction
(`pullbackSection`); this is natural in the open and `f.app`-semilinear. Hence the
pulled-back frames of `O_X(D)` along a prime curve `i : C → X` transform by the image
cocycle `i.app g` (`pullbackFrame_transition`).

Finally, the transition units extracted from any covering atlas are determined by frames:
if `σ_i` are sections with chart coordinate `1` and `σ_j|_{ij} = g_ij • σ_i|_{ij}`, then the
extracted units are the `g_ij` (`transitionUnits_eq_of_frames`). Identifying the
pulled-back frames with the frames of the pulled-back atlas of `i^*O_X(D)` is the
remaining step of the Picard-class bridge; see `F03_RESTRICTION_ADAPTERS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry

open TransitionUnitGluing TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Frames

variable (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)

/-- The frame `1/f` of `O(D)` on an equation chart `(U, f)`. -/
def cartierFrame (c : CartierEquationChart X D) :
    (cartierDivisorModule X D).val.obj (op c.openSet) :=
  cartierEquationSectionEquivOn X D c.openSet c.equation c.represents (Over.mk (𝟙 c.openSet)) 1

/-- The frame has rational value `f⁻¹`. -/
theorem cartierFrame_field (c : CartierEquationChart X D) :
    rationalFunctionModuleSectionsEquiv X c.openSet (cartierFrame X D c).val =
      ((c.equation⁻¹ : X.functionFieldˣ) : X.functionField) := by
  haveI : Nonempty (Over.mk (𝟙 c.openSet) : Over c.openSet).left := c.nonempty
  refine (cartierEquationSectionEquivOn_apply_field X D c.openSet c.equation c.represents
    (Over.mk (𝟙 c.openSet)) 1).trans ?_
  exact (congrArg (· * _) ((X.germToFunctionField _).hom.map_one)).trans (one_mul _)

/-- On the overlap of two charts, the frame of the second is the Cartier transition unit
times the frame of the first: `1/f_d = (f_c/f_d) • (1/f_c)`. -/
theorem cartierFrame_transition (c d : CartierEquationChart X D)
    [Nonempty (c.openSet ⊓ d.openSet : X.Opens)]
    (hcd : cartierEquationClassHom X (c.openSet ⊓ d.openSet) (Additive.ofMul c.equation) =
      cartierEquationClassHom X (c.openSet ⊓ d.openSet) (Additive.ofMul d.equation)) :
    (cartierDivisorModule X D).val.map
        (homOfLE (inf_le_right : c.openSet ⊓ d.openSet ≤ d.openSet)).op (cartierFrame X D d) =
      (cartierTransitionUnit X (c.openSet ⊓ d.openSet) c.equation d.equation hcd :
          Γ(X, c.openSet ⊓ d.openSet)) •
        (cartierDivisorModule X D).val.map
          (homOfLE (inf_le_left : c.openSet ⊓ d.openSet ≤ c.openSet)).op (cartierFrame X D c) := by
  apply Subtype.ext
  apply (rationalFunctionModuleSectionsEquiv X (c.openSet ⊓ d.openSet)).injective
  have hL : rationalFunctionModuleSectionsEquiv X (c.openSet ⊓ d.openSet)
      ((cartierDivisorModule X D).val.map
        (homOfLE (inf_le_right : c.openSet ⊓ d.openSet ≤ d.openSet)).op (cartierFrame X D d)).val =
      ((d.equation⁻¹ : X.functionFieldˣ) : X.functionField) := by
    change rationalFunctionModuleSectionsEquiv X (c.openSet ⊓ d.openSet)
      ((rationalFunctionModule X).val.map
        (homOfLE (inf_le_right : c.openSet ⊓ d.openSet ≤ d.openSet)).op (cartierFrame X D d).val) = _
    rw [rationalFunctionModuleSectionsEquiv_naturality, cartierFrame_field]
  have hu : algebraMap Γ(X, c.openSet ⊓ d.openSet) X.functionField
      (cartierTransitionUnit X (c.openSet ⊓ d.openSet) c.equation d.equation hcd :
        Γ(X, c.openSet ⊓ d.openSet)) =
      ((c.equation / d.equation : X.functionFieldˣ) : X.functionField) :=
    congrArg Units.val (map_cartierTransitionUnit X (c.openSet ⊓ d.openSet) c.equation d.equation hcd)
  have hR : rationalFunctionModuleSectionsEquiv X (c.openSet ⊓ d.openSet)
      ((cartierTransitionUnit X (c.openSet ⊓ d.openSet) c.equation d.equation hcd :
          Γ(X, c.openSet ⊓ d.openSet)) •
        (cartierDivisorModule X D).val.map
          (homOfLE (inf_le_left : c.openSet ⊓ d.openSet ≤ c.openSet)).op (cartierFrame X D c)).val =
      ((d.equation⁻¹ : X.functionFieldˣ) : X.functionField) := by
    change rationalFunctionModuleSectionsEquiv X (c.openSet ⊓ d.openSet)
      ((cartierTransitionUnit X (c.openSet ⊓ d.openSet) c.equation d.equation hcd :
          Γ(X, c.openSet ⊓ d.openSet)) •
        (rationalFunctionModule X).val.map
          (homOfLE (inf_le_left : c.openSet ⊓ d.openSet ≤ c.openSet)).op (cartierFrame X D c).val) = _
    rw [LinearEquiv.map_smul, Algebra.smul_def, rationalFunctionModuleSectionsEquiv_naturality,
      cartierFrame_field, hu, ← Units.val_mul]
    congr 1
    rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel, one_mul]
  exact hL.trans hR.symm

end Frames

section PullbackSections

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)

/-- Pullback of a section of `M` over `U` to a section of `f^*M` over `f⁻¹U`, through the unit
of the accepted pullback/pushforward adjunction. -/
def pullbackSection (U : X.Opens) (s : M.val.obj (op U)) :
    ((schemeModulePullback f).obj M).val.obj (op (f ⁻¹ᵁ U)) :=
  ((schemeModulePullbackPushforwardAdjunction f).unit.app M).val.app (op U) s

/-- Pulling back sections commutes with restriction. -/
theorem pullbackSection_res {U V : X.Opens} (h : V ≤ U) (s : M.val.obj (op U)) :
    ((schemeModulePullback f).obj M).val.map ((Opens.map f.base).map (homOfLE h)).op
        (pullbackSection f M U s) =
      pullbackSection f M V (M.val.map (homOfLE h).op s) :=
  (PresheafOfModules.naturality_apply
    ((schemeModulePullbackPushforwardAdjunction f).unit.app M).val (homOfLE h).op s).symm

/-- Pulling back sections is `f.app`-semilinear. -/
theorem pullbackSection_smul (U : X.Opens) (a : Γ(X, U)) (s : M.val.obj (op U)) :
    pullbackSection f M U (a • s) = f.app U a • pullbackSection f M U s :=
  (((schemeModulePullbackPushforwardAdjunction f).unit.app M).val.app (op U)).hom.map_smul a s

end PullbackSections

section FramesUniqueness

variable (X : Scheme.{u}) (M : X.Modules)
  (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)

/-- Transition units are determined by frames: sections `σ i` over the charts with chart
coordinate `1`, transforming by `g` on overlaps, force the extracted units to be `g`. -/
theorem transitionUnits_eq_of_frames (σ : ∀ i : t.I, M.val.obj (op (t.X i)))
    (hσ : ∀ i, chartEquiv X M t i le_rfl (σ i) = 1)
    (g : ∀ i j : t.I, Γ(X, t.X i ⊓ t.X j)ˣ)
    (hg : ∀ i j : t.I, M.val.map (homOfLE (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).op (σ j) =
      (g i j : Γ(X, t.X i ⊓ t.X j)) •
        M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i))
    (i j : t.I) : transitionUnits X M t i j = g i j := by
  have h := transitionUnits_mul_chart X M t i j (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)
    (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)
    (M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i))
  have hresi : chartEquiv X M t i (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)
      (M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i)) =
      res X (inf_le_left : t.X i ⊓ t.X j ≤ t.X i) (chartEquiv X M t i le_rfl (σ i)) :=
    chartEquiv_restrict X M t i (inf_le_left : t.X i ⊓ t.X j ≤ t.X i) (le_rfl : t.X i ≤ t.X i) (σ i)
  have hi : chartEquiv X M t i (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)
      (M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i)) = 1 :=
    hresi.trans ((congrArg (fun x => res X (inf_le_left : t.X i ⊓ t.X j ≤ t.X i) x) (hσ i)).trans
      (map_one (res X (inf_le_left : t.X i ⊓ t.X j ≤ t.X i))))
  have hresj : chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)
      (M.val.map (homOfLE (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).op (σ j)) =
      res X (inf_le_right : t.X i ⊓ t.X j ≤ t.X j) (chartEquiv X M t j le_rfl (σ j)) :=
    chartEquiv_restrict X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j) (le_rfl : t.X j ≤ t.X j) (σ j)
  have hj1 : chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)
      (M.val.map (homOfLE (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).op (σ j)) = 1 :=
    hresj.trans ((congrArg (fun x => res X (inf_le_right : t.X i ⊓ t.X j ≤ t.X j) x) (hσ j)).trans
      (map_one (res X (inf_le_right : t.X i ⊓ t.X j ≤ t.X j))))
  have hσi : M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i) =
      (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) •
        M.val.map (homOfLE (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).op (σ j) :=
    calc M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i)
        = (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) •
            ((g i j : Γ(X, t.X i ⊓ t.X j)) •
              M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i)) :=
          (inv_smul_smul (g i j)
            (M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i))).symm
      _ = (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) •
            M.val.map (homOfLE (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).op (σ j) :=
          congrArg (fun x => (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) • x)
            (hg i j).symm
  have hj : chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)
      (M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i)) =
      (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) :=
    calc chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)
          (M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i))
        = chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)
            ((((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) •
              M.val.map (homOfLE (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).op (σ j)) :=
          congrArg (fun x => chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j) x) hσi
      _ = (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) •
            chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)
              (M.val.map (homOfLE (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).op (σ j)) :=
          (chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).map_smul _ _
      _ = (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) * 1 :=
          congrArg (fun x => (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) * x) hj1
      _ = (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) := mul_one _
  have hA : res X (le_inf (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)
      (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)) (transitionUnits X M t i j : Γ(X, t.X i ⊓ t.X j)) =
      (transitionUnits X M t i j : Γ(X, t.X i ⊓ t.X j)) :=
    res_self X _ _
  have h2 : (transitionUnits X M t i j : Γ(X, t.X i ⊓ t.X j)) *
      (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) = 1 :=
    (congrArg₂ (· * ·) hA.symm hj.symm).trans (h.trans hi)
  exact Units.ext (Units.mul_inv_eq_one.mp h2)

end FramesUniqueness

end KltDP.Geometry

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme)

/-- The pullback along `i : C → X` of the frame `1/f_c` of `O_X(D)` on a generic chart. -/
def pullbackFrame (c : C.GenericChart D) :
    ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)).val.obj
      (op (C.chartPreimage D c.1)) :=
  pullbackSection C.inclusion (cartierDivisorModule X.toScheme D) c.1.chart.openSet
    (cartierFrame X.toScheme D c.1.chart)

/-- The pulled-back frames transform by the image cocycle `i.app g_cd`. -/
theorem pullbackFrame_transition (c d : C.GenericChart D) :
    ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)).val.map
        ((Opens.map C.inclusion.base).map
          (homOfLE (inf_le_right : c.1.chart.openSet ⊓ d.1.chart.openSet ≤ d.1.chart.openSet))).op
        (C.pullbackFrame D d) =
      C.inclusion.app (c.1.chart.openSet ⊓ d.1.chart.openSet)
          (C.chartTransitionUnit D c d : Γ(X.toScheme, c.1.chart.openSet ⊓ d.1.chart.openSet)) •
        ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)).val.map
          ((Opens.map C.inclusion.base).map
            (homOfLE (inf_le_left : c.1.chart.openSet ⊓ d.1.chart.openSet ≤ c.1.chart.openSet))).op
          (C.pullbackFrame D c) := by
  letI : Nonempty (c.1.chart.openSet ⊓ d.1.chart.openSet : X.toScheme.Opens) :=
    ⟨⟨C.genericPoint, c.2, d.2⟩⟩
  rw [pullbackFrame, pullbackFrame, pullbackSection_res, pullbackSection_res,
    cartierFrame_transition X.toScheme D c.1.chart d.1.chart (C.chart_class_eq_on_inf D c d),
    pullbackSection_smul]
  rfl

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
