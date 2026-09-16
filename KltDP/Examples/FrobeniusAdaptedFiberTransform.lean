import KltDP.Geometry.SchemeLiftOverIsoOpen
import KltDP.Geometry.SchematicImageOpenImmersion
import KltDP.Examples.FrobeniusFiberTranslation
import KltDP.Examples.FrobeniusUnaffectedFibers

/-!
# The whole-fibre strict transform on an arbitrary charted plane

The fibre analogue of `FrobeniusAdaptedStrictTransform`: an *adapted fibre* on a charted plane `A`
is a closed integral Noetherian curve `C.ι : C.curve ⟶ A.carrier` with an open parameter chart
`C.param` such that the tangent line `v = 0` of the distinguished chart is the restriction of the
curve (`fiberCurve ≫ A.chart = C.param ≫ C.ι`). The curve minus the centre lifts to every stage
(`C.lift n`), its schematic image `C.strict n` is a closed subscheme whose ideal sheaf is the generic
strict-fibre closure ideal `liftedFiberClosureIdeal A n` (`strictIdeal_eq_local`), so
`C.strict n ≅ liftedFiberClosure A n` compatibly with the inclusions and `C.strict n` is integral.

The horizontal fibre `{y = a^p}` of `P¹ ×_k P¹` is an adapted fibre on the translated tower at
`(a, a^p)` (`fiberAdaptedTranslated`), by `fiberCurve_translatedChart`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusAdaptedFiberTransform

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusBlowupContact
  FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusStrictTransformClosure
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusTranslatedCharts
  FrobeniusGraphPicardClassZeroFiber FrobeniusFiberClosure FrobeniusFiberTranslation
  FrobeniusUnaffectedFibers

variable {k : Type u} [Field k]

/-- A nonzero parameter on the fibre line is not the origin of the plane. -/
theorem fiberCurve_ne_origin (q : parameterPuncture (k := k)) :
    (fiberCurve (k := k)).base q.1 ≠ originPoint := by
  intro h
  have hu : uCoord (k := k) ∈ ((fiberCurve (k := k)).base q.1).asIdeal := by
    rw [h]
    exact centerU.property
  change (Polynomial.evalRingHom (0 : Polynomial k)) (Polynomial.C Polynomial.X) ∈ q.1.asIdeal at hu
  exact q.2 (by simpa using hu)

/-- A closed integral curve in the charted plane whose piece in the distinguished chart is the
tangent line `v = 0`, with its open parameter chart. -/
structure FiberAdapted (A : PlaneChartedScheme k) where
  curve : Scheme.{u}
  ι : curve ⟶ A.carrier
  ι_isClosedImmersion : IsClosedImmersion ι
  curve_isIntegral : IsIntegral curve
  curve_noetherianSpace : TopologicalSpace.NoetherianSpace curve
  param : Spec (CommRingCat.of (Polynomial k)) ⟶ curve
  param_isOpenImmersion : IsOpenImmersion param
  chart_curve : fiberCurve ≫ A.chart = param ≫ ι

namespace FiberAdapted

variable {A : PlaneChartedScheme k} (C : FiberAdapted A)

instance instIsClosedImmersionι : IsClosedImmersion C.ι := C.ι_isClosedImmersion
instance instIsIntegralCurve : IsIntegral C.curve := C.curve_isIntegral
instance instNoetherianCurve : TopologicalSpace.NoetherianSpace C.curve := C.curve_noetherianSpace
instance instIsOpenImmersionParam : IsOpenImmersion C.param := C.param_isOpenImmersion

/-- The curve minus the selected centre. -/
def puncture : C.curve.Opens := C.ι ⁻¹ᵁ initialPuncture A

/-- The punctured curve as a morphism to the charted plane. -/
def puncturedCurve : (C.puncture).toScheme ⟶ A.carrier := (C.puncture).ι ≫ C.ι

theorem puncturedCurve_range :
    Set.range C.puncturedCurve.base ⊆ Set.range (initialPuncture A).ι.base := by
  rintro _ ⟨z, rfl⟩
  exact ⟨⟨C.puncturedCurve.base z, z.2⟩, rfl⟩

/-- The lift of the punctured curve to the whole scheme after `n` blowups. -/
def lift (n : ℕ) : (C.puncture).toScheme ⟶ (A.stage n).carrier :=
  letI := toInitial_restrict_isIso A n
  liftOverIso (A.toInitial n) (initialPuncture A) C.puncturedCurve C.puncturedCurve_range

@[reassoc] theorem lift_projection (n : ℕ) : C.lift n ≫ A.toInitial n = C.puncturedCurve := by
  letI := toInitial_restrict_isIso A n
  exact liftOverIso_comp _ _ _ _

theorem lift_isPullback (n : ℕ) :
    IsPullback (C.lift n) (𝟙 _) (A.toInitial n) C.puncturedCurve := by
  letI := toInitial_restrict_isIso A n
  exact liftOverIso_isPullback _ _ _ _

/-- The whole-fibre strict transform at stage `n`: the schematic image of the lift. -/
abbrev strict (n : ℕ) : Scheme.{u} := SchematicImageGlued.image (C.lift n)

/-- Its closed immersion into the stage. -/
abbrev strictι (n : ℕ) : C.strict n ⟶ (A.stage n).carrier := SchematicImageGlued.inclusion (C.lift n)

instance strictι_isClosedImmersion (n : ℕ) : IsClosedImmersion (C.strictι n) :=
  SchematicImageGlued.inclusion_isClosedImmersion _

/-- The punctured curve factors through the strict transform. -/
def puncturedToStrict (n : ℕ) : (C.puncture).toScheme ⟶ C.strict n :=
  SchematicImageGlued.toImage (C.lift n)

@[reassoc] theorem puncturedToStrict_ι (n : ℕ) :
    C.puncturedToStrict n ≫ C.strictι n = C.lift n :=
  SchematicImageGlued.toImage_inclusion _

/-! ### The punctured parameter chart inside the punctured curve -/

/-- The parameter chart restricted to `D(t)`. -/
def paramCurve : (parameterPuncture (k := k)).toScheme ⟶ C.curve := parameterPuncture.ι ≫ C.param

@[reassoc] theorem paramCurve_ι :
    C.paramCurve ≫ C.ι = parameterPuncture.ι ≫ fiberCurve ≫ A.chart := by
  rw [paramCurve, Category.assoc, ← C.chart_curve]

/-- The punctured parameter chart avoids the centre. -/
theorem paramCurve_range :
    Set.range C.paramCurve.base ⊆ Set.range (C.puncture).ι.base := by
  rintro _ ⟨q, rfl⟩
  refine ⟨⟨C.paramCurve.base q, ?_⟩, rfl⟩
  change (C.paramCurve ≫ C.ι).base q ≠ A.chart.base (originPoint (k := k))
  rw [paramCurve_ι]
  change A.chart.base ((fiberCurve (k := k)).base (parameterPuncture.ι.base q)) ≠
    A.chart.base (originPoint (k := k))
  intro h
  exact fiberCurve_ne_origin q (A.chart.isOpenEmbedding.injective h)

/-- The punctured parameter chart, factored through the punctured curve. -/
def paramToPuncture : (parameterPuncture (k := k)).toScheme ⟶ (C.puncture).toScheme :=
  IsOpenImmersion.lift (C.puncture).ι C.paramCurve C.paramCurve_range

@[reassoc] theorem paramToPuncture_ι : C.paramToPuncture ≫ (C.puncture).ι = C.paramCurve :=
  IsOpenImmersion.lift_fac _ _ _

instance paramToPuncture_isOpenImmersion : IsOpenImmersion C.paramToPuncture := by
  letI : IsOpenImmersion (C.paramToPuncture ≫ (C.puncture).ι) := by
    rw [paramToPuncture_ι]
    unfold paramCurve
    infer_instance
  exact IsOpenImmersion.of_comp _ (C.puncture).ι

instance puncture_nonempty : Nonempty (C.puncture).toScheme :=
  ⟨C.paramToPuncture.base (Classical.choice inferInstance)⟩

instance puncture_isIntegral : IsIntegral (C.puncture).toScheme :=
  isIntegral_of_isOpenImmersion (C.puncture).ι

instance puncture_noetherianSpace : TopologicalSpace.NoetherianSpace (C.puncture).toScheme :=
  (C.puncture).ι.isOpenEmbedding.isInducing.noetherianSpace

/-- On the punctured parameter chart the lift is the punctured strict fibre. -/
theorem paramToPuncture_lift (n : ℕ) :
    C.paramToPuncture ≫ C.lift n = puncturedFiberResidual A n := by
  letI := toInitial_restrict_isIso A n
  have w : puncturedFiberResidual A n ≫ A.toInitial n = C.paramToPuncture ≫ C.puncturedCurve := by
    rw [puncturedFiberResidual, Category.assoc, fiberResidual_toInitial, puncturedCurve,
      paramToPuncture_ι_assoc, paramCurve_ι]
  exact (liftOverIso_eq_of_projection (A.toInitial n) (initialPuncture A) C.puncturedCurve
    C.puncturedCurve_range _ _ w).symm

/-- The strict-transform ideal equals the generic strict-fibre closure ideal. -/
theorem strictIdeal_eq_local (n : ℕ) : (C.lift n).ker = liftedFiberClosureIdeal A n := by
  rw [liftedFiberClosureIdeal, ← C.paramToPuncture_lift n]
  exact (SchematicImageOpenImmersion.ker_precompose_openImmersion C.paramToPuncture
    (C.lift n)).symm

private theorem gluedTo_eqToHom {X : Scheme.{u}} (I J : X.IdealSheafData) (h : I = J) :
    eqToHom (congrArg (fun K : X.IdealSheafData => K.glueData.glued) h) ≫ J.gluedTo =
      I.gluedTo := by
  subst J
  exact Category.id_comp _

/-- The whole-fibre strict transform is the generic strict fibre. -/
def strictIsoLocal (n : ℕ) : C.strict n ≅ liftedFiberClosure A n :=
  eqToIso (congrArg (fun I : (A.stage n).carrier.IdealSheafData => I.glueData.glued)
    (C.strictIdeal_eq_local n))

@[reassoc] theorem strictIsoLocal_hom_ι (n : ℕ) :
    (C.strictIsoLocal n).hom ≫ fiberClosureInclusion A n = C.strictι n :=
  gluedTo_eqToHom _ _ (C.strictIdeal_eq_local n)

/-- The whole-fibre strict transform is integral. -/
theorem strict_isIntegral (n : ℕ) : IsIntegral (C.strict n) := by
  letI : Nonempty (C.strict n) :=
    ⟨(C.strictIsoLocal n).inv.base (Classical.choice inferInstance)⟩
  exact isIntegral_of_isOpenImmersion (C.strictIsoLocal n).hom

/-- The support of the strict transform is the closure of the lifted punctured curve. -/
theorem range_strictι (n : ℕ) :
    Set.range (C.strictι n).base = closure (Set.range (C.lift n).base) := by
  rw [Scheme.IdealSheafData.range_gluedTo]
  exact Scheme.Hom.support_ker (C.lift n)

end FiberAdapted

/-- The horizontal fibre at height `a^p`, adapted to the translated tower at `(a, a^p)`. -/
def fiberAdaptedTranslated (p : ℕ) (a : k) : FiberAdapted (translatedInitial p a) where
  curve := projectiveSpace k 1
  ι := horizontalFiberMorphism (a ^ p)
  ι_isClosedImmersion := horizontalFiberMorphism_isClosedImmersion (a ^ p)
  curve_isIntegral := projectiveSpace_isIntegral k 1
  curve_noetherianSpace := projectiveSpace_noetherianSpace k 1
  param := (parameterTranslationIso a).hom ≫ ProjectiveLineComparison.polynomialChartMap k 0
  param_isOpenImmersion := inferInstance
  chart_curve := fiberCurve_translatedChart p a

end KltDP.Examples.FrobeniusAdaptedFiberTransform
