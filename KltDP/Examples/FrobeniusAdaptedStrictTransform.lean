import KltDP.Geometry.SchemeLiftOverIsoOpen
import KltDP.Geometry.SchematicImageOpenImmersion
import KltDP.Examples.FrobeniusClosureContact
import KltDP.Examples.FrobeniusTranslatedCharts
import KltDP.Examples.FrobeniusContactTowerInfinity

/-!
# The whole-curve strict transform on an arbitrary charted plane

The accepted whole-graph strict transform (`FrobeniusGlobalStrictTransform`) is specialised to the
origin tower. Here the construction is carried out for an arbitrary `PlaneChartedScheme A` and an
*adapted curve*: a closed integral Noetherian curve `C.ι : C.curve ⟶ A.carrier` together with an
open parameter chart `C.param : Spec k[t] ⟶ C.curve` such that the monomial curve `v = u^p` of the
distinguished plane chart is the restriction of the curve (`curveInPlane p ≫ A.chart = C.param ≫ C.ι`).
These are properties of the input curve, all proved for the Frobenius graph on the origin tower,
on the translated tower at `(a, a^p)` (characteristic `p`) and on the tower at `(∞,∞)`.

For such data: the curve minus the centre lifts to every stage of the tower (generic lift over the
accepted complement isomorphism); its schematic image `C.strict n` is a closed subscheme; when the
accumulated exponent is `p` (`m + n = p`) its ideal sheaf equals the accepted generic local closure
ideal `liftedGraphClosureIdeal A n m` — proved as in the accepted origin case through the punctured
parameter chart and the accepted kernel invariance under nonempty open restriction of an integral
source — so `C.strict n ≅ liftedGraphClosure A n m` compatibly with the inclusions, and `C.strict n`
is integral. Through this isomorphism every contact and separation statement of
`FrobeniusClosureContact` applies to the whole-curve strict transform.

No strict-transform property is assumed; the adapted-curve fields are the actual graph data.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusAdaptedStrictTransform

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
  FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusStrictTransformClosure
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusTranslatedCharts
  FrobeniusContactTowerInfinity FrobeniusGraphPicardClassPowerCharts

variable {k : Type u} [Field k]

/-- A closed integral curve in the charted plane whose piece in the distinguished chart is the
monomial curve `v = u^p`, with its open parameter chart. -/
structure CurveAdapted (A : PlaneChartedScheme k) (p : ℕ) where
  curve : Scheme.{u}
  ι : curve ⟶ A.carrier
  ι_isClosedImmersion : IsClosedImmersion ι
  curve_isIntegral : IsIntegral curve
  curve_noetherianSpace : TopologicalSpace.NoetherianSpace curve
  param : Spec (CommRingCat.of (Polynomial k)) ⟶ curve
  param_isOpenImmersion : IsOpenImmersion param
  chart_curve : curveInPlane p ≫ A.chart = param ≫ ι

namespace CurveAdapted

variable {A : PlaneChartedScheme k} {p : ℕ} (C : CurveAdapted A p)

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

/-- The whole-curve strict transform at stage `n`: the schematic image of the lift. -/
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
    C.paramCurve ≫ C.ι = parameterPuncture.ι ≫ curveInPlane p ≫ A.chart := by
  rw [paramCurve, Category.assoc, ← C.chart_curve]

/-- The punctured parameter chart avoids the centre. -/
theorem paramCurve_range :
    Set.range C.paramCurve.base ⊆ Set.range (C.puncture).ι.base := by
  rintro _ ⟨q, rfl⟩
  refine ⟨⟨C.paramCurve.base q, ?_⟩, rfl⟩
  change (C.paramCurve ≫ C.ι).base q ≠ A.chart.base (originPoint (k := k))
  rw [paramCurve_ι]
  change A.chart.base ((curveInPlane p).base (parameterPuncture.ι.base q)) ≠
    A.chart.base (originPoint (k := k))
  intro h
  exact curveInPlane_ne_origin p q (A.chart.isOpenEmbedding.injective h)

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

/-- On the punctured parameter chart the lift is the accepted punctured residual curve. -/
theorem paramToPuncture_lift (n m : ℕ) (hm : m + n = p) :
    C.paramToPuncture ≫ C.lift n = puncturedResidualCurve A n m := by
  letI := toInitial_restrict_isIso A n
  have w : puncturedResidualCurve A n m ≫ A.toInitial n = C.paramToPuncture ≫ C.puncturedCurve := by
    rw [puncturedResidualCurve, Category.assoc, A.residualCurve_toInitial, hm, puncturedCurve,
      paramToPuncture_ι_assoc, paramCurve_ι]
  exact (liftOverIso_eq_of_projection (A.toInitial n) (initialPuncture A) C.puncturedCurve
    C.puncturedCurve_range _ _ w).symm

/-- The strict-transform ideal equals the accepted generic local closure ideal. -/
theorem strictIdeal_eq_local (n m : ℕ) (hm : m + n = p) :
    (C.lift n).ker = liftedGraphClosureIdeal A n m := by
  rw [liftedGraphClosureIdeal, ← C.paramToPuncture_lift n m hm]
  exact (SchematicImageOpenImmersion.ker_precompose_openImmersion C.paramToPuncture
    (C.lift n)).symm

private theorem gluedTo_eqToHom {X : Scheme.{u}} (I J : X.IdealSheafData) (h : I = J) :
    eqToHom (congrArg (fun K : X.IdealSheafData => K.glueData.glued) h) ≫ J.gluedTo =
      I.gluedTo := by
  subst J
  exact Category.id_comp _

/-- The whole-curve strict transform is the accepted local closure. -/
def strictIsoLocal (n m : ℕ) (hm : m + n = p) : C.strict n ≅ liftedGraphClosure A n m :=
  eqToIso (congrArg (fun I : (A.stage n).carrier.IdealSheafData => I.glueData.glued)
    (C.strictIdeal_eq_local n m hm))

@[reassoc] theorem strictIsoLocal_hom_ι (n m : ℕ) (hm : m + n = p) :
    (C.strictIsoLocal n m hm).hom ≫ closureInclusion A n m = C.strictι n :=
  gluedTo_eqToHom _ _ (C.strictIdeal_eq_local n m hm)

/-- In the contact range the whole-curve strict transform is integral. -/
theorem strict_isIntegral (n m : ℕ) (hm : m + n = p) : IsIntegral (C.strict n) := by
  letI : Nonempty (C.strict n) :=
    ⟨(C.strictIsoLocal n m hm).inv.base (Classical.choice inferInstance)⟩
  exact isIntegral_of_isOpenImmersion (C.strictIsoLocal n m hm).hom

/-- The support of the strict transform is the closure of the lifted punctured curve. -/
theorem range_strictι (n : ℕ) :
    Set.range (C.strictι n).base = closure (Set.range (C.lift n).base) := by
  rw [Scheme.IdealSheafData.range_gluedTo]
  exact Scheme.Hom.support_ker (C.lift n)

end CurveAdapted

/-! ## The Frobenius graph as an adapted curve on the three towers -/

section GraphInstances

variable (p : ℕ)

theorem graph_isIntegral : IsIntegral (graph (k := k) p) := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : Nonempty (graph (k := k) p) :=
    ⟨(graphIsoProjectiveLine (k := k) p).inv.base (Classical.choice inferInstance)⟩
  exact isIntegral_of_isOpenImmersion (graphIsoProjectiveLine (k := k) p).hom

theorem graph_noetherianSpace : TopologicalSpace.NoetherianSpace (graph (k := k) p) := by
  letI := projectiveSpace_noetherianSpace k 1
  exact (graphIsoProjectiveLine (k := k) p).hom.isOpenEmbedding.isInducing.noetherianSpace

theorem lineToGraph_isIso : IsIso (lineToGraph (k := k) p) := by
  change IsIso (graphIsoProjectiveLine p).inv
  infer_instance

/-- The graph, adapted to the origin tower. -/
def graphAdaptedOrigin : CurveAdapted (projectiveProductInitial (k := k)) p where
  curve := graph p
  ι := graphι p
  ι_isClosedImmersion := graphι_isClosedImmersion p
  curve_isIntegral := graph_isIntegral p
  curve_noetherianSpace := graph_noetherianSpace p
  param := ProjectiveLineComparison.polynomialChartMap k 0 ≫ lineToGraph p
  param_isOpenImmersion := by
    letI := lineToGraph_isIso (k := k) p
    infer_instance
  chart_curve := by
    rw [Category.assoc, lineToGraph_ι]
    exact FrobeniusGlobalGraphCompatibility.curveInPlane_productChart p

/-- The graph, adapted to the tower at `(∞,∞)`. -/
def graphAdaptedInfinity : CurveAdapted (infinityInitial k) p where
  curve := graph p
  ι := graphι p
  ι_isClosedImmersion := graphι_isClosedImmersion p
  curve_isIntegral := graph_isIntegral p
  curve_noetherianSpace := graph_noetherianSpace p
  param := ProjectiveLineComparison.polynomialChartMap k 1 ≫ lineToGraph p
  param_isOpenImmersion := by
    letI := lineToGraph_isIso (k := k) p
    infer_instance
  chart_curve := by
    rw [Category.assoc, lineToGraph_ι]
    exact curveInPlane_diagonalChart p 1

/-- The graph, adapted to the translated tower at `(a, a^p)` in characteristic `p`. -/
def graphAdaptedTranslated [Fact p.Prime] [CharP k p] (a : k) :
    CurveAdapted (translatedInitial p a) p where
  curve := graph p
  ι := graphι p
  ι_isClosedImmersion := graphι_isClosedImmersion p
  curve_isIntegral := graph_isIntegral p
  curve_noetherianSpace := graph_noetherianSpace p
  param := (parameterTranslationIso a).hom ≫ ProjectiveLineComparison.polynomialChartMap k 0 ≫
    lineToGraph p
  param_isOpenImmersion := by
    letI := lineToGraph_isIso (k := k) p
    infer_instance
  chart_curve := by
    rw [Category.assoc, Category.assoc, lineToGraph_ι]
    exact curveInPlane_translatedChart p a

end GraphInstances

end KltDP.Examples.FrobeniusAdaptedStrictTransform
