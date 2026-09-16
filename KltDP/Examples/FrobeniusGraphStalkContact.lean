import KltDP.Examples.FrobeniusGraphContact
import KltDP.Examples.FrobeniusGraphClosed
import KltDP.Geometry.SurfaceRegularCharts

/-!
# Fiber contact in the actual projective graph's scheme stalk

The polynomial chart is an actual open immersion into the constructed graph
scheme. Its prime `(t-a)` is proved to map to the previously constructed
rational product point. The existing open-immersion stalk equivalence
identifies this graph stalk with the actual localization `k[t]_(t-a)`.

The fiber germ is obtained from the actual pulled polynomial's Spec germ by
the inverse chart stalk map. A separate formula identifies it with the stalk
pullback of the actual second-coordinate fiber section. Quotient length is
then transported through the proved ring equivalence, using the pinned ideal
order equivalence and `Module.length_quotient`.

No stalk isomorphism or contact multiplicity is assumed. This does not yet
construct the successive blowups or their strict transforms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u v

namespace KltDP.Examples.FrobeniusGraphStalkContact

open KltDP.Geometry ProjectiveChart FrobeniusProjectivePoints
  FrobeniusProjectiveMorphism FrobeniusGraphClosed FrobeniusGraphContact

variable {k : Type u} [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Length of a principal quotient is preserved under an actual change of ring
by a ring equivalence. Both module scalar rings are displayed in the statement. -/
theorem quotient_span_length_eq_of_ringEquiv {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (e : R ≃+* S) (r : R) :
    Module.length R (R ⧸ Ideal.span {r}) =
      Module.length S (S ⧸ Ideal.span {e r}) := by
  rw [Module.length_quotient, Module.length_quotient]
  have h := Order.coheight_orderIso
    (Ideal.relIsoOfBijective e.toRingHom e.bijective).symm (Ideal.span {r})
  change Order.coheight (Ideal.map e.toRingHom (Ideal.span {r})) =
    Order.coheight (Ideal.span {r}) at h
  rw [Ideal.map_span, Set.image_singleton] at h
  exact h.symm

/-- The actual projective-chart ring is identified with the polynomial ring. -/
def chartPolynomialEquiv : chartRing k 1 ≃+* Polynomial k :=
  (coordinateRingEquiv k 1).trans parameterPolynomialEquiv.toRingEquiv

/-- The polynomial affine chart of the actual projective line. -/
def polynomialLineChart : Spec (CommRingCat.of (Polynomial k)) ⟶ projectiveSpace k 1 :=
  Spec.map chartPolynomialEquiv.toCommRingCatIso.hom ≫ chartMorphism k 1

instance polynomialLineChart_isOpenImmersion : IsOpenImmersion (polynomialLineChart (k := k)) := by
  unfold polynomialLineChart
  infer_instance

theorem polynomialLineChart_eq :
    polynomialLineChart (k := k) =
      Spec.map parameterPolynomialEquiv.toRingEquiv.toCommRingCatIso.hom ≫
        parameterMorphism 1 := by
  have h : chartPolynomialEquiv.toCommRingCatIso.hom =
      CommRingCat.ofHom (parameterMap (k := k) 1) ≫
        parameterPolynomialEquiv.toRingEquiv.toCommRingCatIso.hom := by
    rw [parameterMap_one]
    rfl
  rw [polynomialLineChart, h, Spec.map_comp, Category.assoc]
  rfl

/-- The corresponding actual polynomial open chart of the graph scheme. -/
def polynomialGraphChart (p : ℕ) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ graph (k := k) p :=
  polynomialLineChart ≫ (graphIsoProjectiveLine p).inv

instance polynomialGraphChart_isOpenImmersion (p : ℕ) :
    IsOpenImmersion (polynomialGraphChart (k := k) p) := by
  unfold polynomialGraphChart
  infer_instance

/-- The chart's inclusion into the product is the previously constructed affine graph. -/
theorem polynomialGraphChart_inclusion (p : ℕ) :
    polynomialGraphChart (k := k) p ≫ graphι p =
      Spec.map parameterPolynomialEquiv.toRingEquiv.toCommRingCatIso.hom ≫
        affineGraphMorphism p := by
  simp only [polynomialGraphChart, Category.assoc, graphIso_inv_ι,
    polynomialLineChart_eq, parameterMorphism_projectiveGraphMorphism]

/-- The prime in the actual polynomial affine scheme corresponding to `t=a`. -/
def parameterSchemePoint (a : k) : Spec (CommRingCat.of (Polynomial k)) :=
  ⟨parameterPointIdeal a, inferInstance⟩

theorem polynomialEvaluation_point (a : k) :
    fieldMorphismPoint (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) =
      parameterSchemePoint a := by
  apply PrimeSpectrum.ext
  change Ideal.comap (Polynomial.evalRingHom a) (IsLocalRing.maximalIdeal k) =
    parameterPointIdeal a
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
    Polynomial.ker_evalRingHom]
  rfl

theorem parameterEvaluation_via_polynomial (a : k) :
    (Polynomial.evalRingHom a).comp parameterPolynomialEquiv.toRingHom =
      parameterEvaluation a := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [RingHom.comp_apply, parameterEvaluation]
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [RingHom.comp_apply, parameterEvaluation]

/-- Evaluation in the new chart gives exactly the existing rational product-point morphism. -/
theorem polynomialGraphChart_evaluation_inclusion (p : ℕ) (a : k) :
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫ polynomialGraphChart p) ≫
        graphι p = graphPointMorphism p a := by
  have h : parameterPolynomialEquiv.toRingEquiv.toCommRingCatIso.hom ≫
      CommRingCat.ofHom (Polynomial.evalRingHom a) =
        CommRingCat.ofHom (parameterEvaluation a) :=
    CommRingCat.hom_ext (parameterEvaluation_via_polynomial a)
  rw [Category.assoc, polynomialGraphChart_inclusion, ← Category.assoc, ← Spec.map_comp, h]
  exact affineGraphMorphism_evaluation p a

/-- The selected point on the actual graph scheme. -/
def pointOnGraph (p : ℕ) (a : k) : graph (k := k) p :=
  (polynomialGraphChart p).base (parameterSchemePoint a)

/-- Its image is the previously proved rational point `(a,a^p)` in the product. -/
theorem pointOnGraph_inclusion (p : ℕ) (a : k) :
    (graphι p).base (pointOnGraph p a) = graphPoint p a := by
  rw [pointOnGraph, ← polynomialEvaluation_point]
  change fieldMorphismPoint
    ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫ polynomialGraphChart p) ≫
      graphι p) = graphPoint p a
  rw [polynomialGraphChart_evaluation_inclusion]
  rfl

/-- The chart's actual stalk-map equivalence. -/
def graphChartStalkEquiv (p : ℕ) (a : k) :
    (graph p).presheaf.stalk (pointOnGraph p a) ≃+*
      (Spec (CommRingCat.of (Polynomial k))).presheaf.stalk (parameterSchemePoint a) :=
  (asIso ((polynomialGraphChart p).stalkMap (parameterSchemePoint a))).commRingCatIsoToRingEquiv

/-- The existing chart/localization equivalence, specialized to the actual graph and point. -/
def graphStalkLocalEquiv (p : ℕ) (a : k) :
    (graph p).presheaf.stalk (pointOnGraph p a) ≃+* parameterLocalRing a :=
  openImmersionStalkLocalizationEquiv (polynomialGraphChart p) (parameterSchemePoint a)

/-- The actual fiber germ on the graph, obtained by inverse chart restriction of its pulled section. -/
def graphFiberGerm (p : ℕ) (a : k) : (graph p).presheaf.stalk (pointOnGraph p a) :=
  (graphChartStalkEquiv p a).symm
    (StructureSheaf.toStalk (Polynomial k) (parameterSchemePoint a)
      (parameterPolynomialEquiv (pulledFiberEquation p a)))

theorem graphFiberGerm_stalkMap (p : ℕ) (a : k) :
    (polynomialGraphChart p).stalkMap (parameterSchemePoint a) (graphFiberGerm p a) =
      StructureSheaf.toStalk (Polynomial k) (parameterSchemePoint a)
        (parameterPolynomialEquiv (pulledFiberEquation p a)) :=
  (graphChartStalkEquiv p a).apply_symm_apply _

/-- The actual second-coordinate chart ring map in polynomial parameter coordinates. -/
def secondChartRingMap (p : ℕ) : chartRing k 1 →+* Polynomial k :=
  parameterPolynomialEquiv.toRingHom.comp (parameterMap p)

def secondChartMorphism (p : ℕ) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ Spec (CommRingCat.of (chartRing k 1)) :=
  Spec.map (CommRingCat.ofHom (secondChartRingMap p))

/-- This chart morphism is the actual second projection of the graph inclusion. -/
theorem polynomialGraphChart_secondProjection (p : ℕ) :
    (polynomialGraphChart (k := k) p ≫ graphι p) ≫ secondProjection =
      secondChartMorphism p ≫ chartMorphism k 1 := by
  rw [polynomialGraphChart_inclusion, Category.assoc, affineGraph_secondProjection,
    ← Category.assoc, ← Spec.map_comp]
  rfl

/-- The germ is the stalk pullback of the original fiber equation, as checked on the actual chart. -/
theorem graphFiberGerm_pullback (p : ℕ) (a : k) :
    (polynomialGraphChart p).stalkMap (parameterSchemePoint a) (graphFiberGerm p a) =
      (secondChartMorphism p).stalkMap (parameterSchemePoint a)
        (StructureSheaf.toStalk (chartRing k 1)
          ((secondChartMorphism p).base (parameterSchemePoint a)) (fiberEquation (a ^ p))) := by
  rw [graphFiberGerm_stalkMap]
  exact (AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom (secondChartRingMap p))
    (parameterSchemePoint a) (fiberEquation (a ^ p))).symm

/-- The stalk equivalence sends the actual fiber germ to the previously calculated local section. -/
theorem graphStalkLocalEquiv_fiberGerm (p : ℕ) (a : k) :
    graphStalkLocalEquiv p a (graphFiberGerm p a) = localPulledFiberEquation p a := by
  change specStalkLocalizationEquiv (Polynomial k) (parameterSchemePoint a)
      (graphChartStalkEquiv p a ((graphChartStalkEquiv p a).symm
        (StructureSheaf.toStalk (Polynomial k) (parameterSchemePoint a)
          (parameterPolynomialEquiv (pulledFiberEquation p a))))) = _
  rw [RingEquiv.apply_symm_apply]
  exact StructureSheaf.stalkToFiberRingHom_toStalk (Polynomial k) (parameterSchemePoint a)
    (parameterPolynomialEquiv (pulledFiberEquation p a))

/-- The actual projective graph stalk quotient by the actual fiber germ has length `p`. -/
theorem graphStalk_contact_length (p : ℕ) [Fact p.Prime] [CharP k p] (a : k) :
    Module.length ((graph p).presheaf.stalk (pointOnGraph p a))
      ((graph p).presheaf.stalk (pointOnGraph p a) ⧸ Ideal.span {graphFiberGerm p a}) = p := by
  rw [quotient_span_length_eq_of_ringEquiv (graphStalkLocalEquiv p a),
    graphStalkLocalEquiv_fiberGerm]
  exact localContactAlgebra_length p a

end KltDP.Examples.FrobeniusGraphStalkContact
