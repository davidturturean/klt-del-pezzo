import KltDP.Geometry.ProjectiveChartNormal
import KltDP.Geometry.RationalPoints
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual projective points for the Frobenius construction

For each scalar `a`, evaluation on the first projective chart gives an
actual section `Spec k → ℙ¹_k` with affine coordinate `a`. Its underlying
point is closed, and distinct scalars give distinct underlying points.
The pairs with coordinates `(a, a^p)` are actual sections of the scheme
fiber product `ℙ¹_k ×_k ℙ¹_k`. Over an algebraically closed field, any
finite number of distinct such points can be chosen.
Each selected product point factors through an actual scheme morphism
from the affine line, defined by the polynomial substitution `(t,t^p)`.

Reuse: the pinned `Proj.awayι_toSpecZero`, `Spec.map_injective`,
`Infinite.natEmbedding`, and `frobenius_inj`, together with the project's
proved chart equivalence and actual-section/closed-point comparison.
The current official affine-space `homOfVector` API was also inspected;
the existing chart maps already give the needed construction at this pin.

This supplies the point choice in manuscript Proposition
`prop:frobenius-family`, lines 2894–2898. It does not construct the global
projective Frobenius graph as a closed subscheme, its contact multiplicities,
or any blowups. The product-point coordinates are proved using the actual
fiber-product projections, not stored as assertions about numerical labels.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusProjectivePoints

open KltDP.Geometry ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- Evaluation at `a` on the ordinary affine polynomial ring. -/
def parameterEvaluation (a : k) : affineRing k 1 →+* k :=
  MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : Fin 1 => a)

/-- Evaluation at affine coordinate `a`, on the actual homogeneous chart ring. -/
def coordinateEvaluation (a : k) : chartRing k 1 →+* k :=
  (parameterEvaluation a).comp (dehomogenize k 1)

@[simp] theorem coordinateEvaluation_constants (a r : k) :
    coordinateEvaluation a (constants k 1 r) = r := by
  simp [coordinateEvaluation, parameterEvaluation]

@[simp] theorem coordinateEvaluation_ratio (a : k) :
    coordinateEvaluation a (ratio k 1 0) = a := by
  simp [coordinateEvaluation, parameterEvaluation]

/-- The point with homogeneous coordinates `[1:a]`, as an actual morphism. -/
def pointMorphism (a : k) : Spec (CommRingCat.of k) ⟶ projectiveSpace k 1 :=
  Spec.map (CommRingCat.ofHom (coordinateEvaluation a)) ≫ chartMorphism k 1

/-- The first-chart inclusion preserves the actual field structure map. -/
theorem chartMorphism_over_base :
    chartMorphism k 1 ≫ projectiveSpaceToSpec k 1 =
      Spec.map (CommRingCat.ofHom (constants k 1)) := by
  unfold chartMorphism projectiveSpaceToSpec
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- Evaluation fixes the base constants, so it gives a `k`-rational point. -/
theorem pointMorphism_over_base (a : k) :
    pointMorphism a ≫ projectiveSpaceToSpec k 1 =
      𝟙 (Spec (CommRingCat.of k)) := by
  have h : CommRingCat.ofHom (constants k 1) ≫
      CommRingCat.ofHom (coordinateEvaluation a) = 𝟙 (CommRingCat.of k) := by
    ext r
    exact coordinateEvaluation_constants a r
  rw [pointMorphism, Category.assoc, chartMorphism_over_base,
    ← Spec.map_comp, h, Spec.map_id]

/-- Distinct coordinates already give distinct scheme morphisms. -/
theorem pointMorphism_injective : Function.Injective (pointMorphism (k := k)) := by
  intro a b hab
  change Spec.map (CommRingCat.ofHom (coordinateEvaluation a)) ≫ chartMorphism k 1 =
    Spec.map (CommRingCat.ofHom (coordinateEvaluation b)) ≫ chartMorphism k 1 at hab
  have h := Spec.map_injective ((cancel_mono (chartMorphism k 1)).mp hab)
  have hv := congrArg
    (fun f : CommRingCat.of (chartRing k 1) ⟶ CommRingCat.of k => f (ratio k 1 0)) h
  change coordinateEvaluation a (ratio k 1 0) = coordinateEvaluation b (ratio k 1 0) at hv
  simpa only [coordinateEvaluation_ratio] using hv

/-- The actual underlying scheme point of `[1:a]`. -/
def point (a : k) : projectiveSpace k 1 := fieldMorphismPoint (pointMorphism a)

theorem point_isClosed (a : k) : IsClosed ({point a} : Set (projectiveSpace k 1)) :=
  isClosed_point_of_section (projectiveSpaceToSpec k 1) (pointMorphism a)
    (pointMorphism_over_base a)

/-- The actual product over the specified base field. -/
abbrev projectiveProduct (k : Type u) [Field k] : Scheme.{u} :=
  pullback (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)

/-- Its actual structure morphism to the base. -/
def projectiveProductToSpec : projectiveProduct k ⟶ Spec (CommRingCat.of k) :=
  pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) ≫
    projectiveSpaceToSpec k 1

/-- The actual rational product point with affine coordinates `(a,a^p)`. -/
def graphPointMorphism (p : ℕ) (a : k) :
    Spec (CommRingCat.of k) ⟶ projectiveProduct k :=
  pullback.lift (pointMorphism a) (pointMorphism (a ^ p))
    (by rw [pointMorphism_over_base, pointMorphism_over_base])

theorem graphPointMorphism_fst (p : ℕ) (a : k) :
    graphPointMorphism p a ≫
        pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      pointMorphism a :=
  pullback.lift_fst _ _ _

theorem graphPointMorphism_snd (p : ℕ) (a : k) :
    graphPointMorphism p a ≫
        pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      pointMorphism (a ^ p) :=
  pullback.lift_snd _ _ _

theorem graphPointMorphism_over_base (p : ℕ) (a : k) :
    graphPointMorphism p a ≫ projectiveProductToSpec =
      𝟙 (Spec (CommRingCat.of k)) := by
  rw [projectiveProductToSpec, ← Category.assoc, graphPointMorphism_fst,
    pointMorphism_over_base]

/-- The underlying point of the actual section in the product. -/
def graphPoint (p : ℕ) (a : k) : projectiveProduct k :=
  fieldMorphismPoint (graphPointMorphism p a)

theorem graphPoint_fst (p : ℕ) (a : k) :
    (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base
        (graphPoint p a) = point a := by
  change fieldMorphismPoint (graphPointMorphism p a ≫
    pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)) = point a
  rw [graphPointMorphism_fst]
  rfl

theorem graphPoint_snd (p : ℕ) (a : k) :
    (pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base
        (graphPoint p a) = point (a ^ p) := by
  change fieldMorphismPoint (graphPointMorphism p a ≫
    pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)) = point (a ^ p)
  rw [graphPointMorphism_snd]
  rfl

theorem graphPoint_isClosed (p : ℕ) (a : k) :
    IsClosed ({graphPoint p a} : Set (projectiveProduct k)) :=
  isClosed_point_of_section projectiveProductToSpec (graphPointMorphism p a)
    (graphPointMorphism_over_base p a)

/-- Substitution of `t^p` into the affine coordinate of the projective chart. -/
def parameterMap (p : ℕ) : chartRing k 1 →+* affineRing k 1 :=
  (MvPolynomial.eval₂Hom MvPolynomial.C
    (fun _ : Fin 1 => (MvPolynomial.X 0 : affineRing k 1) ^ p)).comp
    (dehomogenize k 1)

@[simp] theorem parameterMap_constants (p : ℕ) (r : k) :
    parameterMap p (constants k 1 r) = (MvPolynomial.C r : affineRing k 1) := by
  simp [parameterMap]

/-- The substitution is compatible with evaluation at each actual scalar. -/
theorem parameterEvaluation_comp_parameterMap (p : ℕ) (a : k) :
    (parameterEvaluation a).comp (parameterMap p) = coordinateEvaluation (a ^ p) := by
  have h : (parameterEvaluation a).comp
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (fun _ : Fin 1 => (MvPolynomial.X 0 : affineRing k 1) ^ p)) =
      parameterEvaluation (a ^ p) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [parameterEvaluation]
    · intro i
      simp [parameterEvaluation]
  exact congrArg (fun g : affineRing k 1 →+* k => g.comp (dehomogenize k 1)) h

/-- The actual affine-line morphism with projective coordinate `[1:t^p]`. -/
def parameterMorphism (p : ℕ) :
    Spec (CommRingCat.of (affineRing k 1)) ⟶ projectiveSpace k 1 :=
  Spec.map (CommRingCat.ofHom (parameterMap p)) ≫ chartMorphism k 1

theorem parameterMorphism_over_base (p : ℕ) :
    parameterMorphism (k := k) p ≫ projectiveSpaceToSpec k 1 =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* affineRing k 1)) := by
  have h : CommRingCat.ofHom (constants k 1) ≫ CommRingCat.ofHom (parameterMap p) =
      CommRingCat.ofHom (MvPolynomial.C : k →+* affineRing k 1) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact parameterMap_constants p r
  rw [parameterMorphism, Category.assoc, chartMorphism_over_base, ← Spec.map_comp, h]

theorem parameterMorphism_evaluation (p : ℕ) (a : k) :
    Spec.map (CommRingCat.ofHom (parameterEvaluation a)) ≫ parameterMorphism p =
      pointMorphism (a ^ p) := by
  have h : CommRingCat.ofHom (parameterMap p) ≫
      CommRingCat.ofHom (parameterEvaluation a) =
      CommRingCat.ofHom (coordinateEvaluation (a ^ p)) :=
    CommRingCat.hom_ext (parameterEvaluation_comp_parameterMap p a)
  rw [parameterMorphism, pointMorphism, ← Category.assoc, ← Spec.map_comp, h]

/-- The actual affine parameterization `(t,t^p)` in the projective product. -/
def affineGraphMorphism (p : ℕ) :
    Spec (CommRingCat.of (affineRing k 1)) ⟶ projectiveProduct k :=
  pullback.lift (parameterMorphism 1) (parameterMorphism p)
    (by rw [parameterMorphism_over_base, parameterMorphism_over_base])

/-- Every chosen rational product point factors through the affine parameterization. -/
theorem affineGraphMorphism_evaluation (p : ℕ) (a : k) :
    Spec.map (CommRingCat.ofHom (parameterEvaluation a)) ≫ affineGraphMorphism p =
      graphPointMorphism p a := by
  apply pullback.hom_ext
  · simp only [affineGraphMorphism, Category.assoc, pullback.lift_fst,
      parameterMorphism_evaluation, pow_one, graphPointMorphism_fst]
  · simp only [affineGraphMorphism, Category.assoc, pullback.lift_snd,
      parameterMorphism_evaluation, graphPointMorphism_snd]

/-- Membership is in the image of an actual scheme morphism. -/
theorem graphPoint_mem_affineGraph_range (p : ℕ) (a : k) :
    graphPoint p a ∈ Set.range (affineGraphMorphism (k := k) p).base := by
  refine ⟨fieldMorphismPoint (Spec.map (CommRingCat.ofHom (parameterEvaluation a))), ?_⟩
  change fieldMorphismPoint
    (Spec.map (CommRingCat.ofHom (parameterEvaluation a)) ≫ affineGraphMorphism p) =
      graphPoint p a
  rw [affineGraphMorphism_evaluation]
  rfl

variable [IsAlgClosed k]

/-- Distinct coordinates give distinct underlying projective scheme points. -/
theorem point_injective : Function.Injective (point (k := k)) := by
  letI : LocallyOfFiniteType (projectiveSpaceToSpec k 1) :=
    projectiveSpaceToSpec_locallyOfFiniteType k 1
  intro a b hab
  apply pointMorphism_injective
  exact section_eq_of_point_eq (projectiveSpaceToSpec k 1)
    (pointMorphism a) (pointMorphism b)
    (pointMorphism_over_base a) (pointMorphism_over_base b) hab

/-- The first product projection distinguishes all these graph-coordinate points. -/
theorem graphPoint_injective (p : ℕ) : Function.Injective (graphPoint (k := k) p) := by
  intro a b hab
  apply point_injective
  have h := congrArg
    (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base hab
  simpa only [graphPoint_fst] using h

/-- In characteristic `p`, the second projection also distinguishes the points. -/
theorem graphPoint_snd_injective (p : ℕ) [Fact p.Prime] [CharP k p] :
    Function.Injective (fun a : k =>
      (pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base
        (graphPoint p a)) := by
  intro a b hab
  apply frobenius_inj k p
  apply point_injective
  simpa only [graphPoint_snd, frobenius_def] using hab

/-- A finite list of actual, pairwise distinct affine field coordinates. -/
def affineCoordinates (n : ℕ) : Fin n ↪ k where
  toFun i := Infinite.natEmbedding k i.val
  inj' _ _ h := Fin.ext ((Infinite.natEmbedding k).injective h)

/-- The resulting embedding into the underlying projective line. -/
def projectivePoints (n : ℕ) : Fin n ↪ projectiveSpace k 1 :=
  (affineCoordinates (k := k) n).trans ⟨point, point_injective⟩

theorem projectivePoints_isClosed (n : ℕ) (i : Fin n) :
    IsClosed ({projectivePoints (k := k) n i} : Set (projectiveSpace k 1)) :=
  point_isClosed (affineCoordinates (k := k) n i)

/-- The resulting distinct actual product points with coordinates `(a_i,a_i^p)`. -/
def graphPoints (p n : ℕ) : Fin n ↪ projectiveProduct k :=
  (affineCoordinates (k := k) n).trans ⟨graphPoint p, graphPoint_injective p⟩

theorem graphPoints_isClosed (p n : ℕ) (i : Fin n) :
    IsClosed ({graphPoints (k := k) p n i} : Set (projectiveProduct k)) :=
  graphPoint_isClosed p (affineCoordinates (k := k) n i)

theorem graphPoints_mem_affineGraph_range (p n : ℕ) (i : Fin n) :
    graphPoints (k := k) p n i ∈ Set.range (affineGraphMorphism p).base :=
  graphPoint_mem_affineGraph_range p (affineCoordinates (k := k) n i)

/-- Existence for every finite `n`, with distinctness expressed in actual scheme points. -/
theorem exists_distinct_closed_graphPoints (p n : ℕ) :
    ∃ q : Fin n ↪ projectiveProduct k,
      (∀ i, IsClosed ({q i} : Set (projectiveProduct k))) ∧
      (∀ i, ∃ a : k, q i = graphPoint p a) :=
  ⟨graphPoints p n, graphPoints_isClosed p n,
    fun i => ⟨affineCoordinates n i, rfl⟩⟩

/-- Distinct closed points on the actual affine graph image, each witnessed by
a section of the specified product structure map. -/
theorem exists_distinct_closed_rational_points_on_affineGraph (p n : ℕ) :
    ∃ q : Fin n ↪ projectiveProduct k,
      (∀ i, IsClosed ({q i} : Set (projectiveProduct k))) ∧
      (∀ i, q i ∈ Set.range (affineGraphMorphism p).base) ∧
      (∀ i, ∃ g : Spec (CommRingCat.of k) ⟶ projectiveProduct k,
        g ≫ projectiveProductToSpec = 𝟙 (Spec (CommRingCat.of k)) ∧
          fieldMorphismPoint g = q i) :=
  ⟨graphPoints p n, graphPoints_isClosed p n, graphPoints_mem_affineGraph_range p n,
    fun i => ⟨graphPointMorphism p (affineCoordinates n i),
      graphPointMorphism_over_base p (affineCoordinates n i), rfl⟩⟩

end KltDP.Examples.FrobeniusProjectivePoints
