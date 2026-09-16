import KltDP.Examples.FrobeniusCoordinateFrobenius
import KltDP.Examples.FrobeniusGraphStalkContact
import KltDP.Geometry.ClosedPoints
import KltDP.Geometry.RationalPoints

/-!
# Rational points of the actual Frobenius graph scheme

The accepted `FrobeniusGraphClosed.graph p` is the equalizer subscheme of the product
`P¹ ×_k P¹` cut out by `y = F(x)`, and `FrobeniusProjectivePoints` supplies the actual
`k`-rational points `[1:a]` of `P¹` and `(a,a^p)` of the product. This module lifts the
selected points to the graph scheme itself, as sections of its structure morphism.

* `graphToSpec p` is the structure morphism `graph p ⟶ Spec k`, the first projection
  followed by the accepted structure morphism of `P¹`; it equals the inclusion followed by
  the product structure morphism, and it is locally of finite type.
* `graphSection p a : Spec k ⟶ graph p` is the rational point `[1:a]` composed with the
  accepted inverse `lineToGraph p` of the graph/projective-line isomorphism. Its composite
  with the inclusion is the accepted product section `graphPointMorphism p a`, and it is a
  section of `graphToSpec p`. Distinct `a` give distinct sections.
* `graphRationalPoint p a` is the underlying scheme point. It maps to the accepted product
  point `(a,a^p)`, it is the same point as `FrobeniusGraphStalkContact.pointOnGraph p a`
  (so the accepted stalk contact length applies to it), and it is closed.
* Over an algebraically closed field, distinct `a` give distinct points, the canonical map
  `k → κ(x)` induced by `graphToSpec p` is bijective at each such point, any injective family
  of sections has injective underlying points, and for every `n` there are `n` distinct
  closed rational points of the graph with residue field `k`.

No point, closedness, distinctness or residue-field statement is assumed; all are derived
from the accepted constructions and the accepted closed-point/rational-point theory.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusGraphRationalPoints

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
  FrobeniusGraphStalkContact FrobeniusCoordinateFrobenius

variable {k : Type u} [Field k]

/-- The rational point `[1:a]` of the projective line lands at `(a, a^p)` in the product. -/
theorem pointMorphism_projectiveGraphMorphism (p : ℕ) (a : k) :
    pointMorphism a ≫ projectiveGraphMorphism p = graphPointMorphism p a := by
  apply pullback.hom_ext
  · simp only [projectiveGraphMorphism, graphPointMorphism, Category.assoc, pullback.lift_fst,
      Category.comp_id]
  · simp only [projectiveGraphMorphism, graphPointMorphism, Category.assoc, pullback.lift_snd,
      pointMorphism_projectivePowerMorphism]

/-- The structure morphism of the graph scheme over the base field. -/
def graphToSpec (p : ℕ) : graph (k := k) p ⟶ Spec (CommRingCat.of k) :=
  graphToLine p ≫ projectiveSpaceToSpec k 1

/-- It is also the inclusion followed by the product's structure morphism. -/
theorem graphToSpec_eq_ι (p : ℕ) :
    graphToSpec (k := k) p = graphι p ≫ projectiveProductToSpec :=
  Category.assoc _ _ _

instance graphToSpec_locallyOfFiniteType (p : ℕ) :
    LocallyOfFiniteType (graphToSpec (k := k) p) := by
  letI : IsIso (graphToLine (k := k) p) :=
    inferInstanceAs (IsIso (graphIsoProjectiveLine (k := k) p).hom)
  letI : LocallyOfFiniteType (projectiveSpaceToSpec k 1) :=
    projectiveSpaceToSpec_locallyOfFiniteType k 1
  unfold graphToSpec
  infer_instance

/-- The rational point `[1:a]` of the projective line, lifted to the graph scheme. -/
def graphSection (p : ℕ) (a : k) : Spec (CommRingCat.of k) ⟶ graph (k := k) p :=
  pointMorphism a ≫ lineToGraph p

theorem graphSection_ι (p : ℕ) (a : k) :
    graphSection p a ≫ graphι p = graphPointMorphism p a := by
  rw [graphSection, Category.assoc, lineToGraph_ι, pointMorphism_projectiveGraphMorphism]

theorem graphSection_graphToLine (p : ℕ) (a : k) :
    graphSection p a ≫ graphToLine p = pointMorphism a := by
  rw [graphSection, Category.assoc, lineToGraph_graphToLine, Category.comp_id]

/-- The lifted point is a section of the graph's structure morphism: a `k`-rational point. -/
theorem graphSection_over_base (p : ℕ) (a : k) :
    graphSection p a ≫ graphToSpec p = 𝟙 (Spec (CommRingCat.of k)) := by
  rw [graphToSpec, ← Category.assoc, graphSection_graphToLine, pointMorphism_over_base]

/-- Distinct coordinates give distinct sections of the graph. -/
theorem graphSection_injective (p : ℕ) : Function.Injective (graphSection (k := k) p) := by
  intro a b hab
  apply pointMorphism_injective
  have h := congrArg (fun g : Spec (CommRingCat.of k) ⟶ graph (k := k) p =>
    g ≫ graphToLine p) hab
  simpa only [graphSection_graphToLine] using h

/-- The underlying scheme point of the rational point `[1:a]` on the graph. -/
def graphRationalPoint (p : ℕ) (a : k) : graph (k := k) p :=
  fieldMorphismPoint (graphSection p a)

/-- It maps to the accepted product point `(a, a^p)`. -/
theorem graphRationalPoint_ι (p : ℕ) (a : k) :
    (graphι p).base (graphRationalPoint p a) = graphPoint p a := by
  change fieldMorphismPoint (graphSection p a ≫ graphι p) = graphPoint p a
  rw [graphSection_ι]
  rfl

/-- Its first projection is the accepted point `[1:a]` of the projective line. -/
theorem graphRationalPoint_graphToLine (p : ℕ) (a : k) :
    (graphToLine p).base (graphRationalPoint p a) = point a := by
  change fieldMorphismPoint (graphSection p a ≫ graphToLine p) = point a
  rw [graphSection_graphToLine]
  rfl

/-- The section point is the chart point used for the accepted stalk contact length. -/
theorem graphRationalPoint_eq_pointOnGraph (p : ℕ) (a : k) :
    graphRationalPoint p a = pointOnGraph p a := by
  apply (graphι (k := k) p).isClosedEmbedding.injective
  rw [graphRationalPoint_ι, pointOnGraph_inclusion]

/-- The underlying point of any section of the graph's structure morphism is closed. -/
theorem section_point_isClosed (p : ℕ) {s : Spec (CommRingCat.of k) ⟶ graph (k := k) p}
    (hs : s ≫ graphToSpec p = 𝟙 (Spec (CommRingCat.of k))) :
    IsClosed ({fieldMorphismPoint s} : Set (graph p)) :=
  isClosed_point_of_section (graphToSpec p) s hs

theorem graphRationalPoint_isClosed (p : ℕ) (a : k) :
    IsClosed ({graphRationalPoint p a} : Set (graph p)) :=
  section_point_isClosed p (graphSection_over_base p a)

section AlgClosed

variable [IsAlgClosed k]

/-- Distinct coordinates give distinct underlying points of the graph scheme. -/
theorem graphRationalPoint_injective (p : ℕ) :
    Function.Injective (graphRationalPoint (k := k) p) := by
  intro a b hab
  apply graphPoint_injective p
  have h := congrArg (graphι (k := k) p).base hab
  simpa only [graphRationalPoint_ι] using h

/-- The canonical map `k → κ(x)` induced by the structure morphism is bijective at the
underlying point of every section: the residue field is `k`. -/
theorem section_point_residue_bijective (p : ℕ)
    {s : Spec (CommRingCat.of k) ⟶ graph (k := k) p}
    (hs : s ≫ graphToSpec p = 𝟙 (Spec (CommRingCat.of k))) :
    Function.Bijective (baseToResidueFieldMap (graphToSpec p) (fieldMorphismPoint s)).hom :=
  baseToResidueFieldMap_bijective (graphToSpec p) (fieldMorphismPoint s)
    (section_point_isClosed p hs)

theorem graphRationalPoint_residue_bijective (p : ℕ) (a : k) :
    Function.Bijective
      (baseToResidueFieldMap (graphToSpec p) (graphRationalPoint p a)).hom :=
  section_point_residue_bijective p (graphSection_over_base p a)

/-- Any injective family of sections of the graph has injective underlying points: an
arbitrary selection of distinct rational points gives distinct scheme points. -/
theorem sections_points_injective (p : ℕ) {ι : Type*}
    (s : ι → (Spec (CommRingCat.of k) ⟶ graph (k := k) p))
    (hs : ∀ i, s i ≫ graphToSpec p = 𝟙 (Spec (CommRingCat.of k)))
    (hinj : Function.Injective s) :
    Function.Injective (fun i => fieldMorphismPoint (s i)) := by
  intro i j hij
  apply hinj
  exact section_eq_of_point_eq (graphToSpec p) (s i) (s j) (hs i) (hs j) hij

/-- `n` pairwise distinct rational points of the graph scheme, for every `n`. -/
def graphRationalPoints (p n : ℕ) : Fin n ↪ graph (k := k) p :=
  (affineCoordinates (k := k) n).trans ⟨graphRationalPoint p, graphRationalPoint_injective p⟩

theorem graphRationalPoints_isClosed (p n : ℕ) (i : Fin n) :
    IsClosed ({graphRationalPoints (k := k) p n i} : Set (graph p)) :=
  graphRationalPoint_isClosed p (affineCoordinates (k := k) n i)

/-- For every `n` there are `n` sections of the graph's structure morphism with pairwise
distinct, closed underlying points whose residue field is `k`. -/
theorem exists_distinct_closed_rational_points_on_graph (p n : ℕ) :
    ∃ s : Fin n → (Spec (CommRingCat.of k) ⟶ graph (k := k) p),
      (∀ i, s i ≫ graphToSpec p = 𝟙 (Spec (CommRingCat.of k))) ∧
      Function.Injective (fun i => fieldMorphismPoint (s i)) ∧
      (∀ i, IsClosed ({fieldMorphismPoint (s i)} : Set (graph p))) ∧
      (∀ i, Function.Bijective
        (baseToResidueFieldMap (graphToSpec p) (fieldMorphismPoint (s i))).hom) :=
  ⟨fun i => graphSection p (affineCoordinates n i),
    fun _ => graphSection_over_base p _,
    fun _ _ h => (affineCoordinates (k := k) n).injective (graphRationalPoint_injective p h),
    fun _ => graphRationalPoint_isClosed p _,
    fun _ => graphRationalPoint_residue_bijective p _⟩

end AlgClosed

end KltDP.Examples.FrobeniusGraphRationalPoints
