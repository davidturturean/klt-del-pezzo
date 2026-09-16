import KltDP.Examples.FrobeniusGraphF28
import KltDP.Examples.FrobeniusContactBlowupsF29
import KltDP.Geometry.ProjectivePlane
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Nonvacuity witnesses for the geometry bundles F28 and F29 (lane B10)

The plan (§10.3) asks that the public geometric statements be instantiated at
actual objects. This module instantiates the two bundles
`KltDP.Examples.f28_frobenius_graph` and `KltDP.Examples.f29_contact_blowups`
at the algebraic closures of the prime fields `𝔽₂` and `𝔽₃`,

* `Fbar2 := AlgebraicClosure (ZMod 2)` with `p := 2`, and
* `Fbar3 := AlgebraicClosure (ZMod 3)` with `p := 3`,

whose `Field`, `IsAlgClosed`, `CharP _ p` and `Fact p.Prime` instances are the
pinned Mathlib instances `AlgebraicClosure.instField`, `AlgebraicClosure.isAlgClosed`,
the `CharP (AlgebraicClosure k) p` instance of `Mathlib/FieldTheory/IsAlgClosed/AlgebraicClosure.lean`
(from `ZMod.charP`), and `Nat.fact_prime_two` / `Nat.fact_prime_three`. No instance
is declared here.

Contents.

1. Generic clause extraction from the bundles (section `Generic`): for any
   algebraically closed `k` of characteristic `p`, the clauses of `f28_frobenius_graph`
   and `f29_contact_blowups` that are exported below are read off the bundle
   statements by destructuring the conjunctions (`f28_points`, `f28_closedImmersion`,
   `f28_class`, `f28_contact`, `f29_proper`, `f29_centers_injective`,
   `f29_totalClass`, ...). Every proof is `obtain … := f28_frobenius_graph k p` /
   `f29_contact_blowups.{u} k p`, so these are literally the bundle's clauses (the F29
   bundle now has the single universe parameter `u`; lane F pinned `FinalIndex.{0}`).
2. The embedding `graphEmbeddingOfF28 k p n : Fin n ↪ graph p` constructed from clause
   (5) of F28 alone (choice on the existential family of sections), with its closed
   points and residue fields; this is the explicit check that the point-injectivity
   of F28 yields an actual `Fin n ↪ graph`.
3. The concrete statements at `Fbar2`, `p = 2` (the graph of `y = x²`) and at `Fbar3`,
   `p = 3` (the graph of `y = x³`): closed immersion, `P¹`-isomorphism, Picard class
   `2 • a + b` resp. `3 • a + b`, Frobenius action `a ↦ a²` resp. `a ↦ a³` on rational
   points, contact length `2` resp. `3`, and for every `n` (in particular `n = 3`) `n`
   distinct closed rational points with residue field the base field. From F29:
   properness and smoothness of every stage of every selected tower, injectivity of the
   centres (with the concrete instance that the centres at `0` and `1` differ), the
   total-transform class on every stage, the exceptional contact lengths, and the
   unaffected fibres.
4. Two families of actual embeddings `Fin n ↪ graph p` at each field: the F28-derived
   `graphTwoEmbedding n`, `graphThreeEmbedding n`, and the lane F re-exports
   `graphTwoRationalPoints n`, `graphThreeRationalPoints n` (points `(a, a^p)` for
   `n` distinct scalars `a`), with closedness.
5. The accepted projective-space witnesses at these fields: `projectiveSpace Fbar2 1`,
   `projectiveSpace Fbar2 2`, `projectiveSpace Fbar3 1`, `projectiveSpace Fbar3 2` as
   actual schemes (accepted `KltDP.Geometry.projectiveSpace`), actual rational points
   and `Fin n ↪ P¹` (accepted `FrobeniusProjectivePoints.point`, `projectivePoints`),
   the accepted `projectivePlaneSurface` as a `NormalProjectiveSurface` at each field,
   and the accepted `normalProjectiveSurface_nonempty` re-exported at each field.
6. The summary `geometry_bundle_witnesses`.

Every witness is a term; nothing is assumed. The lane F modules imported here
(`FrobeniusGraphF28`, `FrobeniusContactBlowupsF29`, `FrobeniusGraphRationalPoints`,
`FrobeniusCoordinateFrobenius`, `FrobeniusUnaffectedFibers`,
`FrobeniusContactTowerSelectedPoint`, `FrobeniusGraphExceptionalSeparation`,
`FrobeniusGraphPicardClassTotalTransform`) are byte-identical copies of the lane F
sources at the time of writing; see `GEOMETRY_WITNESSES_CORRESPONDENCE.md`.
What is not done here: nothing new about the geometry is proved; the strict-transform
classes and the multi-centre surface of F29 remain open exactly as in the bundle.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Support.GeometryBundleWitnesses

open KltDP.Geometry KltDP.Examples
open KltDP.Examples.FrobeniusProjectivePoints KltDP.Examples.FrobeniusProjectiveMorphism
  KltDP.Examples.FrobeniusGraphClosed KltDP.Examples.FrobeniusGraphStalkContact
  KltDP.Examples.FrobeniusCoordinateFrobenius KltDP.Examples.FrobeniusGraphRationalPoints
  KltDP.Examples.FrobeniusGraphPicardClassFrames
  KltDP.Examples.FrobeniusGraphPicardClassFiberClasses
  KltDP.Examples.FrobeniusBlowupContact KltDP.Examples.FrobeniusBlowupChartIteration
  KltDP.Examples.FrobeniusBlowupIncidence KltDP.Examples.FrobeniusGlobalBlowupStages
  KltDP.Examples.FrobeniusGlobalBlowupSmooth KltDP.Examples.FrobeniusTranslatedCharts
  KltDP.Examples.FrobeniusStageComplement.PlaneChartedScheme
  KltDP.Examples.FrobeniusGlobalStrictTransform KltDP.Examples.FrobeniusStrictTransformContact
  KltDP.Examples.FrobeniusGlobalExceptionalSuccessor
  KltDP.Examples.FrobeniusExceptionalFinalConfiguration
  KltDP.Examples.FrobeniusGraphPicardClassZeroFiber
  KltDP.Examples.FrobeniusGraphPicardClassTotalTransform
  KltDP.Examples.FrobeniusContactTowerSelectedPoint KltDP.Examples.FrobeniusUnaffectedFibers
  KltDP.Examples.FrobeniusGraphExceptionalSeparation

/-! ### The two fields -/

/-- The algebraic closure of the prime field `𝔽₂`: an algebraically closed field of
characteristic two (pinned Mathlib instances). -/
abbrev Fbar2 : Type := AlgebraicClosure (ZMod 2)

/-- The algebraic closure of the prime field `𝔽₃`: an algebraically closed field of
characteristic three (pinned Mathlib instances). -/
abbrev Fbar3 : Type := AlgebraicClosure (ZMod 3)

theorem Fbar2_isAlgClosed : IsAlgClosed Fbar2 := inferInstance

theorem Fbar3_isAlgClosed : IsAlgClosed Fbar3 := inferInstance

theorem Fbar2_charP : CharP Fbar2 2 := inferInstance

theorem Fbar3_charP : CharP Fbar3 3 := inferInstance

theorem Fbar2_two_eq_zero : (2 : Fbar2) = 0 := by
  exact_mod_cast (CharP.cast_eq_zero_iff Fbar2 2 2).2 dvd_rfl

theorem Fbar3_three_eq_zero : (3 : Fbar3) = 0 := by
  exact_mod_cast (CharP.cast_eq_zero_iff Fbar3 3 3).2 dvd_rfl

theorem Fbar2_infinite : Infinite Fbar2 := inferInstance

theorem Fbar3_infinite : Infinite Fbar3 := inferInstance

/-! ### Generic clause extraction from the two bundles -/

section Generic

variable (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- F28, clause (1b), with `frobenius k p a` unfolded to `a ^ p`. -/
theorem f28_frobenius_points (a : k) :
    pointMorphism a ≫ projectivePowerMorphism p = pointMorphism (a ^ p) := by
  obtain ⟨-, h, -⟩ := f28_frobenius_graph k p
  have ha := h a
  rwa [frobenius_def] at ha

/-- F28, clause (2): the graph is a closed subscheme of the product. -/
theorem f28_closedImmersion : IsClosedImmersion (graphι (k := k) p) := by
  obtain ⟨-, -, -, h, -⟩ := f28_frobenius_graph k p
  exact h

/-- F28, clause (3): the graph is isomorphic to the projective line over the first factor. -/
theorem f28_iso_projectiveLine :
    ∃ e : graph (k := k) p ≅ projectiveSpace k 1,
      e.hom = graphι p ≫ firstProjection ∧ e.inv ≫ graphι p = projectiveGraphMorphism p := by
  obtain ⟨-, -, -, -, -, h, -⟩ := f28_frobenius_graph k p
  exact h

/-- F28, clause (4): the class of the graph is `p • a + b`. -/
theorem f28_class :
    -Additive.ofMul (graphIdealLine (k := k) p).toPic = p • firstFiberClass + secondFiberClass := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := f28_frobenius_graph k p
  exact h

/-- F28, clause (5): `n` sections with distinct closed points of residue field `k`. -/
theorem f28_points (n : ℕ) :
    ∃ s : Fin n → (Spec (CommRingCat.of k) ⟶ graph (k := k) p),
      (∀ i, s i ≫ graphToSpec p = 𝟙 (Spec (CommRingCat.of k))) ∧
      Function.Injective (fun i => fieldMorphismPoint (s i)) ∧
      (∀ i, IsClosed ({fieldMorphismPoint (s i)} : Set (graph p))) ∧
      (∀ i, Function.Bijective
        (baseToResidueFieldMap (graphToSpec p) (fieldMorphismPoint (s i))).hom) := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := f28_frobenius_graph k p
  exact h n

/-- F28, clause (7): contact length `p` with the fibre `y = a^p` at every rational point. -/
theorem f28_contact (a : k) :
    Module.length ((graph p).presheaf.stalk (pointOnGraph p a))
      ((graph p).presheaf.stalk (pointOnGraph p a) ⧸ Ideal.span {graphFiberGerm p a}) = p := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := f28_frobenius_graph k p
  exact (h a).2

/-- The explicit check asked for by the brief: clause (5) of F28 alone yields, for every
`n`, an actual embedding `Fin n ↪ graph p`, namely the underlying points of the chosen
family of sections. -/
def graphEmbeddingOfF28 (n : ℕ) : Fin n ↪ graph (k := k) p where
  toFun i := fieldMorphismPoint ((f28_points k p n).choose i)
  inj' := (f28_points k p n).choose_spec.2.1

theorem graphEmbeddingOfF28_isClosed (n : ℕ) (i : Fin n) :
    IsClosed ({graphEmbeddingOfF28 k p n i} : Set (graph p)) :=
  (f28_points k p n).choose_spec.2.2.1 i

theorem graphEmbeddingOfF28_residue_bijective (n : ℕ) (i : Fin n) :
    Function.Bijective
      (baseToResidueFieldMap (graphToSpec p) (graphEmbeddingOfF28 k p n i)).hom :=
  (f28_points k p n).choose_spec.2.2.2 i

theorem graphEmbeddingOfF28_exists_section (n : ℕ) (i : Fin n) :
    ∃ s : Spec (CommRingCat.of k) ⟶ graph (k := k) p,
      s ≫ graphToSpec p = 𝟙 (Spec (CommRingCat.of k)) ∧
      fieldMorphismPoint s = graphEmbeddingOfF28 k p n i :=
  ⟨(f28_points k p n).choose i, (f28_points k p n).choose_spec.1 i, rfl⟩

/-- F29, clause (1): properness of the tower projections and of the stages, smoothness. -/
theorem f29_proper (a : k) (n : ℕ) :
    IsProper (selectedProjection p a n) ∧
      IsProper ((translatedInitial (k := k) p a).stage n).structureMap ∧
      IsSmoothOfRelativeDimension 2 ((translatedInitial (k := k) p a).stage n).structureMap := by
  obtain ⟨h, -⟩ := f29_contact_blowups.{u} k p
  exact h a n

/-- F29, clause (2): distinct scalars give distinct centres. -/
theorem f29_centers_injective :
    Function.Injective (β := projectiveProduct k)
      (fun a : k => (translatedInitial p a).chart.base (originPoint (k := k))) := by
  obtain ⟨-, -, -, h, -⟩ := f29_contact_blowups.{u} k p
  exact h

include p in
/-- F29, clause (4): the three contact lengths at the origin tower. -/
theorem f29_contactLengths (n m : ℕ) :
    Module.length (contactStalk (k := k) (n + 1) m)
        (contactStalk (k := k) (n + 1) m ⧸ Ideal.span {contactGerm n m chartU}) = 1 ∧
      Module.length (contactStalk (k := k) (n + 1) m)
        (contactStalk (k := k) (n + 1) m ⧸ Ideal.span {contactGerm n m chartW}) = m ∧
      Module.length (contactStalk (k := k) (n + 1) m)
        (contactStalk (k := k) (n + 1) m ⧸
          Ideal.span {contactGerm n m (baseMap vCoord)}) = m + 1 := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := f29_contact_blowups.{u} k p
  exact h n m

/-- F29, clause (5): the total-transform class on every stage. -/
theorem f29_totalClass (n : ℕ) :
    -Additive.ofMul (graphTotalIdealLine (k := k) n p).toPic =
      p • firstFiberTotalClass n + secondFiberTotalClass n := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := f29_contact_blowups.{u} k p
  exact h n

include p in
/-- F29, clause (6): the newest exceptional fibre of every stage is a projective line. -/
theorem f29_previousFiber_iso (n : ℕ) :
    Nonempty (previousFiber ((projectiveProductInitial (k := k)).stage n) ≅ projectiveSpace k 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := f29_contact_blowups.{u} k p
  exact h n

/-- F29, clause (8): horizontal fibres over non-selected points are unaffected. -/
theorem f29_horizontalFiber (a c : k) (hc : c ≠ a ^ p) (n : ℕ) :
    IsPullback (horizontalFiberLift p a c hc n) (𝟙 (projectiveSpace k 1))
        (selectedProjection p a n) (horizontalFiberMorphism c) ∧
      IsClosedImmersion (horizontalFiberLift p a c hc n) ∧
      ∀ y, (horizontalFiberLift p a c hc n).base y ∈ stagePuncture (translatedInitial p a) n := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := f29_contact_blowups.{u} k p
  exact h a c hc n

end Generic

/-! ### Concrete statements over `𝔽̄₂`, `p = 2`: the graph of `y = x²` -/

/-- Over `𝔽̄₂` the coordinate-power map acts on rational points by `a ↦ a²`. -/
theorem graphTwo_frobenius_points (a : Fbar2) :
    pointMorphism a ≫ projectivePowerMorphism 2 = pointMorphism (a ^ 2) :=
  f28_frobenius_points Fbar2 2 a

/-- The graph of `y = x²` in `P¹ × P¹` over `𝔽̄₂` is a closed subscheme. -/
theorem graphTwo_isClosedImmersion : IsClosedImmersion (graphι (k := Fbar2) 2) :=
  f28_closedImmersion Fbar2 2

/-- It is isomorphic to the projective line over the first factor. -/
theorem graphTwo_iso_projectiveLine :
    ∃ e : graph (k := Fbar2) 2 ≅ projectiveSpace Fbar2 1,
      e.hom = graphι 2 ≫ firstProjection ∧ e.inv ≫ graphι 2 = projectiveGraphMorphism 2 :=
  f28_iso_projectiveLine Fbar2 2

/-- Its class in the actual Picard group of `P¹ × P¹` over `𝔽̄₂` is `2 • a + b`. -/
theorem graphTwo_class :
    -Additive.ofMul (graphIdealLine (k := Fbar2) 2).toPic =
      2 • firstFiberClass + secondFiberClass :=
  f28_class Fbar2 2

/-- For every `n` the graph of `y = x²` over `𝔽̄₂` has `n` distinct closed rational points
with residue field `𝔽̄₂`, given by sections of its structure morphism. -/
theorem graphTwo_points (n : ℕ) :
    ∃ s : Fin n → (Spec (CommRingCat.of Fbar2) ⟶ graph (k := Fbar2) 2),
      (∀ i, s i ≫ graphToSpec 2 = 𝟙 (Spec (CommRingCat.of Fbar2))) ∧
      Function.Injective (fun i => fieldMorphismPoint (s i)) ∧
      (∀ i, IsClosed ({fieldMorphismPoint (s i)} : Set (graph 2))) ∧
      (∀ i, Function.Bijective
        (baseToResidueFieldMap (graphToSpec 2) (fieldMorphismPoint (s i))).hom) :=
  f28_points Fbar2 2 n

/-- In particular three such points. -/
theorem graphTwo_three_points :
    ∃ s : Fin 3 → (Spec (CommRingCat.of Fbar2) ⟶ graph (k := Fbar2) 2),
      (∀ i, s i ≫ graphToSpec 2 = 𝟙 (Spec (CommRingCat.of Fbar2))) ∧
      Function.Injective (fun i => fieldMorphismPoint (s i)) ∧
      (∀ i, IsClosed ({fieldMorphismPoint (s i)} : Set (graph 2))) ∧
      (∀ i, Function.Bijective
        (baseToResidueFieldMap (graphToSpec 2) (fieldMorphismPoint (s i))).hom) :=
  graphTwo_points 3

/-- Contact of order two with the fibre `y = a²` at every rational point `[1:a]`. -/
theorem graphTwo_contact (a : Fbar2) :
    Module.length ((graph 2).presheaf.stalk (pointOnGraph 2 a))
      ((graph 2).presheaf.stalk (pointOnGraph 2 a) ⧸ Ideal.span {graphFiberGerm 2 a}) = 2 :=
  f28_contact Fbar2 2 a

/-- The F28-derived embedding `Fin n ↪ graph 2` over `𝔽̄₂`. -/
def graphTwoEmbedding (n : ℕ) : Fin n ↪ graph (k := Fbar2) 2 :=
  graphEmbeddingOfF28 Fbar2 2 n

theorem graphTwoEmbedding_isClosed (n : ℕ) (i : Fin n) :
    IsClosed ({graphTwoEmbedding n i} : Set (graph 2)) :=
  graphEmbeddingOfF28_isClosed Fbar2 2 n i

/-- The lane F embedding: the points `(a, a²)` for `n` distinct scalars `a`. -/
def graphTwoRationalPoints (n : ℕ) : Fin n ↪ graph (k := Fbar2) 2 :=
  graphRationalPoints 2 n

theorem graphTwoRationalPoints_isClosed (n : ℕ) (i : Fin n) :
    IsClosed ({graphTwoRationalPoints n i} : Set (graph 2)) :=
  graphRationalPoints_isClosed 2 n i

/-- Every stage of every selected contact tower over `𝔽̄₂` is proper and smooth of
relative dimension two, with proper projection to the product. -/
theorem graphTwo_tower_proper_smooth (a : Fbar2) (n : ℕ) :
    IsProper (selectedProjection 2 a n) ∧
      IsProper ((translatedInitial (k := Fbar2) 2 a).stage n).structureMap ∧
      IsSmoothOfRelativeDimension 2 ((translatedInitial (k := Fbar2) 2 a).stage n).structureMap :=
  f29_proper Fbar2 2 a n

/-- Distinct scalars give distinct centres over `𝔽̄₂`. -/
theorem graphTwo_centers_injective :
    Function.Injective (β := projectiveProduct Fbar2)
      (fun a : Fbar2 => (translatedInitial 2 a).chart.base (originPoint (k := Fbar2))) :=
  f29_centers_injective Fbar2 2

/-- Concretely, the centres at `a = 0` and `a = 1` are different points of `P¹ × P¹`. -/
theorem graphTwo_center_zero_ne_one :
    (translatedInitial (k := Fbar2) 2 0).chart.base (originPoint (k := Fbar2)) ≠
      (translatedInitial (k := Fbar2) 2 1).chart.base (originPoint (k := Fbar2)) :=
  fun h => zero_ne_one (graphTwo_centers_injective h)

/-- The exceptional contact lengths `1`, `m`, `m + 1` at the origin tower over `𝔽̄₂`. -/
theorem graphTwo_contactLengths (n m : ℕ) :
    Module.length (contactStalk (k := Fbar2) (n + 1) m)
        (contactStalk (k := Fbar2) (n + 1) m ⧸ Ideal.span {contactGerm n m chartU}) = 1 ∧
      Module.length (contactStalk (k := Fbar2) (n + 1) m)
        (contactStalk (k := Fbar2) (n + 1) m ⧸ Ideal.span {contactGerm n m chartW}) = m ∧
      Module.length (contactStalk (k := Fbar2) (n + 1) m)
        (contactStalk (k := Fbar2) (n + 1) m ⧸
          Ideal.span {contactGerm n m (baseMap vCoord)}) = m + 1 :=
  f29_contactLengths Fbar2 2 n m

/-- The total-transform class `2 • a + b` on every stage over `𝔽̄₂`. -/
theorem graphTwo_totalClass (n : ℕ) :
    -Additive.ofMul (graphTotalIdealLine (k := Fbar2) n 2).toPic =
      2 • firstFiberTotalClass n + secondFiberTotalClass n :=
  f29_totalClass Fbar2 2 n

/-- Horizontal fibres `y = c` with `c ≠ a²` are unaffected by the tower at `(a, a²)`. -/
theorem graphTwo_horizontalFiber (a c : Fbar2) (hc : c ≠ a ^ 2) (n : ℕ) :
    IsPullback (horizontalFiberLift 2 a c hc n) (𝟙 (projectiveSpace Fbar2 1))
        (selectedProjection 2 a n) (horizontalFiberMorphism c) ∧
      IsClosedImmersion (horizontalFiberLift 2 a c hc n) ∧
      ∀ y, (horizontalFiberLift 2 a c hc n).base y ∈ stagePuncture (translatedInitial 2 a) n :=
  f29_horizontalFiber Fbar2 2 a c hc n

/-! ### Concrete statements over `𝔽̄₃`, `p = 3`: the graph of `y = x³` -/

/-- Over `𝔽̄₃` the coordinate-power map acts on rational points by `a ↦ a³`. -/
theorem graphThree_frobenius_points (a : Fbar3) :
    pointMorphism a ≫ projectivePowerMorphism 3 = pointMorphism (a ^ 3) :=
  f28_frobenius_points Fbar3 3 a

/-- The graph of `y = x³` in `P¹ × P¹` over `𝔽̄₃` is a closed subscheme. -/
theorem graphThree_isClosedImmersion : IsClosedImmersion (graphι (k := Fbar3) 3) :=
  f28_closedImmersion Fbar3 3

/-- It is isomorphic to the projective line over the first factor. -/
theorem graphThree_iso_projectiveLine :
    ∃ e : graph (k := Fbar3) 3 ≅ projectiveSpace Fbar3 1,
      e.hom = graphι 3 ≫ firstProjection ∧ e.inv ≫ graphι 3 = projectiveGraphMorphism 3 :=
  f28_iso_projectiveLine Fbar3 3

/-- Its class in the actual Picard group of `P¹ × P¹` over `𝔽̄₃` is `3 • a + b`. -/
theorem graphThree_class :
    -Additive.ofMul (graphIdealLine (k := Fbar3) 3).toPic =
      3 • firstFiberClass + secondFiberClass :=
  f28_class Fbar3 3

/-- For every `n` the graph of `y = x³` over `𝔽̄₃` has `n` distinct closed rational points
with residue field `𝔽̄₃`. -/
theorem graphThree_points (n : ℕ) :
    ∃ s : Fin n → (Spec (CommRingCat.of Fbar3) ⟶ graph (k := Fbar3) 3),
      (∀ i, s i ≫ graphToSpec 3 = 𝟙 (Spec (CommRingCat.of Fbar3))) ∧
      Function.Injective (fun i => fieldMorphismPoint (s i)) ∧
      (∀ i, IsClosed ({fieldMorphismPoint (s i)} : Set (graph 3))) ∧
      (∀ i, Function.Bijective
        (baseToResidueFieldMap (graphToSpec 3) (fieldMorphismPoint (s i))).hom) :=
  f28_points Fbar3 3 n

/-- The brief's example: the graph of `y = x³` over the algebraic closure of `𝔽₃` has three
distinct closed rational points with residue field `𝔽̄₃`, each the underlying point of a
section of the structure morphism. -/
theorem graphThree_three_points :
    ∃ s : Fin 3 → (Spec (CommRingCat.of Fbar3) ⟶ graph (k := Fbar3) 3),
      (∀ i, s i ≫ graphToSpec 3 = 𝟙 (Spec (CommRingCat.of Fbar3))) ∧
      Function.Injective (fun i => fieldMorphismPoint (s i)) ∧
      (∀ i, IsClosed ({fieldMorphismPoint (s i)} : Set (graph 3))) ∧
      (∀ i, Function.Bijective
        (baseToResidueFieldMap (graphToSpec 3) (fieldMorphismPoint (s i))).hom) :=
  graphThree_points 3

/-- Contact of order three with the fibre `y = a³` at every rational point `[1:a]`. -/
theorem graphThree_contact (a : Fbar3) :
    Module.length ((graph 3).presheaf.stalk (pointOnGraph 3 a))
      ((graph 3).presheaf.stalk (pointOnGraph 3 a) ⧸ Ideal.span {graphFiberGerm 3 a}) = 3 :=
  f28_contact Fbar3 3 a

/-- The F28-derived embedding `Fin n ↪ graph 3` over `𝔽̄₃`. -/
def graphThreeEmbedding (n : ℕ) : Fin n ↪ graph (k := Fbar3) 3 :=
  graphEmbeddingOfF28 Fbar3 3 n

theorem graphThreeEmbedding_isClosed (n : ℕ) (i : Fin n) :
    IsClosed ({graphThreeEmbedding n i} : Set (graph 3)) :=
  graphEmbeddingOfF28_isClosed Fbar3 3 n i

/-- Three distinct points of the graph of `y = x³` over `𝔽̄₃`, as an actual embedding. -/
def graphThreeEmbeddingThree : Fin 3 ↪ graph (k := Fbar3) 3 :=
  graphThreeEmbedding 3

/-- The lane F embedding: the points `(a, a³)` for `n` distinct scalars `a`. -/
def graphThreeRationalPoints (n : ℕ) : Fin n ↪ graph (k := Fbar3) 3 :=
  graphRationalPoints 3 n

theorem graphThreeRationalPoints_isClosed (n : ℕ) (i : Fin n) :
    IsClosed ({graphThreeRationalPoints n i} : Set (graph 3)) :=
  graphRationalPoints_isClosed 3 n i

/-- Every stage of every selected contact tower over `𝔽̄₃` is proper and smooth of
relative dimension two, with proper projection to the product. -/
theorem graphThree_tower_proper_smooth (a : Fbar3) (n : ℕ) :
    IsProper (selectedProjection 3 a n) ∧
      IsProper ((translatedInitial (k := Fbar3) 3 a).stage n).structureMap ∧
      IsSmoothOfRelativeDimension 2 ((translatedInitial (k := Fbar3) 3 a).stage n).structureMap :=
  f29_proper Fbar3 3 a n

/-- Distinct scalars give distinct centres over `𝔽̄₃`. -/
theorem graphThree_centers_injective :
    Function.Injective (β := projectiveProduct Fbar3)
      (fun a : Fbar3 => (translatedInitial 3 a).chart.base (originPoint (k := Fbar3))) :=
  f29_centers_injective Fbar3 3

/-- Three distinct centres over `𝔽̄₃`, indexed by `Fin 3` through the lane F scalars. -/
theorem graphThree_three_centers_injective :
    Function.Injective (β := projectiveProduct Fbar3) (fun i : Fin 3 =>
      (translatedInitial (k := Fbar3) 3 (affineCoordinates 3 i)).chart.base
        (originPoint (k := Fbar3))) :=
  fun _ _ h => (affineCoordinates (k := Fbar3) 3).injective (graphThree_centers_injective h)

/-- The total-transform class `3 • a + b` on every stage over `𝔽̄₃`. -/
theorem graphThree_totalClass (n : ℕ) :
    -Additive.ofMul (graphTotalIdealLine (k := Fbar3) n 3).toPic =
      3 • firstFiberTotalClass n + secondFiberTotalClass n :=
  f29_totalClass Fbar3 3 n

/-- The newest exceptional fibre of every stage of the origin tower over `𝔽̄₃` is a
projective line. -/
theorem graphThree_previousFiber_iso (n : ℕ) :
    Nonempty (previousFiber ((projectiveProductInitial (k := Fbar3)).stage n) ≅
      projectiveSpace Fbar3 1) :=
  f29_previousFiber_iso Fbar3 3 n

/-! ### The accepted projective-space and surface witnesses at these fields -/

/-- The projective line over `𝔽̄₂` as an actual scheme (accepted `projectiveSpace`). -/
def projectiveLineTwo : Scheme := projectiveSpace Fbar2 1

/-- The projective plane over `𝔽̄₂` as an actual scheme. -/
def projectivePlaneTwo : Scheme := projectiveSpace Fbar2 2

/-- The projective line over `𝔽̄₃` as an actual scheme. -/
def projectiveLineThree : Scheme := projectiveSpace Fbar3 1

/-- The projective plane over `𝔽̄₃` as an actual scheme. -/
def projectivePlaneThree : Scheme := projectiveSpace Fbar3 2

/-- An actual point of the projective line over `𝔽̄₂`: `[1:0]`. -/
def projectiveLineTwo_origin : projectiveSpace Fbar2 1 := point (0 : Fbar2)

theorem projectiveLineTwo_origin_isClosed :
    IsClosed ({projectiveLineTwo_origin} : Set (projectiveSpace Fbar2 1)) :=
  point_isClosed (0 : Fbar2)

/-- `n` distinct points of the projective line over `𝔽̄₂` (accepted `projectivePoints`). -/
def projectiveLineTwo_points (n : ℕ) : Fin n ↪ projectiveSpace Fbar2 1 :=
  projectivePoints n

/-- `n` distinct points of the projective line over `𝔽̄₃`. -/
def projectiveLineThree_points (n : ℕ) : Fin n ↪ projectiveSpace Fbar3 1 :=
  projectivePoints n

/-- The accepted projective plane over `𝔽̄₂` as a normal projective surface. -/
def projectivePlaneSurfaceTwo : NormalProjectiveSurface Fbar2 := projectivePlaneSurface Fbar2

theorem projectivePlaneSurfaceTwo_toScheme :
    projectivePlaneSurfaceTwo.toScheme = projectiveSpace Fbar2 2 := rfl

/-- The accepted projective plane over `𝔽̄₃` as a normal projective surface. -/
def projectivePlaneSurfaceThree : NormalProjectiveSurface Fbar3 := projectivePlaneSurface Fbar3

theorem projectivePlaneSurfaceThree_toScheme :
    projectivePlaneSurfaceThree.toScheme = projectiveSpace Fbar3 2 := rfl

/-- Accepted `normalProjectiveSurface_nonempty` at `𝔽̄₂`. -/
theorem normalProjectiveSurface_nonempty_two : Nonempty (NormalProjectiveSurface Fbar2) :=
  normalProjectiveSurface_nonempty Fbar2

/-- Accepted `normalProjectiveSurface_nonempty` at `𝔽̄₃`. -/
theorem normalProjectiveSurface_nonempty_three : Nonempty (NormalProjectiveSurface Fbar3) :=
  normalProjectiveSurface_nonempty Fbar3

/-! ### Summary -/

/-- The geometry bundles are instantiated: both graphs are closed subschemes of the
respective products, both fields carry a normal projective surface, and both graphs
carry `n` distinct closed rational points for every `n`. -/
theorem geometry_bundle_witnesses :
    IsClosedImmersion (graphι (k := Fbar2) 2) ∧
    IsClosedImmersion (graphι (k := Fbar3) 3) ∧
    Nonempty (NormalProjectiveSurface Fbar2) ∧
    Nonempty (NormalProjectiveSurface Fbar3) ∧
    (∀ n : ℕ, Nonempty (Fin n ↪ graph (k := Fbar2) 2)) ∧
    (∀ n : ℕ, Nonempty (Fin n ↪ graph (k := Fbar3) 3)) ∧
    (-Additive.ofMul (graphIdealLine (k := Fbar2) 2).toPic =
      2 • firstFiberClass + secondFiberClass) ∧
    (-Additive.ofMul (graphIdealLine (k := Fbar3) 3).toPic =
      3 • firstFiberClass + secondFiberClass) :=
  ⟨graphTwo_isClosedImmersion, graphThree_isClosedImmersion,
    normalProjectiveSurface_nonempty_two, normalProjectiveSurface_nonempty_three,
    fun n => ⟨graphTwoEmbedding n⟩, fun n => ⟨graphThreeEmbedding n⟩,
    graphTwo_class, graphThree_class⟩

end KltDP.Support.GeometryBundleWitnesses
