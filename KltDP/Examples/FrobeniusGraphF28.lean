import KltDP.Examples.FrobeniusGraphRationalPoints
import KltDP.Examples.FrobeniusGraphPicardClassFiberClasses

/-!
# F28 bundle: the Frobenius graph as a `k`-morphism and arbitrary selected points

`f28_frobenius_graph` states, for an algebraically closed field `k` of characteristic `p`
(`p` prime), every clause of obligation F28 for the accepted actual objects:

1. the coordinate-power morphism `projectivePowerMorphism p` of the actual projective line is
   a morphism over `Spec k`; on rational points `[1:a]` it is the Frobenius `a ↦ a^p` of `k`;
   the absolute Frobenius of the affine coordinate ring is the coefficient Frobenius followed
   by this `k`-linear coordinate-power map;
2. the graph `graph p` is a closed subscheme of `P¹ ×_k P¹` (its inclusion `graphι p` is a
   closed immersion with closed image);
3. the graph is isomorphic to `P¹` by the first projection, the inverse being the graph
   morphism, which is a section of the first projection;
4. in the actual Picard group of the product, the class of the graph (inverse of its ideal
   line) is `p • a + b`, where `a`, `b` are the classes of the actual fibres `x = 1`, `y = 1`;
5. for every `n` there are `n` sections `Spec k ⟶ graph p` of the graph's structure morphism
   with pairwise distinct, closed underlying points whose residue field is `k`
   (the canonical map `k → κ(x)` is bijective);
6. any injective family of such sections has pairwise distinct underlying points, each closed
   with residue field `k` (arbitrary selections, not only `0, 1, ∞`);
7. at each rational point `[1:a]` the graph meets the fibre `y = a^p` with contact length `p`
   in the actual scheme stalk.

Every component is an accepted or lane-proved theorem about the accepted schemes; no clause
is assumed. Hypotheses beyond `[Field k]` are only used where listed in
`F28_CORRESPONDENCE.md`: `[IsAlgClosed k]` for distinctness of underlying points, infinitude
and residue fields; `[Fact p.Prime] [CharP k p]` for the Frobenius identifications and the
contact length.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples

open KltDP.Geometry ProjectiveChart
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
  FrobeniusGraphStalkContact FrobeniusCoordinateFrobenius FrobeniusGraphRationalPoints
  FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassFiberClasses

/-- Obligation F28 for the accepted Frobenius graph, all clauses. -/
theorem f28_frobenius_graph (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    -- (1) the coordinate-power map is a `k`-morphism acting as Frobenius on rational points
    (projectivePowerMorphism (k := k) p ≫ projectiveSpaceToSpec k 1 =
        projectiveSpaceToSpec k 1) ∧
    (∀ a : k, pointMorphism a ≫ projectivePowerMorphism p = pointMorphism (frobenius k p a)) ∧
    (frobenius (affineRing k 1) p =
        (affinePowerHom p).comp (MvPolynomial.map (frobenius k p))) ∧
    -- (2) the graph is a closed subscheme of the product
    IsClosedImmersion (graphι (k := k) p) ∧
    IsClosed (Set.range (graphι (k := k) p).base) ∧
    -- (3) the graph is isomorphic to the projective line, as a section over the first factor
    (∃ e : graph (k := k) p ≅ projectiveSpace k 1,
        e.hom = graphι p ≫ firstProjection ∧ e.inv ≫ graphι p = projectiveGraphMorphism p) ∧
    (projectiveGraphMorphism (k := k) p ≫ firstProjection = 𝟙 (projectiveSpace k 1)) ∧
    -- (4) its class in the actual Picard group of the product is `p • a + b`
    (-Additive.ofMul (graphIdealLine (k := k) p).toPic =
        p • firstFiberClass + secondFiberClass) ∧
    -- (5) `n` distinct closed rational points with residue field `k`, for every `n`
    (∀ n : ℕ, ∃ s : Fin n → (Spec (CommRingCat.of k) ⟶ graph (k := k) p),
        (∀ i, s i ≫ graphToSpec p = 𝟙 (Spec (CommRingCat.of k))) ∧
        Function.Injective (fun i => fieldMorphismPoint (s i)) ∧
        (∀ i, IsClosed ({fieldMorphismPoint (s i)} : Set (graph p))) ∧
        (∀ i, Function.Bijective
          (baseToResidueFieldMap (graphToSpec p) (fieldMorphismPoint (s i))).hom)) ∧
    -- (6) arbitrary selections of distinct rational points
    (∀ (n : ℕ) (s : Fin n → (Spec (CommRingCat.of k) ⟶ graph (k := k) p)),
        (∀ i, s i ≫ graphToSpec p = 𝟙 (Spec (CommRingCat.of k))) → Function.Injective s →
        Function.Injective (fun i => fieldMorphismPoint (s i)) ∧
        (∀ i, IsClosed ({fieldMorphismPoint (s i)} : Set (graph p))) ∧
        (∀ i, Function.Bijective
          (baseToResidueFieldMap (graphToSpec p) (fieldMorphismPoint (s i))).hom)) ∧
    -- (7) contact of order `p` with the `b`-fibre at each rational point `[1:a]`
    (∀ a : k, graphRationalPoint p a = pointOnGraph p a ∧
        Module.length ((graph p).presheaf.stalk (pointOnGraph p a))
          ((graph p).presheaf.stalk (pointOnGraph p a) ⧸ Ideal.span {graphFiberGerm p a}) = p) :=
  ⟨projectivePowerMorphism_over_base p,
    fun a => pointMorphism_projectivePowerMorphism_frobenius p a,
    frobenius_affineRing_eq p,
    graphι_isClosedImmersion p,
    (graphι (k := k) p).isClosedEmbedding.isClosed_range,
    ⟨graphIsoProjectiveLine p, rfl, graphIso_inv_ι p⟩,
    projectiveGraphMorphism_fst p,
    inverse_graphIdeal_picard_eq_actual_fibers p,
    fun n => exists_distinct_closed_rational_points_on_graph p n,
    fun _ s hs hinj => ⟨sections_points_injective p s hs hinj,
      fun i => section_point_isClosed p (hs i),
      fun i => section_point_residue_bijective p (hs i)⟩,
    fun a => ⟨graphRationalPoint_eq_pointOnGraph p a, graphStalk_contact_length p a⟩⟩

end KltDP.Examples
