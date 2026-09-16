import KltDP.Manuscript.S02.RationalTreePicardNodalCurveStatement
import KltDP.Geometry.PicardClopenDecomposition
import KltDP.Topology.Dimension

/-!
# Manuscript Lemma 2.2 for a disjoint union of rational trees (forest form)

The forest (disjoint-union) variant of `lem:tree-picard` (THEOREM_MAP strategy item 3): a scheme
`X` decomposed into clopen pieces `X = ⊔ᵢ Uᵢ` (`U : ι → X.Opens` pairwise disjoint and covering, `ι` any
index type in universe `u`), each piece a rational tree in the sense of the accepted Lemma 2.2, has
`Pic X ≅ ∏ᵢ ℤ^{components of Uᵢ}` via Euler degrees.

* `forestEulerMultidegree X f U : X.Pic → ∀ i, components (Uᵢ) → ℤ`: restrict a class to each clopen
  piece (`restrictionPi`, the accepted clopen Picard decomposition) and take the Euler multidegree of
  the piece with its structure map `(Uᵢ).ι ≫ f`; `forestEulerMultidegree_mul` (it is a homomorphism).
* `rationalForestPicard_degrees` (transverse-branch form) and **`KltDP.Manuscript.S02.rationalForestPicard`**
  (nodal form, hypotheses on each piece: components ≅ `P¹` over `k`, `IsOrdinaryDoublePoint` at the
  points where a component meets the other components of the piece, tree component-point incidence
  graph): the forest Euler multidegree is bijective. The proof composes the accepted
  `picardEquiv : X.Pic ≃* ∀ i, (Uᵢ).Pic` with the piecewise `rationalTreePicard_degrees`.
* `rationalForestPicardEquiv : Additive X.Pic ≃+ (∀ i, components (Uᵢ) → ℤ)` and
  `rationalForestPicard_trivial_of_degree_zero`.

Conventions. The global hypotheses are those of the accepted statement on `X` (`k` algebraically closed,
`X` reduced, Noetherian, locally Noetherian, locally of finite type over `k`, `dim X ≤ 1`); they descend
to the open pieces (`opens_noetherianSpace`, Mathlib's `isLocallyNoetherian_of_isOpenImmersion`,
`isReduced_of_isOpenImmersion`, `locallyOfFiniteType_comp`, and the accepted
`topologicalKrullDim_opens_le`). "The component-point incidence graph of `X` is a forest whose connected
components are the pieces" is imposed piecewise, as `hTree i : (componentPointIncidenceGraph Uᵢ).IsTree`
for every `i`; the identification of the components of `X` with the disjoint union of the components of
the pieces is not part of this module (the conclusion is stated on the pieces' components).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

open KltDP.Geometry KltDP.Geometry.PicardClopenDecomposition KltDP.Geometry.IntrinsicNodal

variable {k : Type u} [Field k] (X : Scheme.{u})

/-- Open subschemes of a Noetherian scheme are Noetherian. -/
instance opens_noetherianSpace [NoetherianSpace X] (U : X.Opens) : NoetherianSpace U.toScheme :=
  U.ι.isOpenEmbedding.isInducing.noetherianSpace

variable [NoetherianSpace X] (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type u} [DecidableEq ι]
  (U : ι → X.Opens)

/-- The forest Euler multidegree: restrict a Picard class to each clopen piece and take the Euler
multidegree of the piece with its structure map. -/
def forestEulerMultidegree (p : X.Pic) : ∀ i, ↥(irreducibleComponents (U i).toScheme) → ℤ :=
  fun i => eulerMultidegree (U i).toScheme ((U i).ι ≫ f) (KltDP.Geometry.PicardClopenDecomposition.restrictionPi U p i)

omit [DecidableEq ι] in
theorem forestEulerMultidegree_apply (p : X.Pic) (i : ι) :
    forestEulerMultidegree X f U p i =
      eulerMultidegree (U i).toScheme ((U i).ι ≫ f) (schemePicardPullbackHom (U i).ι p) := rfl

omit [DecidableEq ι] in
/-- The forest Euler multidegree is a homomorphism when the identifications of the components of the
pieces with `P¹` are over `k`. -/
theorem forestEulerMultidegree_mul
    (e : ∀ i (C : ↥(irreducibleComponents (U i).toScheme)),
      componentUnionScheme (U i).toScheme {C} ≅ projectiveSpace k 1)
    (hfe : ∀ i C, (e i C).hom ≫ projectiveSpaceToSpec k 1 =
      componentUnionInclusion (U i).toScheme {C} ≫ ((U i).ι ≫ f))
    (p p' : X.Pic) :
    forestEulerMultidegree X f U (p * p') =
      forestEulerMultidegree X f U p + forestEulerMultidegree X f U p' := by
  funext i
  show eulerMultidegree (U i).toScheme ((U i).ι ≫ f) (KltDP.Geometry.PicardClopenDecomposition.restrictionPi U (p * p') i) =
    eulerMultidegree (U i).toScheme ((U i).ι ≫ f) (KltDP.Geometry.PicardClopenDecomposition.restrictionPi U p i) +
      eulerMultidegree (U i).toScheme ((U i).ι ≫ f) (KltDP.Geometry.PicardClopenDecomposition.restrictionPi U p' i)
  rw [map_mul, Pi.mul_apply, eulerMultidegree_mul (U i).toScheme ((U i).ι ≫ f) (e i) (hfe i)]

variable [IsAlgClosed k]

/-- **Lemma 2.2, forest form (transverse-branch nodality).** For a clopen decomposition `X = ⊔ᵢ Uᵢ` of
a reduced Noetherian curve over `k` whose pieces are rational trees (tree incidence graph, transverse
component branches, components ≅ `P¹` over `k`), the forest Euler multidegree
`Pic X → ∏ᵢ ℤ^{components of Uᵢ}` is bijective. -/
theorem rationalForestPicard_degrees [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    [LocallyOfFiniteType f] (hdisj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (hcov : (⨆ i, U i) = ⊤)
    (hdim : topologicalKrullDim X ≤ 1)
    (hTree : ∀ i, (componentPointIncidenceGraph (U i).toScheme).IsTree)
    (htrans : ∀ i, HasTransverseComponentBranches (U i).toScheme)
    (e : ∀ i (C : ↥(irreducibleComponents (U i).toScheme)),
      componentUnionScheme (U i).toScheme {C} ≅ projectiveSpace k 1)
    (hfe : ∀ i C, (e i C).hom ≫ projectiveSpaceToSpec k 1 =
      componentUnionInclusion (U i).toScheme {C} ≫ ((U i).ι ≫ f)) :
    Function.Bijective (forestEulerMultidegree X f U) := by
  have hpiece : ∀ i, Function.Bijective (eulerMultidegree (U i).toScheme ((U i).ι ≫ f)) := by
    intro i
    haveI : IsLocallyNoetherian (U i).toScheme := isLocallyNoetherian_of_isOpenImmersion (U i).ι
    haveI : AlgebraicGeometry.IsReduced (U i).toScheme := isReduced_of_isOpenImmersion (U i).ι
    exact rationalTreePicard_degrees (U i).toScheme ((U i).ι ≫ f)
      ((KltDP.Topology.topologicalKrullDim_opens_le (U i)).trans hdim) (hTree i) (htrans i) (e i)
      (hfe i)
  have h : forestEulerMultidegree X f U =
      (fun c i => eulerMultidegree (U i).toScheme ((U i).ι ≫ f) (c i)) ∘
        KltDP.Geometry.PicardClopenDecomposition.picardEquiv U hdisj hcov := by
    funext p
    funext i
    rfl
  rw [h]
  exact (Equiv.piCongrRight fun i => Equiv.ofBijective _ (hpiece i)).bijective.comp
    (KltDP.Geometry.PicardClopenDecomposition.picardEquiv U hdisj hcov).bijective

end KltDP.Geometry.RationalTreePicard

namespace KltDP.Manuscript.S02

open KltDP.Geometry KltDP.Geometry.RationalTreePicard KltDP.Geometry.IntrinsicNodal

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Manuscript Lemma 2.2, forest form.** For a reduced curve `X` over the algebraically closed field
`k` with a clopen decomposition `X = ⊔ᵢ Uᵢ` into rational trees — each piece has components identified
with `P¹` over `k`, ordinary double points (`Ô ≃ₐ[k] k⟦x, y⟧ ⧸ (x y)`) where a component meets the other
components of the piece, and tree incidence graph — the forest Euler multidegree
`Pic X → ∏ᵢ ℤ^{components of Uᵢ}` is bijective. -/
theorem rationalForestPicard (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
    [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    {ι : Type u} [DecidableEq ι] (U : ι → X.Opens)
    (hdisj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (hcov : (⨆ i, U i) = ⊤)
    (hdim : topologicalKrullDim X ≤ 1)
    (hTree : ∀ i, (componentPointIncidenceGraph (U i).toScheme).IsTree)
    (hnode : ∀ i (C : ↥(irreducibleComponents (U i).toScheme)) (q : (U i).toScheme), q ∈ C.1 →
      q ∈ (componentClosedUnion (U i).toScheme ({C}ᶜ) : Set (U i).toScheme) →
      IsOrdinaryDoublePoint ((U i).ι ≫ f) q)
    (e : ∀ i (C : ↥(irreducibleComponents (U i).toScheme)),
      componentUnionScheme (U i).toScheme {C} ≅ projectiveSpace k 1)
    (hfe : ∀ i C, (e i C).hom ≫ projectiveSpaceToSpec k 1 =
      componentUnionInclusion (U i).toScheme {C} ≫ ((U i).ι ≫ f)) :
    Function.Bijective (forestEulerMultidegree X f U) :=
  rationalForestPicard_degrees X f U hdisj hcov hdim hTree
    (fun i => by
      haveI : IsLocallyNoetherian (U i).toScheme := isLocallyNoetherian_of_isOpenImmersion (U i).ι
      haveI : AlgebraicGeometry.IsReduced (U i).toScheme := isReduced_of_isOpenImmersion (U i).ι
      exact hasTransverseComponentBranches_of_completedStalk' (U i).toScheme ((U i).ι ≫ f)
        fun C q hqC hqCc => (hnode i C q hqC hqCc).2.some)
    e hfe

/-- The isomorphism `Pic X ≅ ∏ᵢ ℤ^{components of Uᵢ}` of the forest form, given by Euler degrees; the
Picard group is written additively. -/
def rationalForestPicardEquiv (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
    [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    {ι : Type u} [DecidableEq ι] (U : ι → X.Opens)
    (hdisj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (hcov : (⨆ i, U i) = ⊤)
    (hdim : topologicalKrullDim X ≤ 1)
    (hTree : ∀ i, (componentPointIncidenceGraph (U i).toScheme).IsTree)
    (hnode : ∀ i (C : ↥(irreducibleComponents (U i).toScheme)) (q : (U i).toScheme), q ∈ C.1 →
      q ∈ (componentClosedUnion (U i).toScheme ({C}ᶜ) : Set (U i).toScheme) →
      IsOrdinaryDoublePoint ((U i).ι ≫ f) q)
    (e : ∀ i (C : ↥(irreducibleComponents (U i).toScheme)),
      componentUnionScheme (U i).toScheme {C} ≅ projectiveSpace k 1)
    (hfe : ∀ i C, (e i C).hom ≫ projectiveSpaceToSpec k 1 =
      componentUnionInclusion (U i).toScheme {C} ≫ ((U i).ι ≫ f)) :
    Additive X.Pic ≃+ (∀ i, ↥(irreducibleComponents (U i).toScheme) → ℤ) :=
  AddEquiv.mk'
    (Additive.toMul.trans
      (Equiv.ofBijective _ (rationalForestPicard X f U hdisj hcov hdim hTree hnode e hfe)))
    fun x y => by
      show forestEulerMultidegree X f U (Additive.toMul (x + y)) =
        forestEulerMultidegree X f U (Additive.toMul x) +
          forestEulerMultidegree X f U (Additive.toMul y)
      rw [toMul_add]
      exact forestEulerMultidegree_mul X f U e hfe _ _

/-- "In particular": a line bundle whose restriction to every piece has Euler degree zero on every
component is trivial. -/
theorem rationalForestPicard_trivial_of_degree_zero (X : Scheme.{u}) [NoetherianSpace X]
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    {ι : Type u} [DecidableEq ι] (U : ι → X.Opens)
    (hdisj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (hcov : (⨆ i, U i) = ⊤)
    (hdim : topologicalKrullDim X ≤ 1)
    (hTree : ∀ i, (componentPointIncidenceGraph (U i).toScheme).IsTree)
    (hnode : ∀ i (C : ↥(irreducibleComponents (U i).toScheme)) (q : (U i).toScheme), q ∈ C.1 →
      q ∈ (componentClosedUnion (U i).toScheme ({C}ᶜ) : Set (U i).toScheme) →
      IsOrdinaryDoublePoint ((U i).ι ≫ f) q)
    (e : ∀ i (C : ↥(irreducibleComponents (U i).toScheme)),
      componentUnionScheme (U i).toScheme {C} ≅ projectiveSpace k 1)
    (hfe : ∀ i C, (e i C).hom ≫ projectiveSpaceToSpec k 1 =
      componentUnionInclusion (U i).toScheme {C} ≫ ((U i).ι ≫ f))
    (L : InvertibleSheaf X) (hL : forestEulerMultidegree X f U L.toPic = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) := by
  rw [← toPic_eq_one_iff_iso_unit]
  have h := (rationalForestPicardEquiv X f U hdisj hcov hdim hTree hnode e hfe).map_eq_zero_iff
    (x := Additive.ofMul L.toPic)
  exact h.mp hL

/-- Universe check: the statement at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (X : Scheme.{0}) [NoetherianSpace X]
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k₀)) [LocallyOfFiniteType f]
    {ι : Type} [DecidableEq ι] (U : ι → X.Opens)
    (hdisj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (hcov : (⨆ i, U i) = ⊤)
    (hdim : topologicalKrullDim X ≤ 1)
    (hTree : ∀ i, (componentPointIncidenceGraph (U i).toScheme).IsTree)
    (hnode : ∀ i (C : ↥(irreducibleComponents (U i).toScheme)) (q : (U i).toScheme), q ∈ C.1 →
      q ∈ (componentClosedUnion (U i).toScheme ({C}ᶜ) : Set (U i).toScheme) →
      IsOrdinaryDoublePoint ((U i).ι ≫ f) q)
    (e : ∀ i (C : ↥(irreducibleComponents (U i).toScheme)),
      componentUnionScheme (U i).toScheme {C} ≅ projectiveSpace k₀ 1)
    (hfe : ∀ i C, (e i C).hom ≫ projectiveSpaceToSpec k₀ 1 =
      componentUnionInclusion (U i).toScheme {C} ≫ ((U i).ι ≫ f)) :
    Additive X.Pic ≃+ (∀ i, ↥(irreducibleComponents (U i).toScheme) → ℤ) :=
  rationalForestPicardEquiv X f U hdisj hcov hdim hTree hnode e hfe

end KltDP.Manuscript.S02
