import KltDP.Geometry.NoTriplePointOfCompletedStalk
import KltDP.Geometry.RationalTreePicardDegreeIdentification

/-!
# Manuscript Lemma 2.2 for nodal curves in the completed-stalk sense, with Euler degrees

Source: `source/manuscript.tex`, lines 367–373, label `lem:tree-picard`: for a connected reduced nodal
curve `Z` whose irreducible components are copies of `P¹` and whose dual graph is a tree, the
multidegree map `Pic(Z) → ℤ^{components}` is an isomorphism; in particular a line bundle of degree zero
on every component is trivial.

This module states the lemma with the manuscript's own hypotheses in place of the two interface
predicates of the accepted `KltDP.Manuscript.S02.rationalTreePicard`:

* **nodal** is the completed-stalk condition: at every point `q` where a component `C` meets the union
  of the other components, `q` is an ordinary double point in the accepted sense
  `IsOrdinaryDoublePoint f q` (closed point with `Ô_{X, q} ≃ₐ[k] k⟦x, y⟧ ⧸ (x y)` as `k`-algebras);
  the transverse-branch predicate `HasTransverseComponentBranches X` is derived from it
  (`hasTransverseComponentBranches_of_completedStalk'`, BRIEF26–28), including the fact that no point
  lies on three components;
* **degree** is the Euler-characteristic degree `deg L|_{Z_C} = χ(L|_{Z_C}) − χ(O_{Z_C})` on each
  component (`eulerMultidegree X f`, BRIEF24), computed on the component with its structure map; the
  identifications `e C : Z_C ≅ P¹` are required to be over `k` (`hfe`), and the multidegree map does
  not otherwise depend on them.

The remaining hypotheses are those of the accepted statement (all in one universe `u`): `k`
algebraically closed, `X : Scheme.{u}` reduced, Noetherian, locally Noetherian, locally of finite type
over `k` via `f`, of topological Krull dimension `≤ 1` ("curve"), with tree component-point incidence
graph (`(componentPointIncidenceGraph X).IsTree`, which encodes "connected" and "dual graph a tree").
Properness of `X` is not assumed: it is not used by the proof (the components are identified with the
proper curve `P¹`, and all Euler characteristics are computed there).

* `rationalTreePicardNodal`: the Euler multidegree `Pic X → ℤ^{components}` is bijective;
* `eulerMultidegree_mul`: it is a homomorphism (tensor product to sum), so
* `rationalTreePicardNodalEquiv : Additive X.Pic ≃+ (components → ℤ)` is the isomorphism
  `Pic(Z) ≅ ℤ^{components}` of Lemma 2.2, with `rationalTreePicardNodalEquiv_apply`;
* `rationalTreePicardNodal_trivial_of_degree_zero`: a line bundle of Euler degree `0` on every
  component is trivial ("in particular").
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

variable {k : Type u} [Field k] (X : Scheme.{u}) [NoetherianSpace X]

/-- The Euler multidegree is a homomorphism `X.Pic → ℤ^{components}` when the identifications are
over `k`. -/
theorem eulerMultidegree_mul (f : X ⟶ Spec (CommRingCat.of k))
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (hfe : ∀ C, (e C).hom ≫ projectiveSpaceToSpec k 1 = componentUnionInclusion X {C} ≫ f)
    (p p' : X.Pic) :
    eulerMultidegree X f (p * p') = eulerMultidegree X f p + eulerMultidegree X f p' := by
  rw [eulerMultidegree_eq X f e hfe, eulerMultidegree_eq X f e hfe, eulerMultidegree_eq X f e hfe]
  funext C
  simp only [Pi.add_apply, map_mul, Pi.mul_apply, toAdd_mul]

end KltDP.Geometry.RationalTreePicard

namespace KltDP.Manuscript.S02

open KltDP.Geometry KltDP.Geometry.RationalTreePicard KltDP.Geometry.IntrinsicNodal

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Manuscript Lemma 2.2 (Picard group of a rational tree), nodal form.** For a connected reduced
curve `X` over the algebraically closed field `k` whose irreducible components are identified with `P¹`
over `k`, whose points where a component meets the other components are ordinary double points
(`Ô_{X, q} ≃ₐ[k] k⟦x, y⟧ ⧸ (x y)`) and whose dual graph is a tree, the Euler multidegree
`Pic X → ℤ^{components}`, `L ↦ (χ(L|_{Z_C}) − χ(O_{Z_C}))_C`, is bijective. -/
theorem rationalTreePicardNodal (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
    [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (hnode : ∀ (C : ↥(irreducibleComponents X)) (q : X), q ∈ C.1 →
      q ∈ (componentClosedUnion X ({C}ᶜ) : Set X) → IsOrdinaryDoublePoint f q)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (hfe : ∀ C, (e C).hom ≫ projectiveSpaceToSpec k 1 = componentUnionInclusion X {C} ≫ f) :
    Function.Bijective (eulerMultidegree X f) :=
  rationalTreePicard_degrees X f hdim hTree
    (hasTransverseComponentBranches_of_completedStalk' X f
      fun C q hqC hqCc => (hnode C q hqC hqCc).2.some) e hfe

/-- The isomorphism `Pic(Z) ≅ ℤ^{components}` of manuscript Lemma 2.2 (nodal form), given by Euler
degrees; the Picard group is written additively. -/
def rationalTreePicardNodalEquiv (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
    [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (hnode : ∀ (C : ↥(irreducibleComponents X)) (q : X), q ∈ C.1 →
      q ∈ (componentClosedUnion X ({C}ᶜ) : Set X) → IsOrdinaryDoublePoint f q)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (hfe : ∀ C, (e C).hom ≫ projectiveSpaceToSpec k 1 = componentUnionInclusion X {C} ≫ f) :
    Additive X.Pic ≃+ (↥(irreducibleComponents X) → ℤ) :=
  AddEquiv.mk'
    (Additive.toMul.trans
      (Equiv.ofBijective _ (rationalTreePicardNodal X f hdim hTree hnode e hfe)))
    fun x y => by
      show eulerMultidegree X f (Additive.toMul (x + y)) =
        eulerMultidegree X f (Additive.toMul x) + eulerMultidegree X f (Additive.toMul y)
      rw [toMul_add]
      exact eulerMultidegree_mul X f e hfe _ _

theorem rationalTreePicardNodalEquiv_apply (X : Scheme.{u}) [NoetherianSpace X]
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (hnode : ∀ (C : ↥(irreducibleComponents X)) (q : X), q ∈ C.1 →
      q ∈ (componentClosedUnion X ({C}ᶜ) : Set X) → IsOrdinaryDoublePoint f q)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (hfe : ∀ C, (e C).hom ≫ projectiveSpaceToSpec k 1 = componentUnionInclusion X {C} ≫ f)
    (p : X.Pic) :
    rationalTreePicardNodalEquiv X f hdim hTree hnode e hfe (Additive.ofMul p) =
      eulerMultidegree X f p :=
  rfl

/-- "In particular": a line bundle of Euler degree zero on every irreducible component is trivial. -/
theorem rationalTreePicardNodal_trivial_of_degree_zero (X : Scheme.{u}) [NoetherianSpace X]
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (hnode : ∀ (C : ↥(irreducibleComponents X)) (q : X), q ∈ C.1 →
      q ∈ (componentClosedUnion X ({C}ᶜ) : Set X) → IsOrdinaryDoublePoint f q)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (hfe : ∀ C, (e C).hom ≫ projectiveSpaceToSpec k 1 = componentUnionInclusion X {C} ≫ f)
    (L : InvertibleSheaf X) (hL : ∀ C : ↥(irreducibleComponents X),
      eulerDegree (componentUnionInclusion X {C} ≫ f) (componentUnionRestriction X {C} L) = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) :=
  rationalTreePicard_degrees_trivial X f hdim hTree
    (hasTransverseComponentBranches_of_completedStalk' X f
      fun C q hqC hqCc => (hnode C q hqC hqCc).2.some) e hfe L hL

/-- Universe check: the statement at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (X : Scheme.{0}) [NoetherianSpace X]
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k₀)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (hnode : ∀ (C : ↥(irreducibleComponents X)) (q : X), q ∈ C.1 →
      q ∈ (componentClosedUnion X ({C}ᶜ) : Set X) → IsOrdinaryDoublePoint f q)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k₀ 1)
    (hfe : ∀ C, (e C).hom ≫ projectiveSpaceToSpec k₀ 1 = componentUnionInclusion X {C} ≫ f) :
    Additive X.Pic ≃+ (↥(irreducibleComponents X) → ℤ) :=
  rationalTreePicardNodalEquiv X f hdim hTree hnode e hfe

end KltDP.Manuscript.S02
