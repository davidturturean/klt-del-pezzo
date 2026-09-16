import KltDP.Geometry.RationalTreePicardPulledFrameCoordinate

/-!
# Manuscript Lemma 2.2: the Picard group of a rational tree

Source: `source/manuscript.tex`, lines 367–373, label `lem:tree-picard`: for a connected reduced
nodal curve `Z` whose irreducible components are copies of `P¹` and whose dual graph is a tree, the
multidegree map `Pic(Z) → ℤ^{components}` is an isomorphism; in particular a line bundle of degree
zero on every component is trivial.

Lean form (all in one universe `u`): `X : Scheme.{u}` reduced, Noetherian, locally Noetherian,
locally of finite type over an algebraically closed field `k` (`f : X ⟶ Spec k`), of topological
Krull dimension `≤ 1`, with tree component-point incidence graph
`(componentPointIncidenceGraph X).IsTree` (this encodes "connected" and "dual graph a tree", the
vertices being the components and their intersection points) and transverse branch germs at the
intersection points (`HasTransverseComponentBranches X`, the current form of "nodal"), and with
identifications `e C : Z_C ≅ P¹` of the reduced components with the projective line. The
multidegree map is `multidegreeHom k X e : X.Pic →* (components → Multiplicative ℤ)` (component
exponents through the identifications). Then:

* `rationalTreePicard`: the multidegree map is bijective;
* `rationalTreePicardEquiv`: the resulting isomorphism `X.Pic ≃* (components → Multiplicative ℤ)`;
* `rationalTreePicard_trivial_of_degree_zero`: a line bundle with component exponent `0` on every
  component is trivial ("in particular").

The degree used is the accepted transition exponent on `P¹` (`componentExponent`); its comparison
with an independently defined divisor degree is a separate obligation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Manuscript.S02

open KltDP.Geometry KltDP.Geometry.RationalTreePicard

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Manuscript Lemma 2.2 (Picard group of a rational tree): the multidegree map is an
isomorphism. -/
theorem rationalTreePicard (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
    [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (htrans : HasTransverseComponentBranches X)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1) :
    Function.Bijective (multidegreeHom k X e) :=
  multidegreeHom_bijective_final k X f hdim hTree htrans e

/-- The isomorphism `Pic(Z) ≃ ℤ^{components}` of manuscript Lemma 2.2. -/
def rationalTreePicardEquiv (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
    [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (htrans : HasTransverseComponentBranches X)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1) :
    X.Pic ≃* (↥(irreducibleComponents X) → Multiplicative ℤ) :=
  MulEquiv.ofBijective (multidegreeHom k X e) (rationalTreePicard X f hdim hTree htrans e)

/-- "In particular": a line bundle of degree zero on every irreducible component is trivial. -/
theorem rationalTreePicard_trivial_of_degree_zero (X : Scheme.{u}) [NoetherianSpace X]
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (htrans : HasTransverseComponentBranches X)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (L : InvertibleSheaf X)
    (hL : ∀ C : ↥(irreducibleComponents X), componentExponent k X {C} (e C) L = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) :=
  rationalTreePicard_trivial_of_exponents_zero_final k X f hdim hTree htrans e L hL

/-- Universe check: the statement at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (X : Scheme.{0}) [NoetherianSpace X]
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k₀)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (htrans : HasTransverseComponentBranches X)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k₀ 1) :
    Function.Bijective (multidegreeHom k₀ X e) :=
  rationalTreePicard X f hdim hTree htrans e

end KltDP.Manuscript.S02
