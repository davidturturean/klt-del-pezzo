import KltDP.Geometry.RationalTreePicardDegreeIdentification
import KltDP.Geometry.RationalTreePicardChainOfCurves
import KltDP.Examples.FrobeniusExceptionalHalfClass

/-!
# Lemma 2.2 in Euler-degree form for configurations of projective lines over the base

BRIEF25, task 1 (generic part). The convention-free Lemma 2.2 of
`RationalTreePicardDegreeIdentification` (`rationalTreePicard_degrees`: the Euler multidegree
`Pic X → ℤ^{components}`, `p ↦ (χ(p|_{Z_C}) − χ(O_{Z_C}))_C`, is bijective) carries the hypothesis
`hfe` that the identifications `e C : Z_C ≅ P¹` are over `k`. For a configuration of projective
lines given by closed immersions `c j : P¹ ⟶ X` (`RationalTreePicardOfConfiguration`), the
identification `lineIdentification C` is the inverse of the lift `curveLift C : P¹ ⟶ Z_C` of the
curve (`lineIdentification_inv`), so `hfe` follows from `c j ≫ f = projectiveSpaceToSpec k 1` for
every curve — the curves are `k`-morphisms (`lineIdentification_hom_comp_structure`).
Consequences, for a structure map `f : X ⟶ Spec k` with this property:

* whenever the multidegree map of the configuration is bijective, so is its Euler multidegree
  (`bijective_eulerMultidegree_of_configuration`), and the half-class clause holds in Euler-degree
  form (`pullback_eq_one_of_eulerMultidegree_sq_eq_zero_of_configuration`: a class of the ambient
  scheme whose double has Euler degree zero on every curve restricts trivially);
* the corollary of Lemma 2.2 for transversal configurations of `k`-lines in Euler-degree form
  (`rationalTreePicard_degrees_of_configuration`, `trivial_of_eulerDegree_zero_of_configuration`);
* the same for the chains of projective lines of `RationalTreePicardChainOfCurves`
  (`CurveChain.rationalTreePicard_degrees`, `CurveChain.trivial_of_eulerDegree_zero`,
  `CurveChain.pullback_eq_one_of_eulerMultidegree_sq_eq_zero`), from
  `c i ≫ π = projectiveSpaceToSpec k 1`.

The facts `eulerMultidegree_one`, `bijective_eulerMultidegree_of_bijective_multidegree`,
`eq_one_of_eulerMultidegree_eq_zero` and `trivial_of_eulerDegree_zero_of_bijective` need no
configuration. The concrete identifications (both witnesses, the exceptional chains of the contact
towers and of `S_{p,n}`, the whole exceptional locus) are treated in
`Examples/FrobeniusExceptionalEulerDegrees`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

open KltDP.Geometry KltDP.Geometry.ModuleCohomology

variable {k : Type u} [Field k]

/-! ## Generic facts about the Euler multidegree -/

section Generic

variable (X : Scheme.{u}) [NoetherianSpace X] (f : X ⟶ Spec (CommRingCat.of k))

/-- The Euler multidegree of the trivial class is zero. -/
theorem eulerMultidegree_one : eulerMultidegree X f 1 = 0 := by
  funext C
  show picardEulerDegree (componentUnionInclusion X {C} ≫ f)
    (schemePicardPullbackHom (componentUnionInclusion X {C}) 1) = 0
  rw [map_one]
  exact sub_self _

/-- If the multidegree map of the accepted Lemma 2.2 is bijective and the identifications are over
`k`, the Euler multidegree is bijective. -/
theorem bijective_eulerMultidegree_of_bijective_multidegree
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (hfe : ∀ C, (e C).hom ≫ projectiveSpaceToSpec k 1 = componentUnionInclusion X {C} ≫ f)
    (hbij : Function.Bijective (multidegreeHom k X e)) :
    Function.Bijective (eulerMultidegree X f) := by
  have h : eulerMultidegree X f = fun p C => Multiplicative.toAdd (multidegreeHom k X e p C) := by
    funext p
    exact eulerMultidegree_eq X f e hfe p
  rw [h]
  exact (Equiv.piCongrRight fun _ : ↥(irreducibleComponents X) =>
    (Multiplicative.toAdd : Multiplicative ℤ ≃ ℤ)).bijective.comp hbij

/-- When the Euler multidegree is bijective, a class of Euler degree zero on every component is
trivial. -/
theorem eq_one_of_eulerMultidegree_eq_zero (hbij : Function.Bijective (eulerMultidegree X f))
    (p : X.Pic) (hp : eulerMultidegree X f p = 0) : p = 1 :=
  hbij.1 (hp.trans (eulerMultidegree_one X f).symm)

/-- When the Euler multidegree is bijective, a line bundle whose restriction to every component has
Euler degree zero is trivial. -/
theorem trivial_of_eulerDegree_zero_of_bijective (hbij : Function.Bijective (eulerMultidegree X f))
    (L : InvertibleSheaf X) (hL : ∀ C : ↥(irreducibleComponents X),
      eulerDegree (componentUnionInclusion X {C} ≫ f) (componentUnionRestriction X {C} L) = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) := by
  rw [← toPic_eq_one_iff_iso_unit]
  apply eq_one_of_eulerMultidegree_eq_zero X f hbij
  funext C
  show eulerMultidegree X f L.toPic C = 0
  rw [eulerMultidegree_toPic X f L C, hL C]

end Generic

/-! ## Configurations of projective lines: the identifications are over `k` -/

section Configuration

variable (X : Scheme.{u}) [NoetherianSpace X] {J : Type u} [Fintype J]
  (c : J → (projectiveSpace k 1 ⟶ X)) [∀ j, IsClosedImmersion (c j)]
  (hcover : ⋃ j, Set.range (c j).base = Set.univ)
  (hdistinct : ∀ i j, Set.range (c i).base ⊆ Set.range (c j).base → i = j)
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The inverse of the identification of a component with `P¹` is the lift of its curve. -/
theorem lineIdentification_inv (C : ↥(irreducibleComponents X)) :
    (lineIdentification X c hcover hdistinct C).inv =
      curveLift X (fun _ => projectiveSpace k 1) c (fun _ => projectiveLine_isIntegral) hcover
        hdistinct C := rfl

theorem lineIdentification_inv_comp (C : ↥(irreducibleComponents X)) :
    (lineIdentification X c hcover hdistinct C).inv ≫ componentUnionInclusion X {C} =
      c (curveOf X (fun _ => projectiveSpace k 1) c (fun _ => projectiveLine_isIntegral) hcover
        hdistinct C) := by
  rw [lineIdentification_inv]
  exact curveLift_comp X (fun _ => projectiveSpace k 1) c (fun _ => projectiveLine_isIntegral)
    hcover hdistinct C

/-- **The identifications of a configuration of `k`-lines are over `k`**: if every curve is a
`k`-morphism (`c j ≫ f = projectiveSpaceToSpec k 1`), the hypothesis `hfe` of
`rationalTreePicard_degrees` holds for `lineIdentification`. -/
theorem lineIdentification_hom_comp_structure
    (hc : ∀ j, c j ≫ f = projectiveSpaceToSpec k 1) (C : ↥(irreducibleComponents X)) :
    (lineIdentification X c hcover hdistinct C).hom ≫ projectiveSpaceToSpec k 1 =
      componentUnionInclusion X {C} ≫ f := by
  rw [← Iso.eq_inv_comp, ← Category.assoc, lineIdentification_inv_comp, hc]

/-- The Euler multidegree of a configuration of `k`-lines is the multidegree of Lemma 2.2. -/
theorem eulerMultidegree_eq_of_configuration (hc : ∀ j, c j ≫ f = projectiveSpaceToSpec k 1)
    (p : X.Pic) :
    eulerMultidegree X f p = fun C =>
      Multiplicative.toAdd (multidegreeHom k X (lineIdentification X c hcover hdistinct) p C) :=
  eulerMultidegree_eq X f _ (lineIdentification_hom_comp_structure X c hcover hdistinct f hc) p

/-- If the multidegree map of a configuration of `k`-lines is bijective, so is its Euler
multidegree. -/
theorem bijective_eulerMultidegree_of_configuration (hc : ∀ j, c j ≫ f = projectiveSpaceToSpec k 1)
    (hbij : Function.Bijective (multidegreeHom k X (lineIdentification X c hcover hdistinct))) :
    Function.Bijective (eulerMultidegree X f) :=
  bijective_eulerMultidegree_of_bijective_multidegree X f _
    (lineIdentification_hom_comp_structure X c hcover hdistinct f hc) hbij

variable {S : Scheme.{u}} (ι : X ⟶ S)

/-- **The half-class clause in Euler-degree form.** A class `M` of the ambient scheme whose double
restricts to a class of Euler degree zero on every curve restricts trivially. -/
theorem pullback_eq_one_of_eulerMultidegree_sq_eq_zero_of_configuration
    (hc : ∀ j, c j ≫ f = projectiveSpaceToSpec k 1)
    (hbij : Function.Bijective (multidegreeHom k X (lineIdentification X c hcover hdistinct)))
    (M : S.Pic) (h : eulerMultidegree X f (schemePicardPullbackHom ι (M ^ 2)) = 0) :
    schemePicardPullbackHom ι M = 1 := by
  apply pullback_eq_one_of_multidegree_sq_eq_one X _ ι hbij M
  intro C
  rw [eulerMultidegree_eq_of_configuration X c hcover hdistinct f hc] at h
  have hC : Multiplicative.toAdd (multidegreeHom k X (lineIdentification X c hcover hdistinct)
      (schemePicardPullbackHom ι (M ^ 2)) C) = 0 := congrFun h C
  exact toAdd_eq_zero.mp hC

end Configuration

/-! ## The corollary for transversal configurations of `k`-lines -/

section Corollary

variable [IsAlgClosed k] (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
  [AlgebraicGeometry.IsReduced X] {S : Scheme.{u}} (ι : X ⟶ S) [IsClosedImmersion ι]
  (π : S ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType π]
  (hconf : TransversalConfiguration ι)
  (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
  {J : Type u} [Fintype J] (c : J → (projectiveSpace k 1 ⟶ X)) [∀ j, IsClosedImmersion (c j)]
  (hcover : ⋃ j, Set.range (c j).base = Set.univ)
  (hdistinct : ∀ i j, Set.range (c i).base ⊆ Set.range (c j).base → i = j)
  (hc : ∀ j, c j ≫ ι ≫ π = projectiveSpaceToSpec k 1)

include hconf hdim hTree hcover hdistinct hc in
/-- **Corollary of Lemma 2.2 for a transversal configuration of `k`-lines, in Euler-degree form.**
The Euler multidegree `Pic X → ℤ^{components}` is bijective. -/
theorem rationalTreePicard_degrees_of_configuration :
    Function.Bijective (eulerMultidegree X (ι ≫ π)) :=
  bijective_eulerMultidegree_of_configuration X c hcover hdistinct (ι ≫ π) hc
    (rationalTreePicard_of_configuration X ι π hconf hdim hTree c hcover hdistinct)

include hconf hdim hTree hcover hdistinct hc in
/-- The degree-zero clause in Euler-degree form: a line bundle of Euler degree zero on every curve
is trivial. -/
theorem trivial_of_eulerDegree_zero_of_configuration (L : InvertibleSheaf X)
    (hL : ∀ C : ↥(irreducibleComponents X),
      eulerDegree (componentUnionInclusion X {C} ≫ ι ≫ π) (componentUnionRestriction X {C} L) = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) :=
  trivial_of_eulerDegree_zero_of_bijective X (ι ≫ π)
    (rationalTreePicard_degrees_of_configuration X ι π hconf hdim hTree c hcover hdistinct hc) L hL

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (X₀ : Scheme.{0}) [NoetherianSpace X₀]
    [IsLocallyNoetherian X₀] [AlgebraicGeometry.IsReduced X₀] {S₀ : Scheme.{0}} (ι₀ : X₀ ⟶ S₀)
    [IsClosedImmersion ι₀] (π₀ : S₀ ⟶ Spec (CommRingCat.of k₀)) [LocallyOfFiniteType π₀]
    (hconf : TransversalConfiguration ι₀) (hdim : topologicalKrullDim X₀ ≤ 1)
    (hTree : (componentPointIncidenceGraph X₀).IsTree) {J₀ : Type} [Fintype J₀]
    (c₀ : J₀ → (projectiveSpace k₀ 1 ⟶ X₀)) [∀ j, IsClosedImmersion (c₀ j)]
    (hcover : ⋃ j, Set.range (c₀ j).base = Set.univ)
    (hdistinct : ∀ i j, Set.range (c₀ i).base ⊆ Set.range (c₀ j).base → i = j)
    (hc : ∀ j, c₀ j ≫ ι₀ ≫ π₀ = projectiveSpaceToSpec k₀ 1) :
    Function.Bijective (eulerMultidegree X₀ (ι₀ ≫ π₀)) :=
  rationalTreePicard_degrees_of_configuration X₀ ι₀ π₀ hconf hdim hTree c₀ hcover hdistinct hc

end Corollary

end KltDP.Geometry.RationalTreePicard

/-! ## Chains of `k`-lines -/

namespace KltDP.Geometry.CurveChain

open KltDP.Geometry KltDP.Geometry.RationalTreePicard

variable {k : Type u} [Field k] (S : Scheme.{u}) (m : ℕ)
  (c : Fin (m + 1) → (projectiveSpace k 1 ⟶ S)) [∀ i, IsClosedImmersion (c i)]
  (π : S ⟶ Spec (CommRingCat.of k))

/-- The curves of a chain of `k`-lines are `k`-morphisms of the chain. -/
theorem curve_comp_structure (hc : ∀ i, c i ≫ π = projectiveSpaceToSpec k 1)
    (i : ULift.{u} (Fin (m + 1))) :
    curve S m c i ≫ inclusion S m c ≫ π = projectiveSpaceToSpec k 1 := by
  rw [← Category.assoc, curve_comp, hc]

variable [IsAlgClosed k] [NoetherianSpace S] [IsLocallyNoetherian S] [LocallyOfFiniteType π]
  (hd : ChainData S m c) (htrans : Transversal S m c hd)
  (hc : ∀ i, c i ≫ π = projectiveSpaceToSpec k 1)

include hd htrans hc in
/-- **Lemma 2.2 in Euler-degree form for a chain of `k`-lines**: the Euler multidegree of the
chain (with structure map `inclusion ≫ π`) is bijective. -/
theorem rationalTreePicard_degrees :
    Function.Bijective (eulerMultidegree (scheme S m c) (inclusion S m c ≫ π)) :=
  bijective_eulerMultidegree_of_configuration (scheme S m c) (curve S m c) (curve_cover S m c)
    (curve_distinct S m c hd) (inclusion S m c ≫ π) (curve_comp_structure S m c π hc)
    (CurveChain.rationalTreePicard S m c π hd htrans)

include hd htrans hc in
/-- A line bundle on the chain of Euler degree zero on every component is trivial. -/
theorem trivial_of_eulerDegree_zero (L : InvertibleSheaf (scheme S m c))
    (hL : ∀ C : ↥(irreducibleComponents (scheme S m c)),
      eulerDegree (componentUnionInclusion (scheme S m c) {C} ≫ inclusion S m c ≫ π)
        (componentUnionRestriction (scheme S m c) {C} L) = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit (scheme S m c).ringCatSheaf) :=
  trivial_of_eulerDegree_zero_of_bijective (scheme S m c) (inclusion S m c ≫ π)
    (CurveChain.rationalTreePicard_degrees S m c π hd htrans hc) L hL

include hd htrans hc in
/-- The half-class clause in Euler-degree form: a class of `S` whose double has Euler degree zero
on every curve of the chain restricts trivially to the chain. -/
theorem pullback_eq_one_of_eulerMultidegree_sq_eq_zero (M : S.Pic)
    (h : eulerMultidegree (scheme S m c) (inclusion S m c ≫ π)
      (schemePicardPullbackHom (inclusion S m c) (M ^ 2)) = 0) :
    schemePicardPullbackHom (inclusion S m c) M = 1 :=
  pullback_eq_one_of_eulerMultidegree_sq_eq_zero_of_configuration (scheme S m c) (curve S m c)
    (curve_cover S m c) (curve_distinct S m c hd) (inclusion S m c ≫ π) (inclusion S m c)
    (curve_comp_structure S m c π hc) (CurveChain.rationalTreePicard S m c π hd htrans) M h

end KltDP.Geometry.CurveChain
