import KltDP.Geometry.ProjectiveLineDegreeExponent
import KltDP.Geometry.SchemeIsoEulerTransport
import KltDP.Geometry.PicardEulerValue
import KltDP.Manuscript.S02.RationalTreePicard

/-!
# Lemma 2.2 with Euler-characteristic degrees (gap item 6, the degree convention)

BRIEF24, task 1. The multidegree of the accepted Lemma 2.2 (`KltDP.Manuscript.S02.rationalTreePicard`)
is built from the transition exponent `componentExponent k X {C} (e C) L`: the exponent, on the
accepted `P¹`, of `L` restricted to the component `Z_C = componentUnionScheme X {C}` and transported
along the identification `e C : Z_C ≅ P¹`. This module identifies it with the Euler-characteristic
degree `deg L := χ(L) − χ(O)` (Stacks 0AYR):

* on `P¹`, lane D's `ProjectiveLineDegree.degree_eq_exponent` gives
  `componentExponent k X S e L = degree k (e.inv^* (L|_{Z_S}))` (`componentExponent_eq_degree_transport`,
  no hypothesis on `e`);
* if the identification is over `k` (`e.hom ≫ projectiveSpaceToSpec k 1 = ι_S ≫ f`), lane A2's Euler
  transport along scheme isomorphisms (`SchemeIsoEulerTransport`) gives
  **`componentExponent k X S e L = eulerDegree (ι_S ≫ f) (L|_{Z_S})`**, the Euler degree of `L|_{Z_S}`
  computed on the component itself with its structure map (`componentExponent_eq_eulerDegree`);
* descending to Picard classes (`picardEulerDegree`, through the accepted `picardEulerValue`), the
  **Euler multidegree** `eulerMultidegree X f : X.Pic → (components → ℤ)`,
  `p ↦ (χ(p|_{Z_C}) − χ(O_{Z_C}))_C`, coincides with `toAdd ∘ multidegreeHom k X e`
  (`eulerMultidegree_eq`) whenever every `e C` is over `k`, and therefore
  **`rationalTreePicard_degrees`: `eulerMultidegree X f` is bijective** under the hypotheses of the
  accepted Lemma 2.2 — the convention-free form of `lem:tree-picard`: `Pic(Z) ≅ ℤ^{components}` via the
  actual degrees of the restrictions to the components; with the degree-zero clause
  `rationalTreePicard_degrees_trivial`.

Hypotheses of `rationalTreePicard_degrees`: those of `KltDP.Manuscript.S02.rationalTreePicard`
(`k` algebraically closed; `X` reduced, Noetherian, locally Noetherian, `f : X ⟶ Spec k` locally of
finite type, `dim X ≤ 1`, tree incidence graph, transverse component branches, identifications
`e C : Z_C ≅ P¹`) plus `hfe : ∀ C, (e C).hom ≫ projectiveSpaceToSpec k 1 = componentUnionInclusion X {C} ≫ f`
(the identifications are `k`-isomorphisms; without it the Euler characteristics over `k` on `Z_C` and
on `P¹` need not agree). Lane D's `ProjectiveLineDegreeExponent` and its closure, and lane A2's
accepted `SchemeIsoEulerTransport` with its closure, are copied byte-identically into this lane.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

open KltDP.Geometry KltDP.Geometry.ModuleCohomology KltDP.Geometry.ProjectiveLineDegree

variable {k : Type u} [Field k]

/-! ## Euler degrees -/

/-- The Euler degree `χ(M) − χ(O)` of an invertible sheaf on a scheme `Y` over `k` with structure
map `g`. -/
def eulerDegree {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k)) (M : InvertibleSheaf Y) : ℤ :=
  eulerCharacteristic g M.obj -
    eulerCharacteristic g (_root_.SheafOfModules.unit Y.ringCatSheaf)

/-- The Euler degree of a Picard class (through the accepted `picardEulerValue`). -/
def picardEulerDegree {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k)) (p : Y.Pic) : ℤ :=
  picardEulerValue g p - picardEulerValue g 1

theorem picardEulerDegree_toPic {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k))
    (M : InvertibleSheaf Y) : picardEulerDegree g M.toPic = eulerDegree g M := by
  unfold picardEulerDegree eulerDegree
  rw [picardEulerValue_toPic, picardEulerValue_one]

/-! ## The component exponent is an Euler degree -/

section ComponentExponent

variable (X : Scheme.{u}) [NoetherianSpace X] (S : Set ↥(irreducibleComponents X))
  (e : componentUnionScheme X S ≅ projectiveSpace k 1) (L : InvertibleSheaf X)

/-- On `P¹`: the component exponent is the Euler degree of the transported restriction
(lane D's `degree_eq_exponent`). -/
theorem componentExponent_eq_degree_transport :
    componentExponent k X S e L =
      ProjectiveLineDegree.degree k (pullbackInvertibleSheaf e.inv (componentUnionRestriction X S L)) :=
  (ProjectiveLineDegree.degree_eq_exponent k _).symm

/-- **The component exponent is the Euler degree of the restriction to the component**, computed
on the component with its structure map, when the identification `e` is over `k`. -/
theorem componentExponent_eq_eulerDegree (f : X ⟶ Spec (CommRingCat.of k))
    (hfe : e.hom ≫ projectiveSpaceToSpec k 1 = componentUnionInclusion X S ≫ f) :
    componentExponent k X S e L =
      eulerDegree (componentUnionInclusion X S ≫ f) (componentUnionRestriction X S L) := by
  rw [componentExponent_eq_degree_transport]
  unfold ProjectiveLineDegree.degree eulerDegree
  rw [eulerCharacteristic_eq_pullback_inv e (componentUnionInclusion X S ≫ f)
      (projectiveSpaceToSpec k 1) hfe (componentUnionRestriction X S L).obj,
    eulerCharacteristic_unit_eq e (componentUnionInclusion X S ≫ f)
      (projectiveSpaceToSpec k 1) hfe]
  rfl

end ComponentExponent

/-! ## The Euler multidegree and Lemma 2.2 -/

section Multidegree

variable (X : Scheme.{u}) [NoetherianSpace X]

/-- The Euler multidegree of a Picard class: restrict to each component `Z_C` and take the Euler
degree over `k` (structure map `ι_C ≫ f`). No identification with `P¹` enters the definition. -/
def eulerMultidegree (f : X ⟶ Spec (CommRingCat.of k)) (p : X.Pic) :
    ↥(irreducibleComponents X) → ℤ :=
  fun C => picardEulerDegree (componentUnionInclusion X {C} ≫ f)
    (schemePicardPullbackHom (componentUnionInclusion X {C}) p)

theorem eulerMultidegree_toPic (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
    (C : ↥(irreducibleComponents X)) :
    eulerMultidegree X f L.toPic C =
      eulerDegree (componentUnionInclusion X {C} ≫ f) (componentUnionRestriction X {C} L) := by
  unfold eulerMultidegree
  rw [schemePicardPullbackHom_toPic, picardEulerDegree_toPic]

variable [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The Euler multidegree is the multidegree of the accepted Lemma 2.2 when the identifications are
over `k`. -/
theorem eulerMultidegree_eq (f : X ⟶ Spec (CommRingCat.of k))
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (hfe : ∀ C, (e C).hom ≫ projectiveSpaceToSpec k 1 = componentUnionInclusion X {C} ≫ f)
    (p : X.Pic) :
    eulerMultidegree X f p = fun C => Multiplicative.toAdd (multidegreeHom k X e p C) := by
  obtain ⟨L, rfl⟩ := toPic_surjective p
  funext C
  rw [eulerMultidegree_toPic X f L C, multidegreeHom_toPic, toAdd_ofAdd,
    componentExponent_eq_eulerDegree X {C} (e C) L f (hfe C)]

/-- **Lemma 2.2, convention-free form.** Under the hypotheses of the accepted
`KltDP.Manuscript.S02.rationalTreePicard`, with identifications `e C : Z_C ≅ P¹` over `k`, the Euler
multidegree `Pic X → ℤ^{components}`, `p ↦ (χ(p|_{Z_C}) − χ(O_{Z_C}))_C`, is bijective. -/
theorem rationalTreePicard_degrees [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (htrans : HasTransverseComponentBranches X)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (hfe : ∀ C, (e C).hom ≫ projectiveSpaceToSpec k 1 = componentUnionInclusion X {C} ≫ f) :
    Function.Bijective (eulerMultidegree X f) := by
  have h : eulerMultidegree X f = fun p C => Multiplicative.toAdd (multidegreeHom k X e p C) := by
    funext p
    exact eulerMultidegree_eq X f e hfe p
  rw [h]
  exact (Equiv.piCongrRight fun _ : ↥(irreducibleComponents X) =>
    (Multiplicative.toAdd : Multiplicative ℤ ≃ ℤ)).bijective.comp
    (KltDP.Manuscript.S02.rationalTreePicard X f hdim hTree htrans e)

/-- The degree-zero clause in Euler form: a line bundle whose restriction to every component has
Euler degree zero is trivial. -/
theorem rationalTreePicard_degrees_trivial [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (htrans : HasTransverseComponentBranches X)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (hfe : ∀ C, (e C).hom ≫ projectiveSpaceToSpec k 1 = componentUnionInclusion X {C} ≫ f)
    (L : InvertibleSheaf X) (hL : ∀ C : ↥(irreducibleComponents X),
      eulerDegree (componentUnionInclusion X {C} ≫ f) (componentUnionRestriction X {C} L) = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) :=
  KltDP.Manuscript.S02.rationalTreePicard_trivial_of_degree_zero X f hdim hTree htrans e L
    (fun C => by rw [componentExponent_eq_eulerDegree X {C} (e C) L f (hfe C)]; exact hL C)

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (X₀ : Scheme.{0}) [NoetherianSpace X₀]
    [IsLocallyNoetherian X₀] [AlgebraicGeometry.IsReduced X₀]
    (f₀ : X₀ ⟶ Spec (CommRingCat.of k₀)) [LocallyOfFiniteType f₀]
    (hdim : topologicalKrullDim X₀ ≤ 1) (hTree : (componentPointIncidenceGraph X₀).IsTree)
    (htrans : HasTransverseComponentBranches X₀)
    (e : ∀ C : ↥(irreducibleComponents X₀), componentUnionScheme X₀ {C} ≅ projectiveSpace k₀ 1)
    (hfe : ∀ C, (e C).hom ≫ projectiveSpaceToSpec k₀ 1 = componentUnionInclusion X₀ {C} ≫ f₀) :
    Function.Bijective (eulerMultidegree X₀ f₀) :=
  rationalTreePicard_degrees X₀ f₀ hdim hTree htrans e hfe

end Multidegree

end KltDP.Geometry.RationalTreePicard
