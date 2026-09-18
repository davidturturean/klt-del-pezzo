import KltDP.Geometry.LinearSystemSectionRatio

/-!
# Original generator equations give surjective coordinate-chart maps

The original field scalar map commutes with appLE by the actual affine
chart square and the original structure identity. Polynomial expressions
in the original section ratios therefore lift to actual projective chart
sections. No synthetic chart homomorphism replaces the original appLE.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemMorphism

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

local instance chartSurjectivitySectionModule {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (op U)) := (M.val.obj (op U)).isModule

open InvertibleSectionNonvanishingOpen ProjectiveCoordinateSectionBasicOpen
  PowerSectionFunctionExtension

private theorem baseScalars_appLE {R : Type u} [CommRing R]
    {X Y : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Spec (CommRingCat.of R))
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ g ⁻¹ᵁ V) :
    baseToAffineSectionsMap f hV ≫ g.appLE V U hUV =
      baseToAffineSectionsMap (g ≫ f) hU := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec_map_baseToAffineSectionsMap,
    Spec_map_baseToAffineSectionsMap, ← Category.assoc,
    IsAffineOpen.Spec_map_appLE_fromSpec, Category.assoc]

variable {k : Type u} [Field k] {X : Scheme.{u}} (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections) (f : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)

/-- Original polynomial generators represented by original section ratios
make the actual coordinate-chart restriction surjective. -/
theorem appOnNonvanishing_surjective_of_generators
    (m : Fin (n + 1)) {U : X.Opens} (hU : IsAffineOpen U)
    (hUm : U ≤ nonvanishingOpen X L (s m))
    {d : ℕ} (index : Fin d → Fin (n + 1)) (b : Fin d → Γ(X, U))
    (hb : Function.Surjective (MvPolynomial.eval₂Hom (baseToAffineSectionsMap f hU).hom b))
    (ht : ∀ a, sectionValue L.obj (s (index a)) U =
      b a • sectionValue L.obj (s m) U) :
    Function.Surjective (appOnNonvanishing L s f hcover m hUm).hom := by
  let hstd : IsAffineOpen (standardOpen k n m) :=
    Proj.isAffineOpen_basicOpen (ProjectiveChart.grading k n) (MvPolynomial.X m)
      (ProjectiveChart.coordinate_mem k n m) Nat.one_pos
  let α : k →+* Γ(projectiveSpace k n, standardOpen k n m) :=
    (baseToAffineSectionsMap (projectiveSpaceToSpec k n) hstd).hom
  let φ := (appOnNonvanishing L s f hcover m hUm).hom
  have hscalar : φ.comp α = (baseToAffineSectionsMap f hU).hom := by
    have h := baseScalars_appLE (morphism L s f hcover) (projectiveSpaceToSpec k n)
      hU hstd (show U ≤ morphism L s f hcover ⁻¹ᵁ standardOpen k n m from
        by rw [morphism_preimage_standardOpen]; exact hUm)
    rw [morphism_structure] at h
    exact congrArg (fun a : CommRingCat.of k ⟶ Γ(X, U) => a.hom) h
  have hcoord : (fun a => φ (coordinateSection k n m (index a))) = b := by
    funext a
    exact appOnNonvanishing_coordinateSection_of_eq L s f hcover m (index a) hUm (b a) (ht a)
  intro z
  obtain ⟨p, hp⟩ := hb z
  refine ⟨MvPolynomial.eval₂Hom α (fun a => coordinateSection k n m (index a)) p, ?_⟩
  change φ (MvPolynomial.eval₂Hom α (fun a => coordinateSection k n m (index a)) p) = z
  rw [MvPolynomial.map_eval₂Hom, hscalar]
  change MvPolynomial.eval₂Hom (baseToAffineSectionsMap f hU).hom
    (fun a => φ (coordinateSection k n m (index a))) p = z
  rw [hcoord]
  exact hp

end KltDP.Geometry.LinearSystemMorphism
