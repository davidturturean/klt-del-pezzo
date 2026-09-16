import KltDP.Compatibility.StandardSmoothEtaleCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Actual affine étale coordinates for smooth scheme morphisms

The pinned definition of smoothness supplies standard-smooth affine
neighborhoods. The constructive polynomial factorization then gives an
actual étale map to affine space over the actual chosen affine base.
All maps in the final equation are existing scheme morphisms. There is
no assumption that a smooth neighborhood is an affine-plane open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry

universe u

/-- The pinned local ring-homomorphism characterization translates the
actual dimension-zero standard-smooth map into an actual étale Spec map. -/
theorem isEtale_spec_map_of_standardSmoothZero
    {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S)
    (hg : g.IsStandardSmoothOfRelativeDimension 0) :
    IsEtale (Spec.map (CommRingCat.ofHom g)) := by
  apply (HasRingHomProperty.Spec_iff (P := @IsSmoothOfRelativeDimension 0)).mpr
  exact RingHom.locally_of
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso g hg

/-- A standard-smooth map of actual affine sections produces a commuting
étale coordinate diagram over that same affine base. -/
theorem affine_standardSmooth_etale_coordinates
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1)
    (hf : (f.appLE U.1 V.1 e).hom.IsStandardSmoothOfRelativeDimension n) :
    ∃ g : MvPolynomial (Fin n) Γ(Y, U.1) →+* Γ(X, V.1),
      IsEtale (Spec.map (CommRingCat.ofHom g)) ∧
      Spec.map (CommRingCat.ofHom g) ≫
          Spec.map (CommRingCat.ofHom
            (MvPolynomial.C : Γ(Y, U.1) →+* MvPolynomial (Fin n) Γ(Y, U.1))) ≫
          U.2.fromSpec = V.2.fromSpec ≫ f := by
  obtain ⟨g, hg, he⟩ :=
    KltDP.StandardSmoothCoordinates.ringHom_exists_standardSmoothZero_mvPolynomial hf
  refine ⟨g, isEtale_spec_map_of_standardSmoothZero g he, ?_⟩
  calc
    _ = Spec.map (CommRingCat.ofHom (g.comp MvPolynomial.C)) ≫ U.2.fromSpec := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      simp only [Category.assoc]
    _ = Spec.map (f.appLE U.1 V.1 e) ≫ U.2.fromSpec := by
      simp only [hg, CommRingCat.ofHom_hom]
    _ = V.2.fromSpec ≫ f := IsAffineOpen.Spec_map_appLE_fromSpec f U.2 V.2 e

/-- Around every point of a morphism smooth of relative dimension `n`,
the actual source chart admits an actual étale map to `n`-dimensional
affine space over the actual target chart. -/
theorem smoothOfRelativeDimension_exists_etale_coordinates
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [IsSmoothOfRelativeDimension n f] (x : X) :
    ∃ (U : Y.affineOpens) (V : X.affineOpens), x ∈ V.1 ∧
      ∃ g : MvPolynomial (Fin n) Γ(Y, U.1) →+* Γ(X, V.1),
        IsEtale (Spec.map (CommRingCat.ofHom g)) ∧
        Spec.map (CommRingCat.ofHom g) ≫
            Spec.map (CommRingCat.ofHom
              (MvPolynomial.C : Γ(Y, U.1) →+* MvPolynomial (Fin n) Γ(Y, U.1))) ≫
            U.2.fromSpec = V.2.fromSpec ≫ f := by
  obtain ⟨U, V, hx, e, hf⟩ :=
    IsSmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (f := f) (n := n) x
  exact ⟨U, V, hx, affine_standardSmooth_etale_coordinates f n U V e hf⟩

/-- The ordinary pinned smoothness predicate supplies the corresponding
actual coordinate diagram with some finite relative dimension. -/
theorem smooth_exists_etale_coordinates
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSmooth f] (x : X) :
    ∃ (U : Y.affineOpens) (V : X.affineOpens), x ∈ V.1 ∧
      ∃ n, ∃ g : MvPolynomial (Fin n) Γ(Y, U.1) →+* Γ(X, V.1),
        IsEtale (Spec.map (CommRingCat.ofHom g)) ∧
        Spec.map (CommRingCat.ofHom g) ≫
            Spec.map (CommRingCat.ofHom
              (MvPolynomial.C : Γ(Y, U.1) →+* MvPolynomial (Fin n) Γ(Y, U.1))) ≫
            U.2.fromSpec = V.2.fromSpec ≫ f := by
  obtain ⟨U, V, hx, e, hf⟩ := IsSmooth.exists_isStandardSmooth (f := f) x
  obtain ⟨n, g, hg, he⟩ :=
    KltDP.StandardSmoothCoordinates.ringHom_isStandardSmooth_exists_mvPolynomial hf
  refine ⟨U, V, hx, n, g, isEtale_spec_map_of_standardSmoothZero g he, ?_⟩
  calc
    _ = Spec.map (CommRingCat.ofHom (g.comp MvPolynomial.C)) ≫ U.2.fromSpec := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      simp only [Category.assoc]
    _ = Spec.map (f.appLE U.1 V.1 e) ≫ U.2.fromSpec := by
      simp only [hg, CommRingCat.ofHom_hom]
    _ = V.2.fromSpec ≫ f := IsAffineOpen.Spec_map_appLE_fromSpec f U.2 V.2 e

end KltDP.Geometry
