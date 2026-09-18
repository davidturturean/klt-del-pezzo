import KltDP.Geometry.GluedSubschemeStalkKernel

/-!
# The original ideal on an actual quotient chart

A cartesian quotient chart identifies the original closed-subscheme
kernel on the ambient chart with the literal quotient ideal. The
coordinates are the original open immersion's appIso and Gamma-Spec
isomorphism, so the associated section germs retain their native maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- An actual quotient chart computes the original kernel ideal in the
original chart ring. -/
theorem ker_ideal_chartSectionsEquiv_of_quotient_pullback
    {A : Type u} [CommRing A] {Y Z : Scheme.{u}}
    (g : Z ⟶ Y) [QuasiCompact g]
    (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (I : Ideal A) (e : Spec (CommRingCat.of (A ⧸ I)) ⟶ Z)
    (H : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) e j g) :
    (g.ker.ideal ⟨j ''ᵁ ⊤, chart_image_top_isAffineOpen j⟩).map
      (chartSectionsEquiv j) = I := by
  have h := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion g
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) e j H
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩
  rw [← comap_inv_comap_inv_eq_map, ← h, Scheme.Hom.ker_apply,
    RingHom.comap_ker, ← CommRingCat.hom_comp]
  change RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop).hom) = I
  rw [← Scheme.ΓSpecIso_inv_naturality, CommRingCat.hom_comp]
  change RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).inv.hom).comp
    (Ideal.Quotient.mk I)) = I
  exact (RingHom.ker_comp_of_injective (f := (Scheme.ΓSpecIso
    (CommRingCat.of (A ⧸ I))).inv.hom) (Ideal.Quotient.mk I)
    (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).symm.commRingCatIsoToRingEquiv.injective).trans
      Ideal.mk_ker

end KltDP.Geometry

#check @KltDP.Geometry.ker_ideal_chartSectionsEquiv_of_quotient_pullback
#print axioms KltDP.Geometry.ker_ideal_chartSectionsEquiv_of_quotient_pullback
