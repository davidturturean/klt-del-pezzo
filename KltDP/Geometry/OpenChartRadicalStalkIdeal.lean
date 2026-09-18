import KltDP.Geometry.StrictNormalCrossingsCartierAffineIdeal
import Mathlib.RingTheory.Localization.Ideal

/-!
# The original chart-stalk map preserves radical ideals

The actual germ map in native coordinates is the original affine chart
ring isomorphism followed by localization. Both original maps preserve
radicals, by the pinned ideal-map and localization theorems.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem radical_map_equiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (J : Ideal A) :
    Ideal.map e.toRingHom J.radical = (Ideal.map e.toRingHom J).radical := by
  calc
    _ = J.radical.comap e.symm := Ideal.map_comap_of_equiv e
    _ = (J.comap e.symm).radical := Ideal.comap_radical e.symm J
    _ = _ := congrArg Ideal.radical (Ideal.map_comap_of_equiv e).symm

/-- The literal original chart-stalk ideal map commutes with reduction. -/
theorem openImmersionStalkLocalizationEquiv_germIdeal_radical
    {X : Scheme.{u}} {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (p : PrimeSpectrum R) (J : Ideal Γ(X, j ''ᵁ ⊤)) :
    Ideal.map (openImmersionStalkLocalizationEquiv j p).toRingHom
      (Ideal.map (X.presheaf.germ (j ''ᵁ ⊤) (j.base p) (mem_chart_image_top j p)).hom J.radical) =
      (Ideal.map (openImmersionStalkLocalizationEquiv j p).toRingHom
        (Ideal.map (X.presheaf.germ (j ''ᵁ ⊤) (j.base p) (mem_chart_image_top j p)).hom J)).radical := by
  rw [openImmersionStalkLocalizationEquiv_germIdeal j p J.radical,
    radical_map_equiv, IsLocalization.map_radical p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal), openImmersionStalkLocalizationEquiv_germIdeal j p J]

end KltDP.Geometry
