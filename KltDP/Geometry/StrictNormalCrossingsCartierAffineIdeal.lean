import KltDP.Geometry.StrictNormalCrossingsCartierIdealData
import KltDP.Geometry.StrictNormalCrossingsEquiv
import KltDP.Geometry.GluedSubschemeStalkKernel

/-!
# The actual Cartier affine ideal at an SNC point

The original affine-chart section and stalk isomorphisms transport the
actual regular Cartier ideal to its native chart ring. An SNC Cartier
equation through the point then supplies an SNC generator of precisely
the localization of that original affine ideal.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The original chart-stalk isomorphism carries the original germ ideal
to the localization of the actual ideal in the native chart ring. -/
theorem openImmersionStalkLocalizationEquiv_germIdeal
    {X : Scheme.{u}} {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (p : PrimeSpectrum R) (J : Ideal Γ(X, j ''ᵁ ⊤)) :
    Ideal.map (openImmersionStalkLocalizationEquiv j p).toRingHom
      (Ideal.map (X.presheaf.germ (j ''ᵁ ⊤) (j.base p) (mem_chart_image_top j p)).hom J) =
      Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal))
        (Ideal.map (chartSectionsEquiv j).toRingHom J) := by
  have hmap : (openImmersionStalkLocalizationEquiv j p).toRingHom.comp
      (X.presheaf.germ (j ''ᵁ ⊤) (j.base p) (mem_chart_image_top j p)).hom =
      (algebraMap R (Localization.AtPrime p.asIdeal)).comp
        (chartSectionsEquiv j).toRingHom := by
    apply RingHom.ext
    intro s
    exact openImmersionStalkLocalizationEquiv_germ j p s
  simpa only [Ideal.map_map] using congrArg (fun f => Ideal.map f J) hmap

/-- SNC of the original Cartier divisor supplies an SNC generator of
the actual original affine ideal in the actual native local ring. -/
theorem strictNormalCrossingsCartier_affine_ideal
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (D : CartierDivisor X) (hD : IsStrictNormalCrossingsCartier X D)
    {R : Type u} [CommRing R] (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (p : PrimeSpectrum R) :
    ∃ c : Localization.AtPrime p.asIdeal,
      Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal))
        (Ideal.map (chartSectionsEquiv j).toRingHom
          ((effectiveCartierIdealDataOfRegularEquations X D hD.1).ideal
            ⟨j ''ᵁ ⊤, chart_image_top_isAffineOpen j⟩)) = Ideal.span {c} ∧
      IsStrictNormalCrossingsEquation (Localization.AtPrime p.asIdeal) c := by
  obtain ⟨d, hd⟩ := hD.1 (j.base p)
  let ε := openImmersionStalkLocalizationEquiv j p
  let c := X.presheaf.germ d.chart.openSet (j.base p) hd d.coefficient
  refine ⟨ε c, ?_, (hD.2 d (j.base p) hd).map_equiv ε⟩
  have hideal := regularCartierIdealData_map_germ_eq_span X D hD.1 d
    ⟨j ''ᵁ ⊤, chart_image_top_isAffineOpen j⟩ (j.base p) (mem_chart_image_top j p) hd
  have htransport := openImmersionStalkLocalizationEquiv_germIdeal j p
    ((effectiveCartierIdealDataOfRegularEquations X D hD.1).ideal
      ⟨j ''ᵁ ⊤, chart_image_top_isAffineOpen j⟩)
  rw [hideal, Ideal.map_span, Set.image_singleton] at htransport
  exact htransport.symm

end KltDP.Geometry
