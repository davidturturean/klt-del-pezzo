import KltDP.Geometry.BirationalLinearSystemCartierFractions
import KltDP.Geometry.CartierHomogeneousSectionRatios

/-!
# Actual global same-power section ratios from a birational linear system

The common homogeneous polynomials supplied by the original birational
linear system are evaluated in the original global Cartier sections.
This produces a common nonzero denominator and numerators in the actual
same positive Cartier power. All ratios live in the original ambient
function field. Generation is required only on the actual chosen open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u v

namespace KltDP.Geometry.OpenPullbackLinearSystemCartierRatios

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open LinearSystemMorphism InvertibleSectionNonvanishingOpen ModuleCohomology

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
  (f : Y ⟶ X) [IsOpenImmersion f]
  {k : Type u} [Field k] (b : X ⟶ Spec (CommRingCat.of k))
  (D : CartierDivisor X) {n : ℕ}
  (s : Fin (n + 1) → (cartierDivisorInvertibleSheaf X D).obj.sections)

/-- A birational factor of the original linear system supplies common
actual global section ratios in one positive original Cartier power. -/
theorem exists_common_section_ratios
    (hcover : (⨆ j, nonvanishingOpen Y (pulledLine f D) (pulledTuple f D s j)) = ⊤)
    (e : Z ⟶ projectiveSpace k n) [IsClosedImmersion e] (g : Y ⟶ Z)
    (hg : IsBirationalScheme g)
    (hcomp : g ≫ e = morphism (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover)
    {ι : Type v} [Fintype ι] (z : ι → X.functionField) :
    ∃ (d : ℕ) (t₀ : sections (cartierDivisorModule X (d • D)))
      (t : ι → sections (cartierDivisorModule X (d • D))),
      0 < d ∧ t₀ ≠ 0 ∧ ∀ i,
        cartierGlobalSectionRationalValue X (d • D) (t i) /
          cartierGlobalSectionRationalValue X (d • D) t₀ = z i := by
  obtain ⟨j, d, p, q, hd, hs, hp, hq, hq0, hpq⟩ :=
    exists_common_fractions f b D s hcover e g hg hcomp z
  have hs₀ : (s j).val (op ⊤) ≠ 0 := by
    intro hzero
    apply hs
    rw [hzero]
    exact map_zero (rationalFunctionModuleSectionsEquiv X ⊤)
  let st : Fin (n + 1) → sections (cartierDivisorModule X D) := fun i => (s i).val (op ⊤)
  refine ⟨d, SectionMonomialGrowth.homogeneousSection b D st q hq,
    (fun i => SectionMonomialGrowth.homogeneousSection b D st (p i) (hp i)), hd, ?_, ?_⟩
  · exact SectionMonomialGrowth.homogeneousSection_ne_zero_of_ratio_eval_ne_zero
      b D (st j) st q hq hq0
  · intro i
    exact (SectionMonomialGrowth.homogeneousSection_quotient
      b D (st j) hs₀ st (p i) q (hp i) hq).trans (hpq i)

end KltDP.Geometry.OpenPullbackLinearSystemCartierRatios
