import KltDP.Geometry.OpenPullbackLinearSystemFieldCoordinates
import KltDP.Geometry.BirationalCommonHomogeneousFractions

/-!
# Common homogeneous fractions in original global Cartier section ratios

For the original linear system of original Cartier sections on an actual
open where they generate, a birational factorization through an actual
closed projective image gives every finite family of original ambient
rational functions as homogeneous fractions of one positive degree.
The selected original global section and the common polynomial denominator
are both proved nonzero. This statement allows a base locus on the ambient
scheme; the complete system's original non-base open is sufficient.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u v

namespace KltDP.Geometry.OpenPullbackLinearSystemCartierRatios

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open LinearSystemMorphism InvertibleSectionNonvanishingOpen
  ProjectiveCoordinateSectionBasicOpen OpenImmersionRational
  ProjectiveImageChartFieldGeneration ProjectiveChart

private theorem polynomialValue_congr {k : Type u} [Field k]
    {T : Scheme.{u}} [IsIntegral T] {n : ℕ}
    (a b : T ⟶ projectiveSpace k n) (hab : a = b) (j : Fin (n + 1))
    [Nonempty (a ⁻¹ᵁ standardOpen k n j)] [Nonempty (b ⁻¹ᵁ standardOpen k n j)]
    (p : homogeneousRing k n) :
    MvPolynomial.eval₂ (fieldConstants a j) (fieldCoordinate a j) p =
      MvPolynomial.eval₂ (fieldConstants b j) (fieldCoordinate b j) p := by
  subst b
  rfl

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
  (f : Y ⟶ X) [IsOpenImmersion f]
  {k : Type u} [Field k] (b : X ⟶ Spec (CommRingCat.of k))
  (D : CartierDivisor X) {n : ℕ}
  (s : Fin (n + 1) → (cartierDivisorInvertibleSheaf X D).obj.sections)

/-- Actual birational projective coordinates yield common positive-degree
homogeneous fractions in the original ambient Cartier-section ratios. -/
theorem exists_common_fractions
    (hcover : (⨆ j, nonvanishingOpen Y (pulledLine f D) (pulledTuple f D s j)) = ⊤)
    (e : Z ⟶ projectiveSpace k n) [IsClosedImmersion e] (g : Y ⟶ Z)
    (hg : IsBirationalScheme g)
    (hcomp : g ≫ e = morphism (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover)
    {ι : Type v} [Fintype ι] (z : ι → X.functionField) :
    ∃ (j : Fin (n + 1)) (d : ℕ) (p : ι → homogeneousRing k n) (q : homogeneousRing k n),
      0 < d ∧ cartierGlobalSectionRationalValue X D ((s j).val (op ⊤)) ≠ 0 ∧
      (∀ i, (p i).IsHomogeneous d) ∧ q.IsHomogeneous d ∧
      MvPolynomial.eval₂
        ((algebraMap Γ(X, ⊤) X.functionField).comp (baseFieldToGlobalSections b))
        (fun a => cartierGlobalSectionRationalValue X D ((s a).val (op ⊤)) /
          cartierGlobalSectionRationalValue X D ((s j).val (op ⊤))) q ≠ 0 ∧
      ∀ i, MvPolynomial.eval₂
        ((algebraMap Γ(X, ⊤) X.functionField).comp (baseFieldToGlobalSections b))
        (fun a => cartierGlobalSectionRationalValue X D ((s a).val (op ⊤)) /
          cartierGlobalSectionRationalValue X D ((s j).val (op ⊤))) (p i) /
        MvPolynomial.eval₂
          ((algebraMap Γ(X, ⊤) X.functionField).comp (baseFieldToGlobalSections b))
          (fun a => cartierGlobalSectionRationalValue X D ((s a).val (op ⊤)) /
            cartierGlobalSectionRationalValue X D ((s j).val (op ⊤))) q = z i := by
  have hη : genericPoint Y ∈
      ⨆ c : Chart (pulledLine f D) (pulledTuple f D s), c.affineOpen.1 := by
    rw [chartOpens_cover (pulledLine f D) (pulledTuple f D s) hcover]
    trivial
  obtain ⟨c, hc⟩ := Opens.mem_iSup.mp hη
  letI : Nonempty c.affineOpen.1 := ⟨⟨genericPoint Y, hc⟩⟩
  letI := chart_preimage_nonempty (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover c
  letI : Nonempty (e ⁻¹ᵁ standardOpen k n c.index) := by
    refine ⟨⟨g.base (genericPoint Y), ?_⟩⟩
    change (g ≫ e).base (genericPoint Y) ∈ standardOpen k n c.index
    rw [hcomp]
    exact chart_le_preimage_standardOpen (pulledLine f D) (pulledTuple f D s)
      (f ≫ b) hcover c hc
  letI : GenericPointPreserving g := ⟨hg.map_genericPoint⟩
  obtain ⟨d, p, q, hd, hp, hq, hq0, hpq⟩ :=
    exists_common_homogeneous_fractions e c.index g hg
      (fun i => (functionFieldIso f).hom (z i))
  simp only [polynomialValue_congr (g ≫ e)
    (morphism (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover)
    hcomp c.index] at hq0 hpq
  refine ⟨c.index, d, p, q, hd, denominator_value_ne_zero f D s c, hp, hq, ?_, ?_⟩
  · intro hzero
    apply hq0
    apply (functionFieldIso f).inv.hom.injective
    calc
      _ = _ := inverse_polynomial_value f b D s c hcover q
      _ = 0 := hzero
      _ = _ := (map_zero (functionFieldIso f).inv.hom).symm
  · intro i
    have h := congrArg (functionFieldIso f).inv.hom (hpq i)
    rw [map_div₀, inverse_polynomial_value, inverse_polynomial_value,
      Iso.hom_inv_id_apply] at h
    exact h

end KltDP.Geometry.OpenPullbackLinearSystemCartierRatios
