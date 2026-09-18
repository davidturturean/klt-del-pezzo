import KltDP.Geometry.OpenPullbackLinearSystemCartierRatios
import KltDP.Geometry.ProjectiveImageCoordinateGerms
import KltDP.Geometry.ProjectiveImageChartScalars

/-!
# Original ambient scalar and polynomial values of open linear-system coordinates

The inverse original open function-field isomorphism carries the exact
field coordinates used in projective-image generation to original Cartier
section ratios. It carries the coefficient map to the original ambient
base-field map. Consequently it preserves actual polynomial evaluations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.OpenPullbackLinearSystemCartierRatios

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open LinearSystemMorphism InvertibleSectionNonvanishingOpen
  ProjectiveCoordinateSectionBasicOpen OpenImmersionRational
  ProjectiveImageChartFieldGeneration

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : Y ⟶ X) [IsOpenImmersion f]
  {k : Type u} [Field k] (b : X ⟶ Spec (CommRingCat.of k))

/-- The exact original ambient scalar is recovered by the inverse
original open function-field isomorphism. -/
theorem inverse_originalScalar (a : k) :
    (functionFieldIso f).inv
        (((algebraMap Γ(Y, ⊤) Y.functionField).comp
          (baseFieldToGlobalSections (f ≫ b))) a) =
      ((algebraMap Γ(X, ⊤) X.functionField).comp (baseFieldToGlobalSections b)) a := by
  letI : Nonempty (f ⁻¹ᵁ (⊤ : X.Opens)).toScheme := by
    change Nonempty (⊤ : Y.Opens).toScheme
    exact ⟨⟨genericPoint Y, trivial⟩⟩
  apply (ConcreteCategory.bijective_of_isIso (functionFieldIso f).hom).1
  rw [Iso.inv_hom_id_apply]
  exact (functionFieldIso_germ f ⊤ (baseFieldToGlobalSections b a)).symm

variable (D : CartierDivisor X) {n : ℕ}
  (s : Fin (n + 1) → (cartierDivisorInvertibleSheaf X D).obj.sections)
  (c : Chart (pulledLine f D) (pulledTuple f D s)) [Nonempty c.affineOpen.1]
  (hcover : (⨆ j, nonvanishingOpen Y (pulledLine f D) (pulledTuple f D s j)) = ⊤)

/-- The generator used by the actual field-generation theorem becomes
the ratio of the actual original global Cartier section values. -/
theorem inverse_fieldCoordinate (j : Fin (n + 1)) :
    letI := chart_preimage_nonempty (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover c
    (functionFieldIso f).inv
        (fieldCoordinate (morphism (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover)
          c.index j) =
      cartierGlobalSectionRationalValue X D ((s j).val (op ⊤)) /
        cartierGlobalSectionRationalValue X D ((s c.index).val (op ⊤)) := by
  letI := chart_preimage_nonempty (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover c
  rw [fieldCoordinate_eq_coordinate_germ]
  exact inverse_germ_coordinates f D s c j

/-- The coefficient homomorphism is the original ambient field map,
without replacing the base field or supplying compatibility data. -/
theorem inverse_fieldConstants :
    letI := chart_preimage_nonempty (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover c
    (functionFieldIso f).inv.hom.comp
        (fieldConstants (morphism (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover)
          c.index) =
      (algebraMap Γ(X, ⊤) X.functionField).comp (baseFieldToGlobalSections b) := by
  letI := chart_preimage_nonempty (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover c
  ext a
  rw [RingHom.comp_apply, fieldConstants_eq_originalScalar, morphism_structure]
  exact inverse_originalScalar f b a

/-- Polynomial evaluation is retained in the actual original function
field, at the actual global section ratios and original base scalars. -/
theorem inverse_polynomial_value (p : ProjectiveChart.homogeneousRing k n) :
    letI := chart_preimage_nonempty (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover c
    (functionFieldIso f).inv.hom
        (MvPolynomial.eval₂
          (fieldConstants (morphism (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover) c.index)
          (fieldCoordinate (morphism (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover) c.index) p) =
      MvPolynomial.eval₂
        ((algebraMap Γ(X, ⊤) X.functionField).comp (baseFieldToGlobalSections b))
        (fun j => cartierGlobalSectionRationalValue X D ((s j).val (op ⊤)) /
          cartierGlobalSectionRationalValue X D ((s c.index).val (op ⊤))) p := by
  letI := chart_preimage_nonempty (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover c
  rw [MvPolynomial.eval₂_comp_left, inverse_fieldConstants]
  congr 1
  funext j
  exact inverse_fieldCoordinate f b D s c hcover j

end KltDP.Geometry.OpenPullbackLinearSystemCartierRatios
