import KltDP.Geometry.ProjectiveImageChartFieldGeneration
import KltDP.Geometry.ProperGlobalSectionsFinite

/-!
# Original base scalars in projective image-chart field generation

The chart coefficient homomorphism is the original structure morphism's
global-section scalar map followed by its original generic-point germ.
Thus the polynomial-quotient conclusion uses precisely the original field
action. All comparison maps are the canonical maps already used to define
the projective space, its homogeneous charts, and scheme sections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProjectiveImageChartFieldGeneration

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

open ProjectiveChart ProjectiveCoordinateSectionBasicOpen

variable {k : Type u} [Field k] {n : ℕ}

private theorem specMap_awayToSection_chart (j : Fin (n + 1))
    (hV : IsAffineOpen (standardOpen k n j)) :
    Spec.map (Proj.awayToSection (grading k n) (MvPolynomial.X j)) ≫
        coordinateChartMorphism k n j = hV.fromSpec := by
  apply (cancel_epi hV.isoSpec.hom).mp
  change (standardOpen k n j).toSpecΓ ≫
      (Spec.map (Proj.awayToSection (grading k n) (MvPolynomial.X j)) ≫
        coordinateChartMorphism k n j) =
    (standardOpen k n j).toSpecΓ ≫ hV.fromSpec
  calc
    (standardOpen k n j).toSpecΓ ≫
        (Spec.map (Proj.awayToSection (grading k n) (MvPolynomial.X j)) ≫
          coordinateChartMorphism k n j) =
        (Proj.basicOpenIsoSpec (grading k n) (MvPolynomial.X j)
          (coordinate_mem k n j) Nat.one_pos).hom ≫
          ((Proj.basicOpenIsoSpec (grading k n) (MvPolynomial.X j)
            (coordinate_mem k n j) Nat.one_pos).inv ≫ (standardOpen k n j).ι) := by
      rw [← Category.assoc]
      rfl
    _ = (standardOpen k n j).ι := by rw [Iso.hom_inv_id_assoc]
    _ = (standardOpen k n j).toSpecΓ ≫ hV.fromSpec := hV.toSpecΓ_fromSpec.symm

private theorem chartConstants_cat (j : Fin (n + 1)) :
    CommRingCat.ofHom (coordinateChartConstants k n j) ≫
        Proj.awayToSection (grading k n) (MvPolynomial.X j) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (projectiveSpaceToSpec k n).appLE ⊤ (standardOpen k n j) (by simp) := by
  let hV := Proj.isAffineOpen_basicOpen (grading k n) (MvPolynomial.X j)
    (coordinate_mem k n j) Nat.one_pos
  apply Spec.map_injective
  calc
    _ = hV.fromSpec ≫ projectiveSpaceToSpec k n := by
      rw [Spec.map_comp, ← coordinateChartMorphism_over_base,
        ← Category.assoc, specMap_awayToSection_chart j hV]
    _ = _ := by
      rw [Spec.map_comp]
      have hbase : (isAffineOpen_top (Spec (CommRingCat.of k))).fromSpec =
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
        rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
      rw [← hbase]
      exact (IsAffineOpen.Spec_map_appLE_fromSpec (projectiveSpaceToSpec k n)
        (isAffineOpen_top (Spec (CommRingCat.of k))) hV (by simp)).symm

variable {Y : Scheme.{u}} (e : Y ⟶ projectiveSpace k n) (j : Fin (n + 1))

/-- The chart coefficients are the actual original structure-map
coefficients on the inverse-image open. -/
theorem sectionConstants_eq_structureMap :
    sectionConstants e j =
      ((e ≫ projectiveSpaceToSpec k n).appLE ⊤
        (e ⁻¹ᵁ standardOpen k n j) (by simp)).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom := by
  have hcat : CommRingCat.ofHom (coordinateChartConstants k n j) ≫
        Proj.awayToSection (grading k n) (MvPolynomial.X j) ≫
          e.app (standardOpen k n j) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (e ≫ projectiveSpaceToSpec k n).appLE ⊤
          (e ⁻¹ᵁ standardOpen k n j) (by simp) := by
    rw [← Category.assoc, chartConstants_cat, Category.assoc,
      e.app_eq_appLE, Scheme.appLE_comp_appLE]
  exact congrArg (fun φ => φ.hom) hcat

variable [IsIntegral Y] [Nonempty (e ⁻¹ᵁ standardOpen k n j)]

/-- The function-field coefficient map equals the original global
structure-map scalar homomorphism followed by the original generic germ. -/
theorem fieldConstants_eq_originalScalar :
    fieldConstants e j =
      (algebraMap Γ(Y, ⊤) Y.functionField).comp
        (baseFieldToGlobalSections (e ≫ projectiveSpaceToSpec k n)) := by
  unfold fieldConstants
  rw [sectionConstants_eq_structureMap]
  ext a
  change Y.germToFunctionField (e ⁻¹ᵁ standardOpen k n j)
      (Y.presheaf.map (homOfLE (le_top : e ⁻¹ᵁ standardOpen k n j ≤ ⊤)).op
        (baseFieldToGlobalSections (e ≫ projectiveSpaceToSpec k n) a)) =
    Y.germToFunctionField ⊤
      (baseFieldToGlobalSections (e ≫ projectiveSpaceToSpec k n) a)
  exact TopCat.Presheaf.germ_res_apply Y.presheaf
    (homOfLE le_top) (genericPoint Y) _ _

/-- Polynomial fractions with the original base-field scalar map,
without a field-extension or coefficient-compatibility hypothesis. -/
theorem exists_polynomial_quotient_originalScalar [IsClosedImmersion e]
    (z : Y.functionField) :
    ∃ p q : homogeneousRing k n,
      MvPolynomial.eval₂
        ((algebraMap Γ(Y, ⊤) Y.functionField).comp
          (baseFieldToGlobalSections (e ≫ projectiveSpaceToSpec k n)))
        (fieldCoordinate e j) q ≠ 0 ∧
      MvPolynomial.eval₂
        ((algebraMap Γ(Y, ⊤) Y.functionField).comp
          (baseFieldToGlobalSections (e ≫ projectiveSpaceToSpec k n)))
        (fieldCoordinate e j) p /
      MvPolynomial.eval₂
        ((algebraMap Γ(Y, ⊤) Y.functionField).comp
          (baseFieldToGlobalSections (e ≫ projectiveSpaceToSpec k n)))
        (fieldCoordinate e j) q = z := by
  simpa only [fieldConstants_eq_originalScalar] using
    exists_polynomial_quotient e j z

end KltDP.Geometry.ProjectiveImageChartFieldGeneration
