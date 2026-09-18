import KltDP.Geometry.AffineFiniteType
import KltDP.Geometry.ProjectiveCoordinateSectionRelations

/-!
# The original coordinate tuple on an affine projective subopen

On an affine open contained in the original chart `D_+(z_i)`, the tuple
of restricted sections `z_j/z_i` defines the original affine-open immersion
into projective space. Its constants are the original base-to-sections map.

The proof compares the actual map `Proj.awayToSection`, followed by the
original structure-sheaf restriction, with the tuple chart homomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveCoordinateTupleMorphism

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

open ProjectiveChart ProjectiveCoordinateSectionBasicOpen
  ProjectiveCoordinateSectionRelations TransitionUnitGluing

variable (k : Type u) [Field k] (n : ℕ)

/-- The selected original coordinate remains one after restriction. -/
theorem coordinateTuple_self {U : (projectiveSpace k n).Opens}
    (i : Fin (n + 1)) (hUi : U ≤ standardOpen k n i) :
    res (projectiveSpace k n) hUi (coordinateSection k n i i) = 1 := by
  rw [coordinateSection_self, map_one]

private theorem specMap_awayToSection_chart (i : Fin (n + 1))
    (hV : IsAffineOpen (standardOpen k n i)) :
    Spec.map (Proj.awayToSection (grading k n) (MvPolynomial.X i)) ≫
        coordinateChartMorphism k n i = hV.fromSpec := by
  apply (cancel_epi hV.isoSpec.hom).mp
  change (standardOpen k n i).toSpecΓ ≫
      (Spec.map (Proj.awayToSection (grading k n) (MvPolynomial.X i)) ≫
        coordinateChartMorphism k n i) =
    (standardOpen k n i).toSpecΓ ≫ hV.fromSpec
  calc
    (standardOpen k n i).toSpecΓ ≫
        (Spec.map (Proj.awayToSection (grading k n) (MvPolynomial.X i)) ≫
          coordinateChartMorphism k n i) =
        (Proj.basicOpenIsoSpec (grading k n) (MvPolynomial.X i)
          (coordinate_mem k n i) Nat.one_pos).hom ≫
          ((Proj.basicOpenIsoSpec (grading k n) (MvPolynomial.X i)
            (coordinate_mem k n i) Nat.one_pos).inv ≫ (standardOpen k n i).ι) := by
      rw [← Category.assoc]
      rfl
    _ = (standardOpen k n i).ι := by rw [Iso.hom_inv_id_assoc]
    _ = (standardOpen k n i).toSpecΓ ≫ hV.fromSpec := hV.toSpecΓ_fromSpec.symm

/-- The normalized original homogeneous coordinates on an affine subopen
give its original immersion into projective space, over the original field. -/
theorem tupleMorphism_eq_fromSpec {U : (projectiveSpace k n).Opens}
    (hU : IsAffineOpen U) (i : Fin (n + 1)) (hUi : U ≤ standardOpen k n i) :
    tupleMorphism n (baseToAffineSectionsMap (projectiveSpaceToSpec k n) hU).hom
        (fun j => res (projectiveSpace k n) hUi (coordinateSection k n i j)) i
        (coordinateTuple_self k n i hUi) = hU.fromSpec := by
  let hV : IsAffineOpen (standardOpen k n i) :=
    Proj.isAffineOpen_basicOpen (grading k n) (MvPolynomial.X i)
      (coordinate_mem k n i) Nat.one_pos
  let α : CommRingCat.of (coordinateChartRing k n i) ⟶ Γ(projectiveSpace k n, U) :=
    Proj.awayToSection (grading k n) (MvPolynomial.X i) ≫
      (projectiveSpace k n).presheaf.map (homOfLE hUi).op
  have hα : Spec.map α ≫ coordinateChartMorphism k n i = hU.fromSpec := by
    dsimp only [α]
    rw [Spec.map_comp, Category.assoc, specMap_awayToSection_chart k n i hV]
    exact hV.map_fromSpec hU (homOfLE hUi).op
  have hconst : α.hom.comp (coordinateChartConstants k n i) =
      (baseToAffineSectionsMap (projectiveSpaceToSpec k n) hU).hom := by
    have h : CommRingCat.ofHom (coordinateChartConstants k n i) ≫ α =
        baseToAffineSectionsMap (projectiveSpaceToSpec k n) hU := by
      apply Spec.map_injective
      rw [Spec.map_comp, ← coordinateChartMorphism_over_base, ← Category.assoc,
        hα, Spec_map_baseToAffineSectionsMap]
    exact congrArg CommRingCat.Hom.hom h
  have htuple :
      tupleChartHom n (baseToAffineSectionsMap (projectiveSpaceToSpec k n) hU).hom
          (fun j => res (projectiveSpace k n) hUi (coordinateSection k n i j)) i
          (coordinateTuple_self k n i hUi) = α.hom := by
    apply HomogeneousAway.ringHom_ext (grading k n) (coordinate_mem k n i)
    intro d a ha
    rw [tupleChartHom_mk, mk_eq_eval_chartFraction, MvPolynomial.eval₂_comp_left, hconst]
    rfl
  rw [tupleMorphism, tupleSpec, htuple, CommRingCat.ofHom_hom]
  exact hα

end KltDP.Geometry.ProjectiveCoordinateTupleMorphism
