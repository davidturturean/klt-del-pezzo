import KltDP.Geometry.QuadraticCoverAtlasGluing

/-!
# Original affine base intersections of the quadratic atlas

The spectrum maps of the actual structure-sheaf restrictions form the
actual pullback of the original affine base inclusions. The result is
derived from their original image ranges and does not assume a new
intersection presentation.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.QuadraticAtlasBaseIntersections

open TransitionUnitGluing QuadraticCoverOpen QuadraticCoverAtlas

variable {X : Scheme.{u}} {ι : Type u} (D : Data X ι)

def left (i j : ι) : Spec Γ(X, D.opens i ⊓ D.opens j) ⟶ Spec Γ(X, D.opens i) :=
  Spec.map (CommRingCat.ofHom (res X inf_le_left))

def right (i j : ι) : Spec Γ(X, D.opens i ⊓ D.opens j) ⟶ Spec Γ(X, D.opens j) :=
  Spec.map (CommRingCat.ofHom (res X inf_le_right))

instance left_isOpenImmersion (i j : ι) : IsOpenImmersion (left D i j) :=
  restrictionSpec_isOpenImmersion X inf_le_left (D.affine i) (D.pair_affine i j)

instance right_isOpenImmersion (i j : ι) : IsOpenImmersion (right D i j) :=
  restrictionSpec_isOpenImmersion X inf_le_right (D.affine j) (D.pair_affine i j)

@[reassoc]
theorem left_fromSpec (i j : ι) : left D i j ≫ (D.affine i).fromSpec =
    (D.pair_affine i j).fromSpec :=
  (D.affine i).map_fromSpec (D.pair_affine i j) (homOfLE inf_le_left).op

@[reassoc]
theorem right_fromSpec (i j : ι) : right D i j ≫ (D.affine j).fromSpec =
    (D.pair_affine i j).fromSpec :=
  (D.affine j).map_fromSpec (D.pair_affine i j) (homOfLE inf_le_right).op

/-- The literal affine intersection is the actual base-chart pullback. -/
def isPullback (i j : ι) : IsPullback (left D i j) (right D i j)
    (D.affine i).fromSpec (D.affine j).fromSpec := by
  apply KltDP.SchemeTwoOpenGluing.isPullback_of_range
    (left D i j) (right D i j) (D.affine i).fromSpec (D.affine j).fromSpec
    ((left_fromSpec D i j).trans (right_fromSpec D i j).symm)
  have h : Set.range (left D i j).base =
      (D.affine i).fromSpec.base ⁻¹' ((D.opens i ⊓ D.opens j : X.Opens) : Set X) := by
    rw [← IsAffineOpen.range_fromSpec (D.pair_affine i j), ← left_fromSpec D i j,
      Scheme.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.preimage_image_eq _ (D.affine i).fromSpec.isOpenEmbedding.injective]
  rw [h, IsAffineOpen.range_fromSpec]
  ext x
  change ((D.affine i).fromSpec.base x ∈ D.opens i ∧
    (D.affine i).fromSpec.base x ∈ D.opens j) ↔ _
  have hi : (D.affine i).fromSpec.base x ∈ D.opens i := by
    have hx : (D.affine i).fromSpec.base x ∈ Set.range (D.affine i).fromSpec.base := ⟨x, rfl⟩
    rw [IsAffineOpen.range_fromSpec] at hx
    exact hx
  exact ⟨fun z => z.2, fun z => ⟨hi, z⟩⟩

end KltDP.Geometry.QuadraticAtlasBaseIntersections

#print axioms KltDP.Geometry.QuadraticAtlasBaseIntersections.isPullback
