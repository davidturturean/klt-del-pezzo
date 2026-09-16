import KltDP.Geometry.SmoothSurfaceRegularity
import KltDP.Geometry.CartierPicardEndpointTensor

/-!
# Divisor and Picard comparisons under actual surface smoothness

Smoothness of the original structure morphism proves regularity of the
original stalks. Applying the existing geometric Cartier/Weil and Picard
constructions to that proof gives the actual smooth-surface comparisons.
The normalization theorems retain the original Cartier-to-Weil map,
principal rational functions, and constructed O(D).

The integral Picard group has its canonical integer-linear map into its
actual tensor product with ℚ. The rational comparison preserves this map
and its torsion kernel. The codomain is rational linear-equivalence
classes; the further numerical-class quotient belongs to intersection
theory and is not identified with this space.
-/

noncomputable section

open AlgebraicGeometry TensorProduct

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The canonical map from the original integral sheaf Picard group to
its actual tensor product with the rationals. -/
def picardTensorInclusion :
    Additive X.toScheme.Pic →ₗ[ℤ] ℚ ⊗[ℤ] Additive X.toScheme.Pic :=
  TensorProduct.mk ℤ ℚ (Additive X.toScheme.Pic) 1

variable [IsAlgClosed k] [IsSmooth X.structureMorphism]

/-- Every original Weil divisor of the smooth surface determines its
actual Cartier inverse image. -/
def smoothWeilCartierEquiv : X.WeilDivisor ≃+ CartierDivisor X.toScheme :=
  (X.regularCartierWeilEquiv (X.regularPoints_of_isSmooth)).symm

/-- The forward geometric Cartier-to-Weil map recovers exactly the
given original Weil divisor. -/
theorem cartierToWeil_smoothWeilCartierEquiv (D : X.WeilDivisor) :
    X.cartierToWeilHom (X.smoothWeilCartierEquiv D) = D :=
  (X.regularCartierWeilEquiv (X.regularPoints_of_isSmooth)).apply_symm_apply D

/-- The smooth comparison preserves the principal divisor of the same
nonzero element of the original function field. -/
theorem smoothWeilCartierEquiv_principal (f : X.toScheme.functionFieldˣ) :
    X.smoothWeilCartierEquiv (X.principalDivisor f) =
      principalCartierDivisorHom X.toScheme (Additive.ofMul f) := by
  apply (X.regularCartierWeilEquiv (X.regularPoints_of_isSmooth)).injective
  exact ((X.regularCartierWeilEquiv (X.regularPoints_of_isSmooth)).apply_symm_apply _).trans
    (X.regularCartierWeilEquiv_principal (X.regularPoints_of_isSmooth) f).symm

/-- Original integral Weil classes are the original sheaf Picard group
on the surface whose actual structure morphism is smooth. -/
def smoothWeilClassPicardEquiv : X.WeilClassGroup ≃+ Additive X.toScheme.Pic :=
  X.regularWeilClassPicardEquiv (X.regularPoints_of_isSmooth)

/-- The class comparison represents the original Weil divisor by the
constructed O(D) of its actual Cartier inverse image. -/
theorem smoothWeilClassPicardEquiv_representative (D : X.WeilDivisor) :
    (X.smoothWeilClassPicardEquiv (X.weilClassMap D)).toMul =
      cartierPicardClass X.toScheme (X.smoothWeilCartierEquiv D) :=
  X.regularWeilClassPicardEquiv_representative (X.regularPoints_of_isSmooth) D

/-- Each rational Weil divisor has some positive integral multiple
represented by an actual Cartier divisor. No common index is chosen. -/
theorem exists_positive_cartier_multiple_of_isSmooth (D : X.RationalWeilDivisor) :
    ∃ n : ℕ, 0 < n ∧ ∃ A : CartierDivisor X.toScheme,
      rationalizeWeilDivisor X (X.cartierToWeilHom A) = n • D :=
  (X.qCartier_iff_exists_positive_multiple D).mp
    (X.qCartier_of_regular (X.regularPoints_of_isSmooth) D)

/-- The tensor product of the original integral Picard group is the
actual rational Weil class space under original-surface smoothness. -/
def smoothPicardTensorRationalEquiv :
    ℚ ⊗[ℤ] Additive X.toScheme.Pic ≃ₗ[ℚ] X.RationalWeilClassGroup :=
  X.regularPicardTensorRationalEquiv (X.regularPoints_of_isSmooth)

/-- The canonical tensor map followed by the rational equivalence is
the original integral Weil-class rationalization through the Picard
comparison. Both maps retain their original domains and codomains. -/
theorem smoothPicardTensorRationalEquiv_inclusion (c : Additive X.toScheme.Pic) :
    X.smoothPicardTensorRationalEquiv (X.picardTensorInclusion c) =
      X.weilClassRationalization (X.smoothWeilClassPicardEquiv.symm c) :=
  X.regularPicardTensorRationalEquiv_one_tmul (X.regularPoints_of_isSmooth) c

/-- The actual integral-to-tensor map kills exactly torsion, so the
integral Picard group is not replaced by its rationalization. -/
theorem picardTensorInclusion_eq_zero_iff (c : Additive X.toScheme.Pic) :
    X.picardTensorInclusion c = 0 ↔ ∃ n : ℕ, 0 < n ∧ n • c = 0 := by
  rw [← X.smoothPicardTensorRationalEquiv.map_eq_zero_iff,
    X.smoothPicardTensorRationalEquiv_inclusion]
  exact X.regularPicardRationalization_eq_zero_iff (X.regularPoints_of_isSmooth) c

/-- Tensor rationalization of the original O(D) gives the rational
class of that same Cartier divisor's original Weil image. -/
theorem smoothPicardTensorRationalEquiv_cartier (D : CartierDivisor X.toScheme) :
    X.smoothPicardTensorRationalEquiv
        (X.picardTensorInclusion (cartierPicardHom X.toScheme D)) =
      X.rationalWeilClassMap (rationalizeWeilDivisor X (X.cartierToWeilHom D)) :=
  X.regularPicardTensorRationalEquiv_cartier (X.regularPoints_of_isSmooth) D

end KltDP.Geometry.NormalProjectiveSurface
