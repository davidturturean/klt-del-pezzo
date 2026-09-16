import KltDP.Geometry.ZeroDimensionalBigness

/-!
# Zero-dimensional subvarieties do not contribute to the exceptional locus

The original vanishing-ideal construction identifies each reduced induced
subvariety with its original irreducible closed subset. Its radical ideal
makes the scheme reduced, and the homeomorphism transfers irreducibility
and dimension. Its actual closed immersion inherits properness over k.

The zero-dimensional bigness theorem therefore applies to the original
restricted line bundle. Every irreducible closed subset has nonnegative
dimension, so non-bigness already implies the positive-dimensional clause
in the unchanged `Positivity.IsExceptionalSubvariety` definition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ZeroDimensionalSubvarietyBigness

variable {X : Scheme.{u}} (Z : IrreducibleCloseds X)

/-- The actual reduced induced scheme has the original subspace topology. -/
def underlyingHomeomorph : Positivity.toScheme Z ≃ₜ (Z : Set X) :=
  (Scheme.IdealSheafData.vanishingIdeal (Positivity.closedSubset Z)).gluedSupportHomeomorph

/-- The reduced induced scheme of the original irreducible closed subset is integral. -/
theorem toScheme_isIntegral : IsIntegral (Positivity.toScheme Z) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (Positivity.closedSubset Z)
  letI : IsReduced (Positivity.toScheme Z) :=
    I.glued_isReduced (Scheme.IdealSheafData.vanishingIdeal_support (I := I)).symm
  letI : IrreducibleSpace (Z : Set X) := Subtype.irreducibleSpace Z.isIrreducible
  letI : IrreducibleSpace (Positivity.toScheme Z) := by
    apply (irreducibleSpace_def (Positivity.toScheme Z)).mpr
    have h := (IrreducibleSpace.isIrreducible_univ (Z : Set X)).image
      (underlyingHomeomorph Z).symm
      (underlyingHomeomorph Z).symm.continuous.continuousOn
    simpa only [Set.image_univ, (underlyingHomeomorph Z).symm.surjective.range_eq] using h
  exact isIntegral_of_irreducibleSpace_of_isReduced (Positivity.toScheme Z)

/-- The dimension comparison is the one induced by this actual homeomorphism. -/
theorem toScheme_dimension :
    topologicalKrullDim (Positivity.toScheme Z) = topologicalKrullDim (Z : Set X) :=
  IsHomeomorph.topologicalKrullDim_eq (underlyingHomeomorph Z)
    (underlyingHomeomorph Z).isHomeomorph

/-- An irreducible closed subset is nonempty, hence has nonnegative dimension. -/
theorem dimension_nonneg : 0 ≤ topologicalKrullDim (Z : Set X) := by
  letI : IrreducibleSpace (Z : Set X) := Subtype.irreducibleSpace Z.isIrreducible
  letI : Nonempty (IrreducibleCloseds (Z : Set X)) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ (Z : Set X), isClosed_univ⟩⟩
  exact Order.krullDim_nonneg

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- The original subvariety structure morphism is proper. -/
theorem inclusion_comp_isProper : IsProper (Positivity.inclusion Z ≫ f) :=
  inferInstance

/-- Restriction of any actual line bundle to a zero-dimensional subvariety is big. -/
theorem isBig_restriction_of_dimension_zero (L : InvertibleSheaf X)
    (hdim : topologicalKrullDim (Z : Set X) = 0) :
    Positivity.IsBig (Positivity.inclusion Z ≫ f)
      (pullbackInvertibleSheaf (Positivity.inclusion Z) L) := by
  letI : IsIntegral (Positivity.toScheme Z) := toScheme_isIntegral Z
  letI : IsProper (Positivity.inclusion Z ≫ f) := inclusion_comp_isProper Z f
  exact ZeroDimensionalBigness.isBig (Positivity.inclusion Z ≫ f)
    ((toScheme_dimension Z).trans hdim) _

/-- Non-bigness on the original subvariety forces its dimension to be positive. -/
theorem dimension_pos_of_not_isBig (L : InvertibleSheaf X)
    (h : ¬ Positivity.IsBig (Positivity.inclusion Z ≫ f)
      (pullbackInvertibleSheaf (Positivity.inclusion Z) L)) :
    0 < topologicalKrullDim (Z : Set X) := by
  apply lt_of_le_of_ne' (dimension_nonneg Z)
  intro hzero
  exact h (isBig_restriction_of_dimension_zero Z f L hzero)

/-- For a proper ambient scheme, the positive-dimensional clause removes
no irreducible subvariety on which the original restriction is not big. -/
theorem isExceptionalSubvariety_iff_not_isBig (L : InvertibleSheaf X) :
    Positivity.IsExceptionalSubvariety f L Z ↔
      ¬ Positivity.IsBig (Positivity.inclusion Z ≫ f)
        (pullbackInvertibleSheaf (Positivity.inclusion Z) L) :=
  ⟨fun h => h.2, fun h => ⟨dimension_pos_of_not_isBig Z f L h, h⟩⟩

end KltDP.Geometry.ZeroDimensionalSubvarietyBigness
