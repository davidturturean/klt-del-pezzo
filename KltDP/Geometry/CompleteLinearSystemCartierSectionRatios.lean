import KltDP.Geometry.BirationalCartierCommonSectionRatios
import KltDP.Geometry.CompleteLinearSystemImage

/-!
# Common section ratios from the original complete Cartier system

The tuple is the entire original H0 basis. Its actual non-base open,
derived pullback cover, and original schematic-image factorization
discharge the generic linear-system hypotheses. Only birationality of
that original image factor is assumed. No ambient generation or chosen
replacement projective map is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace KltDP.Geometry.CompleteLinearSystemMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open CompleteLinearSystemSections ModuleCohomology

local instance ratios_nonBaseOpen_integral
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (L : InvertibleSheaf X) (hpos : 0 < dimension f L) :
    IsIntegral (nonBaseOpen f L hpos).toScheme := by
  letI : Nonempty (nonBaseOpen f L hpos) := (nonBaseOpen_nonempty f L hpos).to_subtype
  infer_instance

local instance ratios_image_integral
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (L : InvertibleSheaf X) (hpos : 0 < dimension f L) :
    IsIntegral (SchematicImageGlued.image (morphism f L hpos)) :=
  image_isIntegral f L hpos

/-- Birationality of the original complete Cartier-system factor gives
actual common-denominator sections in one positive original power. -/
theorem exists_common_cartier_section_ratios
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (D : CartierDivisor X)
    (hpos : 0 < dimension f (cartierDivisorInvertibleSheaf X D))
    (hbir : IsBirationalScheme (SchematicImageGlued.toImage
      (morphism f (cartierDivisorInvertibleSheaf X D) hpos)))
    {ι : Type v} [Fintype ι] (z : ι → X.functionField) :
    ∃ (d : ℕ) (t₀ : sections (cartierDivisorModule X (d • D)))
      (t : ι → sections (cartierDivisorModule X (d • D))),
      0 < d ∧ t₀ ≠ 0 ∧ ∀ i,
        cartierGlobalSectionRationalValue X (d • D) (t i) /
          cartierGlobalSectionRationalValue X (d • D) t₀ = z i := by
  exact OpenPullbackLinearSystemCartierRatios.exists_common_section_ratios
    (nonBaseOpen f (cartierDivisorInvertibleSheaf X D) hpos).ι f D
    (positiveBasisSections f (cartierDivisorInvertibleSheaf X D) hpos)
    (LinearSystemRationalMap.restrictedSections_cover
      (cartierDivisorInvertibleSheaf X D)
      (positiveBasisSections f (cartierDivisorInvertibleSheaf X D) hpos))
    (SchematicImageGlued.inclusion (morphism f (cartierDivisorInvertibleSheaf X D) hpos))
    (SchematicImageGlued.toImage (morphism f (cartierDivisorInvertibleSheaf X D) hpos))
    hbir (SchematicImageGlued.toImage_inclusion
      (morphism f (cartierDivisorInvertibleSheaf X D) hpos)) z

end KltDP.Geometry.CompleteLinearSystemMap
