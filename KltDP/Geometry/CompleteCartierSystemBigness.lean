import KltDP.Geometry.BirationalCartierSystemBigness
import KltDP.Geometry.CompleteLinearSystemBirational

/-!
# Birationality of the original complete Cartier system implies bigness

The whole original section basis, its actual non-base open, and the
canonical factorization through its schematic image supply all data of
the proved birational-system theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CompleteLinearSystemMap

open CompleteLinearSystemSections

attribute [local instance] subsystem_nonBaseOpen_integral subsystem_image_integral

/-- The original complete-system birationality implies the unchanged
section-growth predicate for the original positive-dimensional Cartier line. -/
theorem isBig_of_cartier_toImage_birational
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (D : CartierDivisor X)
    (hpos : 0 < dimension f (cartierDivisorInvertibleSheaf X D))
    (hbir : IsBirationalScheme (SchematicImageGlued.toImage
      (morphism f (cartierDivisorInvertibleSheaf X D) hpos)))
    (hdim : 0 < Positivity.natDim X) :
    Positivity.IsBig f (cartierDivisorInvertibleSheaf X D) := by
  exact BirationalSectionGrowth.isBig_of_birational_system
    (nonBaseOpen f (cartierDivisorInvertibleSheaf X D) hpos).ι f D
    (positiveBasisSections f (cartierDivisorInvertibleSheaf X D) hpos)
    (LinearSystemRationalMap.restrictedSections_cover
      (cartierDivisorInvertibleSheaf X D)
      (positiveBasisSections f (cartierDivisorInvertibleSheaf X D) hpos))
    (SchematicImageGlued.inclusion (morphism f (cartierDivisorInvertibleSheaf X D) hpos))
    (SchematicImageGlued.toImage (morphism f (cartierDivisorInvertibleSheaf X D) hpos))
    hbir (SchematicImageGlued.toImage_inclusion
      (morphism f (cartierDivisorInvertibleSheaf X D) hpos)) hdim

end KltDP.Geometry.CompleteLinearSystemMap
