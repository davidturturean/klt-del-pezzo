import KltDP.Geometry.BirationalCartierSystemBigness
import KltDP.Geometry.LinearSystemPullbackIsoTransport
import KltDP.Geometry.CompleteLinearSystemImage
import KltDP.Geometry.CartierPicardComparison

/-!
# Original complete-system birationality implies original bigness

An actual Cartier representative transports the entire original H0
tuple through its actual sheaf isomorphism. On the original non-base
open, the proved pullback and isomorphism comparisons retain exactly
the original complete-system morphism and schematic-image triangle.
The original Cartier-system bigness theorem and equality of the actual
Picard classes then give the unchanged bigness of the original line.

This positive-dimensional endpoint assumes birationality of the original
complete-system image factor. No global generation, Cartier presentation,
replacement map, or line-comparison premise is supplied by the caller.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.CompleteLinearSystemMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open CompleteLinearSystemSections LinearSystemNaturality
  InvertibleSectionNonvanishingOpen OpenPullbackLinearSystemCartierRatios

local instance bigness_nonBaseOpen_integral
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (L : InvertibleSheaf X) (hpos : 0 < dimension f L) :
    IsIntegral (nonBaseOpen f L hpos).toScheme := by
  letI : Nonempty (nonBaseOpen f L hpos) := (nonBaseOpen_nonempty f L hpos).to_subtype
  infer_instance

local instance bigness_image_integral
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (L : InvertibleSheaf X) (hpos : 0 < dimension f L) :
    IsIntegral (SchematicImageGlued.image (morphism f L hpos)) :=
  image_isIntegral f L hpos

/-- Birationality of the original complete linear system on a positive-
dimensional proper integral scheme gives the original section-growth bigness. -/
theorem isBig_of_toImage_isBirationalScheme
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (L : InvertibleSheaf X) (hpos : 0 < dimension f L)
    (hbir : IsBirationalScheme (SchematicImageGlued.toImage (morphism f L hpos)))
    (hdim : 0 < Positivity.natDim X) : Positivity.IsBig f L := by
  obtain ⟨D, ⟨e⟩⟩ := exists_cartierDivisor_module_iso X L.obj
  let M := cartierDivisorInvertibleSheaf X D
  let s := positiveBasisSections f L hpos
  let t := isoSections L M e s
  let U := nonBaseOpen f L hpos
  have hs : (⨆ j, nonvanishingOpen U.toScheme (pullbackInvertibleSheaf U.ι L)
      (pullbackSections U.ι L s j)) = ⊤ :=
    LinearSystemRationalMap.restrictedSections_cover L s
  have ht := pullback_isoSections_cover U.ι L M e s hs
  have hmap : LinearSystemMorphism.morphism (pulledLine U.ι D)
      (pulledTuple U.ι D t) (U.ι ≫ f) ht = morphism f L hpos :=
    morphism_pullback_isoSections U.ι L M e s (U.ι ≫ f) hs
  have hbig : Positivity.IsBig f M :=
    BirationalSectionGrowth.isBig_of_birational_system U.ι f D t ht
      (SchematicImageGlued.inclusion (morphism f L hpos))
      (SchematicImageGlued.toImage (morphism f L hpos)) hbir
      ((SchematicImageGlued.toImage_inclusion (morphism f L hpos)).trans hmap.symm) hdim
  have hclass : M.toPic = L.toPic := by
    letI := Scheme.Modules.monoidalCategory X
    apply Units.ext
    change (M.toPic : Skeleton X.Modules) = (L.toPic : Skeleton X.Modules)
    rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
    exact Quotient.sound ⟨e.symm⟩
  simpa only [Positivity.IsBig, hclass] using hbig

end KltDP.Geometry.CompleteLinearSystemMap
