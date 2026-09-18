import KltDP.Geometry.PointBlowupNeighborhoodIndependence
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
Source locality on the original two-piece gluing reduces smoothness of the
point blowup to its actual affine Rees piece. The unchanged complement is
smooth by its original open immersion. No new blowup construction is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PointBlowupGluing

variable {R : Type u} [CommRing R] {X B : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))
    (f : X ⟶ B) [IsSmooth f]

/-- The actual gluing of a smooth affine blowup piece and the unchanged
open complement is smooth over the original base. -/
theorem isSmooth_projection_comp_of_affine
    (hA : IsSmooth (AffineBlowup.toSpec q.asIdeal ≫ j ≫ f)) :
    IsSmooth (projection j q hclosed ≫ f) := by
  apply IsLocalAtSource.of_openCover (P := @IsSmooth)
    (KltDP.SchemeTwoOpenGluing.data
      (overlapOpen q).ι (overlapToPuncture j q hclosed)).openCover
  intro i
  cases i with
  | left =>
      change IsSmooth (affineBlowupι j q hclosed ≫ (projection j q hclosed ≫ f))
      rw [← Category.assoc, affineBlowupι_projection, Category.assoc]
      exact hA
  | right =>
      change IsSmooth (complementι j q hclosed ≫ (projection j q hclosed ≫ f))
      rw [← Category.assoc, complementι_projection]
      infer_instance

end KltDP.Geometry.PointBlowupGluing
