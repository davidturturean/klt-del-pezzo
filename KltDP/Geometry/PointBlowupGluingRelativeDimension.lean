import KltDP.Geometry.PointBlowupGluingSmooth

/-!
# Relative dimension on the original two-piece point-blowup gluing

Apply the pinned source locality of smooth relative dimension to the same
original gluing cover. The unchanged complement uses its actual open
immersion; the affine input is supplied by the derived étale Rees model.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PointBlowupGluing

variable {R : Type u} [CommRing R] {X B : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))
    (f : X ⟶ B) (n : ℕ) [IsSmoothOfRelativeDimension n f]

theorem isSmoothOfRelativeDimension_projection_comp_of_affine
    (hA : IsSmoothOfRelativeDimension n (AffineBlowup.toSpec q.asIdeal ≫ j ≫ f)) :
    IsSmoothOfRelativeDimension n (projection j q hclosed ≫ f) := by
  apply IsLocalAtSource.of_openCover (P := @IsSmoothOfRelativeDimension n)
    (KltDP.SchemeTwoOpenGluing.data
      (overlapOpen q).ι (overlapToPuncture j q hclosed)).openCover
  intro i
  cases i with
  | left =>
      change IsSmoothOfRelativeDimension n
        (affineBlowupι j q hclosed ≫ (projection j q hclosed ≫ f))
      rw [← Category.assoc, affineBlowupι_projection, Category.assoc]
      exact hA
  | right =>
      change IsSmoothOfRelativeDimension n
        (complementι j q hclosed ≫ (projection j q hclosed ≫ f))
      rw [← Category.assoc, complementι_projection]
      simpa only [Nat.zero_add] using
        (inferInstance : IsSmoothOfRelativeDimension (0 + n) ((puncture j q hclosed).ι ≫ f))

end KltDP.Geometry.PointBlowupGluing
