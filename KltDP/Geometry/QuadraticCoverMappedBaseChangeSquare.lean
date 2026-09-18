import KltDP.Geometry.QuadraticCoverBaseChangeSquare
import KltDP.Geometry.QuadraticCoverMappedRescaling

/-!
# A unit generator change preserves the actual coefficient pullback square

This joins existing quotient rescaling and coefficient base change, retaining
both original scheme maps. No geometric comparison is supplied as an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCover

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The original mapped and rescaled quadratic chart is the actual base change. -/
theorem mappedRescaleIsPullback (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) :
    IsPullback (mappedRescaleMap f s t v h) (toBase t) (toBase s)
      (Spec.map (CommRingCat.ofHom f)) := by
  letI : Algebra R S := f.toAlgebra
  have h₁ : IsPullback (rescaleSpecIso (f s) t v h).hom (toBase t)
      (toBase (f s)) (𝟙 (Spec (CommRingCat.of S))) :=
    IsPullback.of_horiz_isIso ⟨by simp only [rescaleSpecIso_hom_toBase, Category.comp_id]⟩
  simpa only [Category.id_comp, ← mappedRescaleMap_eq] using
    h₁.paste_horiz (baseChangeIsPullback (S := S) s)

#print axioms mappedRescaleIsPullback

end KltDP.Geometry.QuadraticCover
