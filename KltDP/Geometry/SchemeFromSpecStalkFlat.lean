import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! Flatness of the original map from the spectrum of an actual stalk.
The affine factor is the original localization germ, not a replacement
ring or a chosen scalar action. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.SchemeFromSpecStalkFlat

theorem affine_fromSpecStalk_flat
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) : Flat (hU.fromSpecStalk hx) := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  letI := hU.isLocalization_stalk ⟨x, hx⟩
  have hflat : (X.presheaf.germ U x hx).hom.Flat := by
    change Module.Flat Γ(X, U) (X.presheaf.stalk x)
    exact IsLocalization.flat _ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  letI : Flat (Spec.map (X.presheaf.germ U x hx)) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr hflat
  unfold IsAffineOpen.fromSpecStalk
  infer_instance

theorem fromSpecStalk_flat (X : Scheme.{u}) (x : X) :
    Flat (X.fromSpecStalk x) :=
  affine_fromSpecStalk_flat
    (isAffineOpen_opensRange (X.affineOpenCover.map x)) (X.affineOpenCover.covers x)

#print axioms fromSpecStalk_flat

end KltDP.Geometry.SchemeFromSpecStalkFlat
