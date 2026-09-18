import KltDP.Compatibility.SmoothNoetherianFlat
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-! Flatness of the original Spec map from its standard-smooth presentation. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry

universe u

/-- The actual standard-smooth map over a Noetherian ring is flat. This uses
the existing module-flatness producer for the same induced scalar action. -/
theorem flat_spec_map_of_standardSmooth
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (g : R →+* S) (hg : g.IsStandardSmooth) :
    Flat (Spec.map (CommRingCat.ofHom g)) := by
  letI : Algebra R S := g.toAlgebra
  letI : Algebra.IsStandardSmooth R S := hg
  apply (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
  exact KltDP.Compatibility.SmoothNoetherianFlat.formallySmooth_flat_of_finiteType
    (R := R) (A := S)

end KltDP.Geometry
