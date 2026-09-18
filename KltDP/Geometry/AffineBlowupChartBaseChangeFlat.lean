import KltDP.Geometry.AffineBlowupChartBaseChangeEtale

/-! Flatness of the original map between actual Rees charts. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.AffineBlowupChartBaseChange

open AffineBlowup

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (φ : R →+* S) (a : I)
variable [hFlat : Flat (Spec.map (CommRingCat.ofHom φ))]

include hFlat in
/-- Flat base change and the original chart square give flatness of the
original chart map, without an étaleness or coordinate hypothesis. -/
theorem chartMap_isFlat : Flat (Spec.map (CommRingCat.ofHom (chartMap I φ a))) := by
  have hcomp : Flat (Spec.map (CommRingCat.ofHom (chartMap I φ a)) ≫ chartι I a) := by
    rw [chartMap_chartι]
    infer_instance
  exact MorphismProperty.of_postcomp @Flat
    (W' := MorphismProperty.monomorphisms Scheme)
    (Spec.map (CommRingCat.ofHom (chartMap I φ a))) (chartι I a)
    (show Mono (chartι I a) from inferInstance) hcomp

include hFlat in
/-- The corresponding flat scalar action is that of the original chart ring map. -/
theorem chartMap_flat : RingHom.Flat (chartMap I φ a) :=
  (HasRingHomProperty.Spec_iff (P := @Flat)).mp (chartMap_isFlat I φ a)

end KltDP.Geometry.AffineBlowupChartBaseChange
