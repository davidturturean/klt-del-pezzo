import KltDP.Geometry.GluedAdjunctionAffineCancellationInputs

/-!
# The two original affine exterior-module carrier annotations

The measured final cancellation differences concern only these objects:
the source affine-open proof and the target's reconstructed bundled ring.
Normalize them before applying any concrete morphism equation. The native
forward and stored maps are not unfolded or replayed in this producer.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionAffineCarrierNormalization

/-- Eliminate the abstract bundled ring before comparing the two exterior-module carriers. -/
theorem ring_object_eta_top {R : Type u} [CommRing R]
    (A : CommRingCat.{u}) (φ : R →+* A) (n : ℕ) :
    HEq
      (SchemeExteriorPower.sheaf
        (@SchemeKaehlerSheaf.baseRingSheaf R _ (Spec (CommRingCat.of A))
          (Spec.map (CommRingCat.ofHom φ))) n)
      (SchemeExteriorPower.sheaf
        (@SchemeKaehlerSheaf.baseRingSheaf R _ (Spec A)
          (Spec.map (CommRingCat.ofHom φ))) n) := by
  cases A
  rfl

/-- The actual target objects from the original affine chart, without any map reconstruction. -/
def actual_target_carrier {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  ring_object_eta_top (X.presheaf.obj (.op U.1)) (algebraMap R Γ(X, U.1)) 2

/-- Changing only an affine-open proof preserves the original source exterior module. -/
def fromSpec_proof_top_eq {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens)
    (p q : IsAffineOpen U) (n : ℕ) :=
  congrArg
    (fun h : IsAffineOpen U =>
      SchemeExteriorPower.sheaf (SchemeKaehlerSheaf.baseRingSheaf (h.fromSpec ≫ f)) n)
    (Subsingleton.elim p q)

/-- The literal two source proof annotations measured in the checked native equations. -/
def actual_source_carrier {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :=
  fromSpec_proof_top_eq f U.1
    (GluedAdjunctionAmbientChart.affineIso._proof_1 U) U.2 2

end KltDP.Geometry.GluedAdjunctionAffineCarrierNormalization
