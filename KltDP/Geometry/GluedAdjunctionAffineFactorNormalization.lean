import KltDP.Geometry.GluedAdjunctionAffineCancellationInputs

/-!
# Compare the original affine factors through their unchanged differential arrow

Each equality-transport factor is heterogeneously equal to its original
differential arrow by Mathlib's comp_eqToHom_heq. Their common arrow is
literally the same in the checked native expressions, so neither entire
forward equation nor its target carrier needs to be converted here.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionAffineFactorNormalization

private theorem transport_factor_heq {C : Type*} [Category C] {Q P : C}
    (h : Q = P) {S : C} (m : S ⟶ Q) : HEq (m ≫ eqToHom h) m :=
  comp_eqToHom_heq m h

/-- The original forward factor, keeping the original generated transport proof. -/
def native_forward_factor_heq {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  transport_factor_heq
    (GluedAdjunctionAmbientChart.affineIso._proof_4 f U)
    (SchemeKaehlerExteriorPullbackMap.map f U.2.fromSpec 2)

/-- The original stored factor, keeping its separately checked transport proof. -/
def native_stored_factor_heq {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  transport_factor_heq
    (SchemeKaehlerExteriorPullbackTransport.map._proof_1 f U.2.fromSpec
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U.1))))
      (GluedAdjunctionAmbientChart.affineBaseMap_comp f U) 2)
    (SchemeKaehlerExteriorPullbackMap.map f U.2.fromSpec 2)

/-- Equality of the two native factors without identifying their target annotations. -/
def native_factor_heq {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :=
  (native_forward_factor_heq f U).trans (native_stored_factor_heq f U).symm

end KltDP.Geometry.GluedAdjunctionAffineFactorNormalization
