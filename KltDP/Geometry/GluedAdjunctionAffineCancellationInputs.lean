import KltDP.Geometry.GluedAdjunctionStoredFrameNormalization

/-!
# The original affine chart hom with its native inferred equality carrier

Start from the original affine map itself. Unfold only the left side of
its reflexive equation, then apply the native inverse law in an abstract
category. The stored frame is normalized independently from its checked
original equation. Cancellation preserves both original map constants.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionOriginalAffineNormalization

private theorem native_triangle {C : Type*} [Category C] {S T P Q : C}
    {e : T ≅ P} {x : S ⟶ T} {u m : S ⟶ Q} {v : Q ⟶ P}
    (hx : u ≫ v ≫ e.inv = x) (hu : u = m) : x ≫ e.hom = m ≫ v := by
  rw [← hx]
  simp only [hu, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem cancel_after_native {C : Type*} [Category C] {S T P : C}
    {e : T ≅ P} {x y : S ⟶ T} {m : S ⟶ P}
    (hx : x ≫ e.hom = m) (hy : y = m ≫ e.inv) : x = y := by
  apply (cancel_mono e.hom).mp
  simpa only [hy, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hx

/-- Retain the original map's exact Hom/Eq carrier while exposing only its defining side. -/
private def original_expanded_hom {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) => by
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hSmooth
    have h := Eq.refl ((GluedAdjunctionAmbientChart.affineIso f U).hom)
    conv at h =>
      lhs
      unfold GluedAdjunctionAmbientChart.affineIso
      simp only [Iso.trans_hom, Iso.symm_hom]
    exact h

/-- Infer the original native forward triangle from the exposed original inverse factors. -/
private def forward_triangle_proof {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hSmooth
    native_triangle (original_expanded_hom f U hSmooth)
      (SchemeKaehlerExteriorOpenRestriction.pullbackIso_hom f U.2.fromSpec 2)

/-- Keep the checked stored equation's carrier while exposing only its transported factor. -/
private def stored_expanded_hom {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) => by
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hSmooth
    have h := GluedAdjunctionStoredFrameNormalization.affine_normalization f U hSmooth
    dsimp only at h
    conv at h =>
      rhs
      unfold SchemeKaehlerExteriorPullbackTransport.map
    exact h

/-- The exact checked forward-triangle proof, without rebuilding its proposition. -/
def nativeForwardTriangle := @forward_triangle_proof

/-- The exact checked stored equation, with its original inferred carrier. -/
def nativeStoredEquation := @stored_expanded_hom

end KltDP.Geometry.GluedAdjunctionOriginalAffineNormalization
