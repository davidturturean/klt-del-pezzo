import KltDP.Geometry.GluedAdjunctionAffineNativeProjectionCancellation

/-! Cancel the original inferred composites before converting their native target annotations. -/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u v w
namespace KltDP.Geometry.GluedAdjunctionOriginalAffineNormalization

private theorem of_exterior_heq_to_eq {A : Type u} [CommRing A]
    {C : Type v} [Category.{w} C] (F : ModuleCat.{u} A → C)
    (V : Type u) [AddCommGroup V] [Module A V] (n : ℕ) {S : C}
    {x : S ⟶ F (ModuleCat.of A (⋀[A]^n V))}
    {y : S ⟶ F ((ModuleCat.of A V).exteriorPower n)}
    (h : HEq x y) : x = y := eq_of_heq h

/-- Keep heterogeneous equality until the two original maps have been cancelled. -/
private def original_affine_hom_heq {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hSmooth
    GluedAdjunctionAffineNativeProjectionCancellation.cancel_abstract_projections
      (fun A => (Spec A).Modules)
      (fun A M => (M.tilde : (Spec A).Modules))
      (fun A M => @SchemeExteriorPower.sheaf (Spec A) M 2)
      (fun A φ => @SchemeKaehlerSheaf.baseRingSheaf R _ (Spec A)
        (Spec.map (CommRingCat.ofHom φ)))
      (X.presheaf.obj (.op U.1)) (algebraMap R Γ(X, U.1))
      (KaehlerDifferential R Γ(X, U.1)) 2
      (AffineDifferentialExteriorTildeMap.standardSmoothIso R Γ(X, U.1))
      (GluedAdjunctionAffineNativeCompositeNormalization.native_composites_heq f U hSmooth)

/-- Convert only the original native ModuleCat.of/exteriorPower target annotation. -/
private def original_affine_hom_proof {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) =>
    of_exterior_heq_to_eq
      ((fun (A : CommRingCat.{u}) (M : ModuleCat.{u} A) =>
        (M.tilde : (Spec A).Modules)) (X.presheaf.obj (.op U.1)))
      (KaehlerDifferential R Γ(X, U.1)) 2
      (original_affine_hom_heq f U hSmooth)

/-- Expose the exact inferred proof for downstream original-map applications. -/
def nativeOriginalAffineHom := @original_affine_hom_proof

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

/-- The actual original affine chart hom equals the original stored frame hom. -/
theorem original_affine_hom {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)],
      statementOf (original_affine_hom_proof f U hSmooth) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro hSmooth
  exact original_affine_hom_proof f U hSmooth

end KltDP.Geometry.GluedAdjunctionOriginalAffineNormalization
