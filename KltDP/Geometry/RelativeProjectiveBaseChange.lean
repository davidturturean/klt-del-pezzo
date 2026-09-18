/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeProjectiveChartPullbacks
import KltDP.Geometry.SchemePullbackOfOpenCover

/-! # Whole polynomial Proj commutes with original coefficient base change -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Geometry.RelativeProjectiveChart
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] (n : ℕ) (φ : R →+* S)

/-- The actual whole polynomial projectivization has its cartesian base-change
square. All maps are the original coefficient and degree-zero structure maps. -/
theorem isPullback_freeProjectivization :
    IsPullback (coefficientMorphism n φ) (freeProjectivizationToBase S n)
      (freeProjectivizationToBase R n) (Spec.map (CommRingCat.ofHom φ)) := by
  apply SchemeLocalPullback.isPullback_of_openCover (coefficientMorphism_toBase n φ)
    (coordinateChartCover R n)
    (fun i => Spec (.of (coordinateChartRing S n i.down)))
    (fun i => coordinateChartMorphism S n i.down)
    (fun i => Spec.map (CommRingCat.ofHom (coefficientChartMap n φ i.down)))
  · intro i
    exact isPullback_coefficientMorphism_chart n φ i.down
  · intro i
    exact isPullback_coordinateChart_over_base n φ i.down

/-- The literal free projectivization over S is the fiber product over R. -/
def baseChangeIso : freeProjectivization S n ≅
    pullback (freeProjectivizationToBase R n) (Spec.map (CommRingCat.ofHom φ)) :=
  (isPullback_freeProjectivization n φ).isoPullback

@[reassoc (attr := simp)] theorem baseChangeIso_hom_fst :
    (baseChangeIso n φ).hom ≫ pullback.fst _ _ = coefficientMorphism n φ :=
  (isPullback_freeProjectivization n φ).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem baseChangeIso_hom_snd :
    (baseChangeIso n φ).hom ≫ pullback.snd _ _ = freeProjectivizationToBase S n :=
  (isPullback_freeProjectivization n φ).isoPullback_hom_snd

end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.isPullback_freeProjectivization
#print axioms KltDP.Geometry.RelativeProjectiveChart.baseChangeIso
