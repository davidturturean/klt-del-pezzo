import KltDP.Geometry.AffineBlowupChartBaseChangeEtale
import KltDP.Examples.FrobeniusBlowupSmooth

/-!
The actual blowup of the extended plane origin is smooth over the original
field. Flat base change gives the original étale blowup comparison, which
composes with the already proved smooth structure of the actual plane blowup.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffinePlaneEtaleBlowupSmooth

open AffineBlowup AffineBlowupChartBaseChange
open KltDP.Examples.FrobeniusBlowupContact KltDP.Examples.FrobeniusBlowupSmooth

variable {k R : Type u} [Field k] [CommRing R]
    (φ : planeRing k →+* R)
    [Flat (Spec.map (CommRingCat.ofHom φ))]
    [IsEtale (Spec.map (CommRingCat.ofHom φ))]

/-- Smooth relative dimension two for the actual extended-center blowup,
with its original composite structure morphism over the original field. -/
theorem isSmoothOfRelativeDimension_two :
    IsSmoothOfRelativeDimension 2
      (toSpec (Ideal.map φ (centerIdeal (k := k))) ≫
        Spec.map (CommRingCat.ofHom φ) ≫ planeStructure) := by
  letI : IsEtale (openBaseChangeMap (centerIdeal (k := k)) φ) :=
    comparison_isEtale (centerIdeal (k := k)) φ
  have h : IsSmoothOfRelativeDimension (0 + 2)
      (openBaseChangeMap (centerIdeal (k := k)) φ ≫ blowupStructure) := inferInstance
  rw [blowupStructure, ← Category.assoc, openBaseChangeMap_toSpec, Category.assoc] at h
  exact h

end KltDP.Geometry.AffinePlaneEtaleBlowupSmooth
