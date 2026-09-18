/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeProjectiveCoefficientCharts
import Mathlib.AlgebraicGeometry.Gluing

/-!
# The actual whole-Proj coefficient morphism, glued from its original charts

The coefficient maps on actual homogeneous fractions commute with both
original overlap restrictions. Native open-cover gluing therefore constructs
the whole morphism and its original base triangle. No Proj map, overlap
compatibility, cartesian square or projective bundle is supplied as a premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Geometry.RelativeProjectiveChart
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] (n : ℕ) (φ : R →+* S)

/-- The actual coefficient morphism from one original coordinate chart. -/
def coefficientChartMorphism (i : Fin (n + 1)) :
    Spec (.of (coordinateChartRing S n i)) ⟶ freeProjectivization R n :=
  Spec.map (CommRingCat.ofHom (coefficientChartMap n φ i)) ≫ coordinateChartMorphism R n i

/-- The chart maps agree on the actual original overlaps. -/
theorem coefficientChartMorphism_compatible (i j : Fin (n + 1)) :
    pullback.fst (coordinateChartMorphism S n i) (coordinateChartMorphism S n j) ≫
        coefficientChartMorphism n φ i =
      pullback.snd (coordinateChartMorphism S n i) (coordinateChartMorphism S n j) ≫
        coefficientChartMorphism n φ j := by
  rw [← cancel_epi (coordinateOverlapIso S n i j).inv,
    ← Category.assoc, coordinateOverlapIso_inv_fst,
    ← Category.assoc, coordinateOverlapIso_inv_snd]
  have hleft :
      Spec.map (CommRingCat.ofHom (toOverlapLeft S n i j)) ≫
          Spec.map (CommRingCat.ofHom (coefficientChartMap n φ i)) =
        Spec.map (CommRingCat.ofHom (coefficientOverlapMap n φ i j)) ≫
          Spec.map (CommRingCat.ofHom (toOverlapLeft R n i j)) := by
    simpa only [CommRingCat.ofHom_comp, Spec.map_comp] using
      congrArg (fun g : coordinateChartRing R n i →+* coordinateOverlapRing S n i j =>
        Spec.map (CommRingCat.ofHom g)) (coefficientChartMap_toOverlapLeft n φ i j)
  have hright :
      Spec.map (CommRingCat.ofHom (toOverlapRight S n i j)) ≫
          Spec.map (CommRingCat.ofHom (coefficientChartMap n φ j)) =
        Spec.map (CommRingCat.ofHom (coefficientOverlapMap n φ i j)) ≫
          Spec.map (CommRingCat.ofHom (toOverlapRight R n i j)) := by
    simpa only [CommRingCat.ofHom_comp, Spec.map_comp] using
      congrArg (fun g : coordinateChartRing R n j →+* coordinateOverlapRing S n i j =>
        Spec.map (CommRingCat.ofHom g)) (coefficientChartMap_toOverlapRight n φ i j)
  dsimp only [coefficientChartMorphism]
  calc
    _ = Spec.map (CommRingCat.ofHom (coefficientOverlapMap n φ i j)) ≫
        (Spec.map (CommRingCat.ofHom (toOverlapLeft R n i j)) ≫
          coordinateChartMorphism R n i) := by
      rw [← Category.assoc, hleft, Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (coefficientOverlapMap n φ i j)) ≫
        (Spec.map (CommRingCat.ofHom (toOverlapRight R n i j)) ≫
          coordinateChartMorphism R n j) :=
      congrArg (fun g => Spec.map (CommRingCat.ofHom (coefficientOverlapMap n φ i j)) ≫ g)
        (overlap_condition R n i j)
    _ = _ := by rw [← Category.assoc, ← hright, Category.assoc]

/-- The coefficient morphism on the original whole polynomial Proj. -/
def coefficientMorphism : freeProjectivization S n ⟶ freeProjectivization R n :=
  (coordinateChartCover S n).glueMorphisms
    (fun i => coefficientChartMorphism n φ i.down)
    (fun i j => coefficientChartMorphism_compatible n φ i.down j.down)

/-- Its restriction is exactly the original homogeneous-localization map. -/
@[reassoc] theorem coordinateChartMorphism_coefficientMorphism (i : Fin (n + 1)) :
    coordinateChartMorphism S n i ≫ coefficientMorphism n φ =
      Spec.map (CommRingCat.ofHom (coefficientChartMap n φ i)) ≫
        coordinateChartMorphism R n i :=
  (coordinateChartCover S n).ι_glueMorphisms _ _ ⟨i⟩

/-- The original whole-Proj morphism retains its original coefficient-base square. -/
@[reassoc] theorem coefficientMorphism_toBase :
    coefficientMorphism n φ ≫ freeProjectivizationToBase R n =
      freeProjectivizationToBase S n ≫ Spec.map (CommRingCat.ofHom φ) := by
  apply (coordinateChartCover S n).hom_ext
  intro i
  change coordinateChartMorphism S n i.down ≫ _ = coordinateChartMorphism S n i.down ≫ _
  rw [← Category.assoc, coordinateChartMorphism_coefficientMorphism,
    Category.assoc, coordinateChartMorphism_over_base,
    ← Category.assoc, coordinateChartMorphism_over_base,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact coefficientChartMap_constants n φ i.down r

end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.coefficientMorphism
#print axioms KltDP.Geometry.RelativeProjectiveChart.coordinateChartMorphism_coefficientMorphism
#print axioms KltDP.Geometry.RelativeProjectiveChart.coefficientMorphism_toBase
