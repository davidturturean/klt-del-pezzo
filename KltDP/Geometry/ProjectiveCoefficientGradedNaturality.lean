/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.ProjectiveCoefficientGradedFractions
import KltDP.Geometry.RelativeProjectiveHomogeneousChart

/-! # Scheme naturality of original coefficient change and graded coordinates -/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.RelativeProjectiveChart
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] (n : ℕ) (φ : R →+* S)

/-- The original homogeneous-chart formula with its literal target denominator. -/
@[reassoc] theorem homogeneousChart_coefficientMorphism_of_eq
    {d : ℕ} (hd : 0 < d) (p : homogeneousRing R n) (hp : p ∈ grading R n d)
    (q : homogeneousRing S n) (hpq : MvPolynomial.map φ p = q) :
    Proj.awayι (grading S n) q (hpq ▸ (show p.IsHomogeneous d from hp).map φ) hd ≫
        coefficientMorphism n φ =
      Spec.map (CommRingCat.ofHom (coefficientMap n φ p q hpq)) ≫
        Proj.awayι (grading R n) p hp hd := by
  subst q
  exact homogeneousChart_coefficientMorphism n φ hd p hp

variable
  (eR : homogeneousRing R n ≃+* homogeneousRing R n)
  (heR : KltDP.GradedProjIso.PreservesDegrees (𝒜 := grading R n) (ℬ := grading R n) eR)
  (eS : homogeneousRing S n ≃+* homogeneousRing S n)
  (heS : KltDP.GradedProjIso.PreservesDegrees (𝒜 := grading S n) (ℬ := grading S n) eS)
  (hcompat : ∀ p, MvPolynomial.map φ (eR p) = eS (MvPolynomial.map φ p))

include hcompat

/-- The commuting square of the original polynomial coefficient and graded
coordinate maps gives the commuting square of their actual scheme maps. -/
theorem coefficientMorphism_gradedMap :
    KltDP.GradedProjIso.map eS heS ≫ coefficientMorphism n φ =
      coefficientMorphism n φ ≫ KltDP.GradedProjIso.map eR heR := by
  have hchart (i : Fin (n + 1)) :
      Proj.awayι (grading S n) (eS (MvPolynomial.X i))
          ((heS 1 _).mp (coordinate_mem S n i)) Nat.one_pos ≫
        (KltDP.GradedProjIso.map eS heS ≫ coefficientMorphism n φ) =
      Proj.awayι (grading S n) (eS (MvPolynomial.X i))
          ((heS 1 _).mp (coordinate_mem S n i)) Nat.one_pos ≫
        (coefficientMorphism n φ ≫ KltDP.GradedProjIso.map eR heR) := by
    have himage : MvPolynomial.map φ (eR (MvPolynomial.X i)) =
        eS (MvPolynomial.X i) := by rw [hcompat, MvPolynomial.map_X]
    have hspec :
        Spec.map (CommRingCat.ofHom (KltDP.GradedProjIso.awayMap eS heS
            (MvPolynomial.X i) (eS (MvPolynomial.X i)) rfl)) ≫
          Spec.map (CommRingCat.ofHom (coefficientChartMap n φ i)) =
        Spec.map (CommRingCat.ofHom (coefficientMap n φ
            (eR (MvPolynomial.X i)) (eS (MvPolynomial.X i)) himage)) ≫
          Spec.map (CommRingCat.ofHom (KltDP.GradedProjIso.awayMap eR heR
            (MvPolynomial.X i) (eR (MvPolynomial.X i)) rfl)) := by
      simpa only [CommRingCat.ofHom_comp, Spec.map_comp, coefficientChartMap] using
        congrArg (fun g : coordinateChartRing R n i →+*
          HomogeneousLocalization.Away (grading S n) (eS (MvPolynomial.X i)) =>
            Spec.map (CommRingCat.ofHom g))
          (coefficientMap_gradedAwayMap n φ eR heR eS heS hcompat
            (MvPolynomial.X i) (MvPolynomial.X i) (by simp)).symm
    calc
      _ = Spec.map (CommRingCat.ofHom (KltDP.GradedProjIso.awayMap eS heS
            (MvPolynomial.X i) (eS (MvPolynomial.X i)) rfl)) ≫
          (Spec.map (CommRingCat.ofHom (coefficientChartMap n φ i)) ≫
            coordinateChartMorphism R n i) := by
        rw [← Category.assoc, KltDP.GradedProjIso.awayι_comp_map eS heS Nat.one_pos
          (MvPolynomial.X i) (coordinate_mem S n i) (eS (MvPolynomial.X i)) rfl,
          Category.assoc]
        exact congrArg (fun g => Spec.map (CommRingCat.ofHom
          (KltDP.GradedProjIso.awayMap eS heS (MvPolynomial.X i)
            (eS (MvPolynomial.X i)) rfl)) ≫ g)
          (coordinateChartMorphism_coefficientMorphism n φ i)
      _ = Spec.map (CommRingCat.ofHom (coefficientMap n φ
            (eR (MvPolynomial.X i)) (eS (MvPolynomial.X i)) himage)) ≫
          (Spec.map (CommRingCat.ofHom (KltDP.GradedProjIso.awayMap eR heR
            (MvPolynomial.X i) (eR (MvPolynomial.X i)) rfl)) ≫
              coordinateChartMorphism R n i) := by
        simpa only [Category.assoc] using
          congrArg (fun g => g ≫ coordinateChartMorphism R n i) hspec
      _ = _ := by
        symm
        rw [← Category.assoc, homogeneousChart_coefficientMorphism_of_eq n φ Nat.one_pos
          (eR (MvPolynomial.X i)) ((heR 1 _).mp (coordinate_mem R n i))
          (eS (MvPolynomial.X i)) himage, Category.assoc,
          KltDP.GradedProjIso.awayι_comp_map eR heR Nat.one_pos
            (MvPolynomial.X i) (coordinate_mem R n i) (eR (MvPolynomial.X i)) rfl]
        rfl
  let F := KltDP.GradedProjIso.map eS heS ≫ coefficientMorphism n φ
  let G := coefficientMorphism n φ ≫ KltDP.GradedProjIso.map eR heR
  change F = G
  rw [← cancel_epi (KltDP.GradedProjIso.iso eS heS).hom]
  apply (coordinateChartCover S n).hom_ext
  intro i
  let A := Proj.awayι (grading S n) (eS (MvPolynomial.X i.down))
    ((heS 1 _).mp (coordinate_mem S n i.down)) Nat.one_pos
  let v := Spec.map (CommRingCat.ofHom (KltDP.GradedProjIso.awayMap eS.symm
    (KltDP.GradedProjIso.preservesDegrees_symm eS heS)
    (eS (MvPolynomial.X i.down)) (MvPolynomial.X i.down) (eS.symm_apply_apply _)))
  have ht : coordinateChartMorphism S n i.down ≫ (KltDP.GradedProjIso.iso eS heS).hom =
      v ≫ A := KltDP.GradedProjIso.awayι_comp_map eS.symm
        (KltDP.GradedProjIso.preservesDegrees_symm eS heS) Nat.one_pos
        (eS (MvPolynomial.X i.down)) ((heS 1 _).mp (coordinate_mem S n i.down))
        (MvPolynomial.X i.down) (eS.symm_apply_apply _)
  change coordinateChartMorphism S n i.down ≫ ((KltDP.GradedProjIso.iso eS heS).hom ≫ F) =
    coordinateChartMorphism S n i.down ≫ ((KltDP.GradedProjIso.iso eS heS).hom ≫ G)
  calc
    _ = (coordinateChartMorphism S n i.down ≫ (KltDP.GradedProjIso.iso eS heS).hom) ≫ F :=
      (Category.assoc _ _ _).symm
    _ = (v ≫ A) ≫ F := congrArg (fun g => g ≫ F) ht
    _ = v ≫ (A ≫ F) := Category.assoc _ _ _
    _ = v ≫ (A ≫ G) := congrArg (fun g => v ≫ g) (hchart i.down)
    _ = (v ≫ A) ≫ G := (Category.assoc _ _ _).symm
    _ = (coordinateChartMorphism S n i.down ≫ (KltDP.GradedProjIso.iso eS heS).hom) ≫ G :=
      congrArg (fun g => g ≫ G) ht.symm
    _ = _ := Category.assoc _ _ _

end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.coefficientMorphism_gradedMap
