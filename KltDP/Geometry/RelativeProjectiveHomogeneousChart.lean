/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeProjectiveHomogeneousRestriction

/-! # Whole coefficient change on every actual homogeneous projective chart -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Geometry.RelativeProjectiveChart
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] (n : ℕ) (φ : R →+* S)

/-- The whole coefficient morphism restricts to the original fraction map
on every positive-degree homogeneous basic open, not only the coordinates. -/
@[reassoc] theorem homogeneousChart_coefficientMorphism
    {d : ℕ} (hd : 0 < d) (p : homogeneousRing R n) (hp : p ∈ grading R n d) :
    Proj.awayι (grading S n) (MvPolynomial.map φ p)
        ((show p.IsHomogeneous d from hp).map φ) hd ≫ coefficientMorphism n φ =
      Spec.map (CommRingCat.ofHom (coefficientMap n φ p (MvPolynomial.map φ p) rfl)) ≫
        Proj.awayι (grading R n) p hp hd := by
  let q : homogeneousRing S n := MvPolynomial.map φ p
  have hq : q ∈ grading S n d := (show p.IsHomogeneous d from hp).map φ
  let f := Proj.awayι (grading S n) q hq hd
  apply ((coordinateChartCover S n).pullbackCover f).hom_ext
  intro i
  change pullback.fst f (coordinateChartMorphism S n i.down) ≫
      (f ≫ coefficientMorphism n φ) =
    pullback.fst f (coordinateChartMorphism S n i.down) ≫
      (Spec.map (CommRingCat.ofHom (coefficientMap n φ p q rfl)) ≫
        Proj.awayι (grading R n) p hp hd)
  rw [← Category.assoc, pullback.condition, Category.assoc,
    coordinateChartMorphism_coefficientMorphism]
  let e := Proj.pullbackAwayιIso (grading S n) hq hd
    (coordinate_mem S n i.down) Nat.one_pos rfl
  rw [← cancel_epi e.inv]
  change e.inv ≫ (pullback.snd f (coordinateChartMorphism S n i.down) ≫
      (Spec.map (CommRingCat.ofHom (coefficientChartMap n φ i.down)) ≫
        coordinateChartMorphism R n i.down)) =
    e.inv ≫ (pullback.fst f (coordinateChartMorphism S n i.down) ≫
      (Spec.map (CommRingCat.ofHom (coefficientMap n φ p q rfl)) ≫
        Proj.awayι (grading R n) p hp hd))
  simp only [← Category.assoc, e, f, coordinateChartMorphism, Proj.pullbackAwayιIso_inv_fst,
    Proj.pullbackAwayιIso_inv_snd]
  have hprod : MvPolynomial.map φ (p * MvPolynomial.X i.down) =
      q * MvPolynomial.X i.down := by simp [q]
  have hleft := SpecMap_coefficientMap_awayMap n φ
    (a := MvPolynomial.X i.down) (b := MvPolynomial.X i.down)
    (c := p) (d := q) (x := p * MvPolynomial.X i.down)
    (y := q * MvPolynomial.X i.down)
    (by simp) rfl hprod (coordinate_mem R n i.down) hp (mul_comm _ _) (mul_comm _ _)
  have hright := SpecMap_coefficientMap_awayMap n φ
    (a := p) (b := q) (c := MvPolynomial.X i.down) (d := MvPolynomial.X i.down)
    (x := p * MvPolynomial.X i.down) (y := q * MvPolynomial.X i.down)
    rfl (by simp) hprod hp (coordinate_mem R n i.down) rfl rfl
  have hoverlap :
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (grading R n)
          hp (mul_comm p (MvPolynomial.X i.down)))) ≫ coordinateChartMorphism R n i.down =
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (grading R n)
          (coordinate_mem R n i.down) rfl)) ≫ Proj.awayι (grading R n) p hp hd := by
    let er := Proj.pullbackAwayιIso (grading R n) hp hd
      (coordinate_mem R n i.down) Nat.one_pos rfl
    have h := congrArg (fun a => er.inv ≫ a)
      (pullback.condition (f := Proj.awayι (grading R n) p hp hd)
        (g := coordinateChartMorphism R n i.down))
    simpa only [← Category.assoc, er, coordinateChartMorphism, Proj.pullbackAwayιIso_inv_fst,
      Proj.pullbackAwayιIso_inv_snd] using h.symm
  dsimp only [coefficientChartMap]
  rw [hleft, hright]
  simpa only [Category.assoc] using
    congrArg (fun a => Spec.map (CommRingCat.ofHom
      (coefficientMap n φ (p * MvPolynomial.X i.down)
        (q * MvPolynomial.X i.down) hprod)) ≫ a) hoverlap

end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.homogeneousChart_coefficientMorphism
