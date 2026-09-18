/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeProjectiveChartBaseChange

/-!
# The literal projective basic open and its base-change square

Every corner below is an original Proj basic open or the spectrum of its base
ring. The maps to the base are restrictions of `Proj.toSpecZero` followed by
the original coefficient map. This supplies the chart-level cartesian bridge;
no globally glued projective bundle is defined or assumed here.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace KltDP.Geometry.RelativeProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (n : ℕ)

/-- The original free projectivization, with `n + 1` generators. -/
abbrev freeProjectivization : Scheme := Proj (grading R n)

/-- Its original structure morphism, through degree zero. -/
def freeProjectivizationToBase : freeProjectivization R n ⟶ Spec (.of R) :=
  Proj.toSpecZero (grading R n) ≫ Spec.map (CommRingCat.ofHom (baseConstants R n))

/-- The actual open subset where the first homogeneous coordinate is nonzero. -/
abbrev standardOpen : (freeProjectivization R n).Opens :=
  Proj.basicOpen (grading R n) (coordinate R n)

abbrev standardChart : Scheme := (standardOpen R n).toScheme

def standardChartToBase : standardChart R n ⟶ Spec (.of R) :=
  (standardOpen R n).ι ≫ freeProjectivizationToBase R n

/-- The native chart isomorphism to the actual homogeneous-localization ring. -/
def standardChartIsoSpec : standardChart R n ≅ Spec (.of (chartRing R n)) :=
  Proj.basicOpenIsoSpec (grading R n) (coordinate R n)
    (MvPolynomial.isHomogeneous_X R (0 : Fin (n + 1))) (by decide)

@[reassoc] theorem standardChartIsoSpec_inv_toBase :
    (standardChartIsoSpec R n).inv ≫ standardChartToBase R n =
      Spec.map (CommRingCat.ofHom (constants R n)) := by
  have h := congrArg
    (fun f => f ≫ Spec.map (CommRingCat.ofHom (baseConstants R n)))
    (Proj.awayι_toSpecZero (grading R n) (coordinate R n)
      (MvPolynomial.isHomogeneous_X R (0 : Fin (n + 1))) (by decide))
  simpa only [Proj.awayι, standardChartIsoSpec, standardChartToBase,
    freeProjectivizationToBase, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, constants] using h

variable {R} {S : Type u} [CommRing S]

/-- Base change on the original Proj basic opens, via their native chart maps. -/
def standardChartMap (φ : R →+* S) : standardChart S n ⟶ standardChart R n :=
  (standardChartIsoSpec S n).hom ≫
    Spec.map (CommRingCat.ofHom (chartMap n φ)) ≫ (standardChartIsoSpec R n).inv

/-- The original `X₀ ≠ 0` chart is cartesian under any base-ring map. -/
theorem isPullback_standardChart (φ : R →+* S) :
    IsPullback (standardChartMap n φ) (standardChartToBase S n)
      (standardChartToBase R n) (Spec.map (CommRingCat.ofHom φ)) := by
  refine (isPullback_chartSpec n φ).of_iso
    (standardChartIsoSpec S n).symm (standardChartIsoSpec R n).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [standardChartMap]
  · simpa using (standardChartIsoSpec_inv_toBase S n).symm
  · simpa using (standardChartIsoSpec_inv_toBase R n).symm
  · simp

@[reassoc] theorem standardChartMap_toBase (φ : R →+* S) :
    standardChartMap n φ ≫ standardChartToBase R n =
      standardChartToBase S n ≫ Spec.map (CommRingCat.ofHom φ) :=
  (isPullback_standardChart n φ).w

/-- The same actual chart as an actual fiber product over the original base. -/
def standardChartBaseChangeIso (φ : R →+* S) :
    standardChart S n ≅
      pullback (standardChartToBase R n) (Spec.map (CommRingCat.ofHom φ)) :=
  (isPullback_standardChart n φ).isoPullback

@[reassoc (attr := simp)] theorem standardChartBaseChangeIso_hom_fst (φ : R →+* S) :
    (standardChartBaseChangeIso n φ).hom ≫ pullback.fst _ _ = standardChartMap n φ :=
  (isPullback_standardChart n φ).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem standardChartBaseChangeIso_hom_snd (φ : R →+* S) :
    (standardChartBaseChangeIso n φ).hom ≫ pullback.snd _ _ = standardChartToBase S n :=
  (isPullback_standardChart n φ).isoPullback_hom_snd

end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.standardChartIsoSpec_inv_toBase
#print axioms KltDP.Geometry.RelativeProjectiveChart.isPullback_standardChart
#print axioms KltDP.Geometry.RelativeProjectiveChart.standardChartBaseChangeIso
