import KltDP.Geometry.PrimeCurveIntersectionOneLength
import KltDP.Geometry.PrimeCurveCrossingCoefficient
import KltDP.Geometry.PrimeCurvePairingSupport

/-!
# Original curve ideals cross when the intersection number is at most one

The numerical intersection bound produces the original stalk-ideal sum.
The stalk-map transport is separated from the actual intersection-point
construction so the original scheme maps elaborate within default limits.
The crossing, local multiplicity, and equation ideals are all conclusions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.PrimeCurveIntersectionOneCrossing

private theorem kernel_sup_of_map_eq_maximalIdeal
    {R T : Type u} [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]
    (φ : R →+* T) [IsLocalHom φ] (hsurj : Function.Surjective φ)
    (J : Ideal R) (hJ : J.map φ = maximalIdeal T) :
    RingHom.ker φ ⊔ J = maximalIdeal R := by
  have h := congrArg (Ideal.comap φ) hJ
  rw [Ideal.comap_map_of_surjective φ hsurj, ← RingHom.ker_eq_comap_bot] at h
  have hcomap : (maximalIdeal T).comap φ = maximalIdeal R := by
    ext r
    change ¬ IsUnit (φ r) ↔ ¬ IsUnit r
    exact not_congr (isUnit_map_iff φ r)
  simpa only [hcomap, sup_comm] using h

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  (C D : X.PrimeCurve)

private theorem ideals_cross_of_restricted_span
    (y : C.toScheme) (U : X.toScheme.affineOpens) (hyU : C.inclusion.base y ∈ U.1)
    (c : RegularCartierEquationChart X.toScheme (X.primeCurveCartier hregular D))
    (hyc : y ∈ C.chartPreimage (X.primeCurveCartier hregular D) c)
    (hcoef : Ideal.span {C.toScheme.presheaf.germ
      (C.chartPreimage (X.primeCurveCartier hregular D) c) y hyc
      (C.restrictedCoefficient (X.primeCurveCartier hregular D) c)} =
      maximalIdeal (C.toScheme.presheaf.stalk y)) :
    (C.vanishingIdeal.ideal U).map
        (X.toScheme.presheaf.germ U.1 (C.inclusion.base y) hyU).hom ⊔
      (D.vanishingIdeal.ideal U).map
        (X.toScheme.presheaf.germ U.1 (C.inclusion.base y) hyU).hom =
      maximalIdeal (X.toScheme.presheaf.stalk (C.inclusion.base y)) := by
  let φ : X.toScheme.presheaf.stalk (C.inclusion.base y) →+*
      C.toScheme.presheaf.stalk y := (C.inclusion.stalkMap y).hom
  let J := (D.vanishingIdeal.ideal U).map
    (X.toScheme.presheaf.germ U.1 (C.inclusion.base y) hyU).hom
  have hmap : J.map φ = maximalIdeal (C.toScheme.presheaf.stalk y) := by
    dsimp only [J]
    rw [PrimeCurveCrossingCoefficient.vanishingIdeal_map_germ_eq_span_coefficient
      X hregular D U (C.inclusion.base y) hyU c hyc, Ideal.map_span, Set.image_singleton]
    have hg := Scheme.stalkMap_germ_apply C.inclusion c.chart.openSet y hyc c.coefficient
    exact (congrArg (fun a => Ideal.span ({a} : Set (C.toScheme.presheaf.stalk y))) hg).trans hcoef
  have hker : RingHom.ker φ = (C.vanishingIdeal.ideal U).map
      (X.toScheme.presheaf.germ U.1 (C.inclusion.base y) hyU).hom :=
    C.vanishingIdeal.stalkMap_gluedTo_ker_eq_map U hyU
  have h := kernel_sup_of_map_eq_maximalIdeal φ (C.inclusion.stalkMap_surjective y) J hmap
  rwa [hker] at h

/-- The original intersection bound forces the original ambient crossing
at every common point. Smoothness is needed only for the first curve. -/
theorem vanishingIdeal_sup_eq_maximalIdeal_of_intersection_le_one [IsSmooth C.toSpec]
    (hCD : C ≠ D) (hdegree : C.intersectionNumber (X.primeCurveCartier hregular D) ≤ 1)
    (y : C.toScheme) (hyD : C.inclusion.base y ∈ (D : Set X.toScheme))
    (U : X.toScheme.affineOpens) (hyU : C.inclusion.base y ∈ U.1) :
    (C.vanishingIdeal.ideal U).map
        (X.toScheme.presheaf.germ U.1 (C.inclusion.base y) hyU).hom ⊔
      (D.vanishingIdeal.ideal U).map
        (X.toScheme.presheaf.germ U.1 (C.inclusion.base y) hyU).hom =
      maximalIdeal (X.toScheme.presheaf.stalk (C.inclusion.base y)) := by
  let E := X.primeCurveCartier hregular D
  let hE := X.primeCurveCartier_hasRegularEquations hregular D
  let hC : C.NotInSupport E hE := X.notInSupport_of_ne hregular hCD
  have hyE : C.inclusion.base y ∈
      ((effectiveCartierIdealDataOfRegularEquations X.toScheme E hE).support :
        Set X.toScheme) := by
    simpa only [E, hE, X.primeCurveCartier_support hregular D] using hyD
  obtain ⟨z, rfl⟩ := C.exists_intersection_point_of_mem_support E hE hC y
    ((C.mem_support_restrictCartier_iff E hE hC y).mpr hyE)
  have hdegree' : C.intersectionDegree E hE hC ≤ 1 := by
    rw [C.intersectionNumber_eq_intersectionDegree E hE hC] at hdegree
    exact_mod_cast hdegree
  obtain ⟨c, hyc⟩ := C.exists_genericChart E hE ((C.intersectionInclusion E hE hC).base z)
  exact ideals_cross_of_restricted_span X hregular C D _ U hyU c.1 hyc
    (C.restrictedCoefficient_span_eq_maximalIdeal_of_degree_le_one E hE hC hdegree' z c hyc)

/-- The same original local crossing conclusion from the symmetric Cartier
pairing, so actual exceptional intersection bounds apply directly. -/
theorem vanishingIdeal_sup_eq_maximalIdeal_of_pairing_le_one [IsSmooth C.toSpec]
    (hCD : C ≠ D)
    (hdegree : X.intersectionPairing hregular (X.primeCurveCartier hregular C)
      (X.primeCurveCartier hregular D) ≤ 1)
    (y : C.toScheme) (hyD : C.inclusion.base y ∈ (D : Set X.toScheme))
    (U : X.toScheme.affineOpens) (hyU : C.inclusion.base y ∈ U.1) :
    (C.vanishingIdeal.ideal U).map
        (X.toScheme.presheaf.germ U.1 (C.inclusion.base y) hyU).hom ⊔
      (D.vanishingIdeal.ideal U).map
        (X.toScheme.presheaf.germ U.1 (C.inclusion.base y) hyU).hom =
      maximalIdeal (X.toScheme.presheaf.stalk (C.inclusion.base y)) := by
  rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber] at hdegree
  exact vanishingIdeal_sup_eq_maximalIdeal_of_intersection_le_one
    X hregular C D hCD hdegree y hyD U hyU

end KltDP.Geometry.PrimeCurveIntersectionOneCrossing

#print axioms KltDP.Geometry.PrimeCurveIntersectionOneCrossing.vanishingIdeal_sup_eq_maximalIdeal_of_intersection_le_one
