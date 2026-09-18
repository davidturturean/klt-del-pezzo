import KltDP.Geometry.EffectiveWeilPrimeSupport

/-! Zero intersection of effective original members without a common prime
forces their actual closed supports to be disjoint. The finite coefficient
sums and the original prime-curve intersection schemes prove this directly. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
open scoped BigOperators
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Every original prime component has zero degree against the other member.
No intersection contribution can cancel, since the members are effective
and have no common prime component. -/
theorem effectivePair_component_degree_zero (D E : X.WeilDivisor)
    (hD : EffectiveDivisor D) (hE : EffectiveDivisor E)
    (hdisj : Disjoint D.support E.support)
    (hzero : X.intersectionPairing hX
      ((X.regularCartierWeilEquiv hX).symm D)
      ((X.regularCartierWeilEquiv hX).symm E) = 0)
    (C : X.PrimeCurve) (hC : C ∈ D.support) :
    C.intersectionNumber ((X.regularCartierWeilEquiv hX).symm E) = 0 := by
  classical
  have hmap : X.cartierToWeilHom ((X.regularCartierWeilEquiv hX).symm D) = D :=
    (X.regularCartierWeilEquiv hX).apply_symm_apply D
  rw [X.intersectionPairing_eq_weil_sum_right hX, hmap] at hzero
  change (∑ P ∈ D.support,
    D P * P.intersectionNumber ((X.regularCartierWeilEquiv hX).symm E)) = 0 at hzero
  have hnonneg (P : X.PrimeCurve) (hP : P ∈ D.support) :
      0 ≤ D P * P.intersectionNumber ((X.regularCartierWeilEquiv hX).symm E) := by
    apply mul_nonneg (hD P)
    rw [← X.intersectionPairing_primeCurve hX]
    exact EffectiveWeilPrimeSupport.intersection_nonneg_of_not_mem_support X hX E hE P
      (fun h => Finset.disjoint_left.mp hdisj hP h)
  have hm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero C hC
  exact (mul_eq_zero.mp hm).resolve_left (Finsupp.mem_support_iff.mp hC)

/-- The actual geometric supports are disjoint, rather than only their
finite sets of prime components. -/
theorem effectivePair_disjoint_divisorSupport (D E : X.WeilDivisor)
    (hD : EffectiveDivisor D) (hE : EffectiveDivisor E)
    (hdisj : Disjoint D.support E.support)
    (hzero : X.intersectionPairing hX
      ((X.regularCartierWeilEquiv hX).symm D)
      ((X.regularCartierWeilEquiv hX).symm E) = 0) :
    Disjoint (divisorSupport D) (divisorSupport E) := by
  classical
  apply Set.disjoint_left.mpr
  intro x hxD hxE
  obtain ⟨C, hC, hxC⟩ := (mem_divisorSupport D x).mp hxD
  obtain ⟨P, hP, hxP⟩ := (mem_divisorSupport E x).mp hxE
  have hCs : C ∈ D.support := Finsupp.mem_support_iff.mpr hC
  have hPs : P ∈ E.support := Finsupp.mem_support_iff.mpr hP
  have hne (Q : X.PrimeCurve) (hQ : Q ∈ E.support) : C ≠ Q := by
    intro h
    exact Finset.disjoint_left.mp hdisj hCs (h.symm ▸ hQ)
  have hz := X.effectivePair_component_degree_zero hX D E hD hE hdisj hzero C hCs
  have hmap : X.cartierToWeilHom ((X.regularCartierWeilEquiv hX).symm E) = E :=
    (X.regularCartierWeilEquiv hX).apply_symm_apply E
  rw [X.intersectionNumber_eq_weil_sum hX C, hmap] at hz
  change (∑ Q ∈ E.support, E Q * X.primeCurveMatrix hX C Q) = 0 at hz
  have hnonneg (Q : X.PrimeCurve) (hQ : Q ∈ E.support) :
      0 ≤ E Q * X.primeCurveMatrix hX C Q := by
    apply mul_nonneg (hE Q)
    change 0 ≤ C.intersectionNumber (X.primeCurveCartier hX Q)
    rw [← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber
      X hX C Q]
    exact PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg X hX C Q (hne Q hQ)
  have hm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz P hPs
  have hp : X.primeCurveMatrix hX C P = 0 := (mul_eq_zero.mp hm).resolve_left hP
  have hpair : X.intersectionPairing hX (X.primeCurveCartier hX C)
      (X.primeCurveCartier hX P) = 0 := by
    rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber X hX C P]
    exact hp
  exact Set.disjoint_left.mp
    ((PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
      X hX C P (hne P hPs)).mp hpair) hxC hxP

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.effectivePair_disjoint_divisorSupport
#print axioms KltDP.Geometry.NormalProjectiveSurface.effectivePair_disjoint_divisorSupport
