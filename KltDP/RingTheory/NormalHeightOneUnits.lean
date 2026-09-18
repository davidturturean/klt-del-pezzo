import KltDP.RingTheory.NormalHartogs
import KltDP.Geometry.CartierLocalClass

/-!
# Zero height-one orders give an original normal-domain unit

The original DVR order criterion supplies actual units in each original
height-one localization. Their images and inverse images have literal
denominator witnesses, so normal Hartogs recovers a unit of the base ring.
-/

noncomputable section

universe u v w

namespace KltDP.RingTheory.NormalHartogs

open FactorialHartogs

section Localization

variable (R : Type u) [CommRing R] (K : Type v) [CommRing K] [Algebra R K]
  (P : Ideal R) [P.IsPrime] (S : Type w) [CommRing S] [Algebra R S]
  [IsLocalization.AtPrime S P] [Algebra S K] [IsScalarTower R S K]

/-- An original localization element has the original denominator witness in the algebra. -/
theorem memLocalizationAt_algebraMap (z : S) :
    MemLocalizationAt R K P (algebraMap S K z) := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj P.primeCompl z
  refine ⟨a, b, b.2, ?_⟩
  calc
    algebraMap R K (b : R) * algebraMap S K z =
        algebraMap S K (algebraMap R S (b : R) * z) := by
      rw [map_mul, ← IsScalarTower.algebraMap_apply]
    _ = algebraMap S K (algebraMap R S a) :=
      congrArg (algebraMap S K) ((mul_comm _ z).trans hab)
    _ = algebraMap R K a := (IsScalarTower.algebraMap_apply R S K a).symm

end Localization

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- Vanishing of the original DVR orders at every actual height-one
prime produces an original base-ring unit, without factoriality. -/
theorem exists_unit_of_affinePrincipalOrder_eq_zero (f : Kˣ)
    (hzero : ∀ p : AffineHeightOnePrime R, affinePrincipalOrder R K p f = 0) :
    ∃ a : Rˣ, Units.map (algebraMap R K).toMonoidHom a = f := by
  apply exists_unit_of_forall_heightOne R K f
  intro P hP hheight
  letI : P.IsPrime := hP
  let p : AffineHeightOnePrime R := ⟨⟨P, hP⟩, hheight⟩
  let S := Localization.AtPrime P
  letI : IsDiscreteValuationRing S := heightOneLocalization_isDiscreteValuationRing R p
  letI : Algebra S K := heightOneFractionFieldAlgebra R K p
  letI : IsScalarTower R S K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S K
      P.primeCompl (nonZeroDivisors R) P.primeCompl_le_nonZeroDivisors
  letI : IsFractionRing S K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl S K
  have horder : divisorOrder S K f = 0 := hzero p
  obtain ⟨a, ha⟩ := (divisorOrder_eq_zero_iff_exists_unit S K f).mp horder
  constructor
  · have hval : algebraMap S K (a : S) = (f : K) := congrArg Units.val ha
    exact (congrArg (MemLocalizationAt R K P) hval).mp
      (memLocalizationAt_algebraMap R K P S (a : S))
  · have hinv : Units.map (algebraMap S K).toMonoidHom a⁻¹ = f⁻¹ :=
      ((Units.map (algebraMap S K).toMonoidHom).map_inv a).trans
        (congrArg Inv.inv ha)
    have hval : algebraMap S K (↑a⁻¹ : S) = (↑f⁻¹ : K) := congrArg Units.val hinv
    exact (congrArg (MemLocalizationAt R K P) hval).mp
      (memLocalizationAt_algebraMap R K P S (↑a⁻¹ : S))

end KltDP.RingTheory.NormalHartogs
