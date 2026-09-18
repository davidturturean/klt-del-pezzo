import KltDP.Geometry.ClosedPointVanishingIdeal
import KltDP.Geometry.PrincipalIdealNeighborhood
import KltDP.Geometry.ClosedPointDimension
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.KrullDimension.Field

/-! A regular closed point on the original integral algebraic curve has
an actual regular principal equation on an original affine neighborhood.
The stalk dimension comes from the original structure map; finite
generation spreads its maximal-ideal generator through the original germ. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry.RegularCurvePointEquation

variable {k : Type u} [Field k] [IsAlgClosed k]
  {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  (x : X) (hclosed : IsClosed ({x} : Set X))
  (hregular : RegularPoint X x) (hdim : topologicalKrullDim X = 1)

include f hregular hdim in
/-- A proved local equation for the original closed-point ideal. -/
theorem exists_regular_equation :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ d : Γ(X, U.1),
      (ClosedPointVanishingIdeal.ideal X x hclosed).ideal U = Ideal.span {d} ∧
      d ∈ nonZeroDivisors Γ(X, U.1) := by
  classical
  let U : X.affineOpens :=
    ⟨(X.affineCover.map x).opensRange, isAffineOpen_opensRange (X.affineCover.map x)⟩
  have hxU : x ∈ U.1 := X.affineCover.covers x
  let p := U.2.primeIdealOf ⟨x, hxU⟩
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_locallyOfFiniteType_toSpec f
  letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  letI : IsNoetherianRing (X.presheaf.stalk x) := hregular.1
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    U.2.isLocalization_stalk ⟨x, hxU⟩
  have hlocal : ringKrullDim (X.presheaf.stalk x) = 1 :=
    (closed_stalk_dimension_eq_global X f x hclosed).trans hdim
  have hfin : Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) = 1 := by
    exact_mod_cast hregular.2.symm.trans hlocal
  have hprincipal : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).IsPrincipal :=
    IsLocalRing.finrank_cotangentSpace_le_one_iff.mp hfin.le
  have hmne : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≠ ⊥ := by
    intro hm
    have hz := ringKrullDim_eq_zero_of_isField
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm)
    rw [hlocal] at hz
    exact one_ne_zero hz
  have hmap : p.asIdeal.map (algebraMap Γ(X, U.1) (X.presheaf.stalk x)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    calc
      _ = ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap
          (algebraMap Γ(X, U.1) (X.presheaf.stalk x))).map
          (algebraMap Γ(X, U.1) (X.presheaf.stalk x)) :=
        congrArg (Ideal.map (algebraMap Γ(X, U.1) (X.presheaf.stalk x)))
          (IsLocalization.AtPrime.comap_maximalIdeal
            (X.presheaf.stalk x) p.asIdeal inferInstance).symm
      _ = _ := IsLocalization.map_comap p.asIdeal.primeCompl (X.presheaf.stalk x) _
  letI : (p.asIdeal.map (algebraMap Γ(X, U.1) (X.presheaf.stalk x))).IsPrincipal :=
    hmap.symm ▸ hprincipal
  obtain ⟨d, hd, b, hb, hdspan, hden⟩ :=
    PrincipalIdealNeighborhood.exists_source_generator_denominator
      p.asIdeal.primeCompl (X.presheaf.stalk x) p.asIdeal (IsNoetherian.noetherian _)
  have hdg : algebraMap Γ(X, U.1) (X.presheaf.stalk x) d ≠ 0 := by
    intro hz
    exact hmne (hmap.symm.trans (hdspan.trans (Ideal.span_singleton_eq_bot.mpr hz)))
  have hxb : x ∈ X.basicOpen b := by
    apply (X.mem_basicOpen b x hxU).mpr
    exact IsLocalization.map_units (X.presheaf.stalk x) ⟨b, hb⟩
  let ρ := (X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom
  have heq : p.asIdeal.map ρ = Ideal.span {ρ d} :=
    PrincipalIdealNeighborhood.map_eq_span_of_unit_denominator ρ p.asIdeal d b hd
      (RingedSpace.isUnit_res_basicOpen X.toRingedSpace b) hden
  letI : IsDomain Γ(X, (X.affineBasicOpen b).1) :=
    @IsIntegral.component_integral X inferInstance (X.affineBasicOpen b).1 ⟨⟨x, hxb⟩⟩
  refine ⟨X.affineBasicOpen b, hxb, ρ d, ?_, mem_nonZeroDivisors_of_ne_zero ?_⟩
  · rw [← (ClosedPointVanishingIdeal.ideal X x hclosed).map_ideal_basicOpen U b,
      ClosedPointVanishingIdeal.ideal_eq_prime X x hclosed U hxU]
    exact heq
  · intro hz
    apply hdg
    change X.presheaf.germ U.1 x hxU d = 0
    rw [← X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le b)) x hxb d]
    change X.presheaf.germ (X.basicOpen b) x hxb (ρ d) = 0
    rw [hz, map_zero]

#print axioms exists_regular_equation

end KltDP.Geometry.RegularCurvePointEquation
