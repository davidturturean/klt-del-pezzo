import KltDP.Geometry.ContractionPicardUnimodular
import KltDP.Geometry.SurfaceNumericalFinitenessProved

/-!
# The original Picard group of a surface with unimodular intersection form

The existing numerical quotient kills exactly the classes which pair to zero.
Injectivity of the original intersection map to the integral dual therefore
makes the quotient map an actual linear equivalence. The already proved
finite freeness of integral numerical classes transfers to the original Picard
group through this same map.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)

/-- The original additive integral-dual bijection is the original linear-dual
bijection, using the canonical integer module structure. -/
theorem integralPicardIntersectionBilinForm_bijective_of_picardUnimodular
    (hU : S.PicardUnimodular hS) :
    Function.Bijective (S.integralPicardIntersectionBilinForm hS) := by
  have hAdd := (S.picardUnimodular_iff_bilinForm hS).mp hU
  constructor
  · intro p q hpq
    apply hAdd.1
    exact congrArg
      (fun l : Additive S.toScheme.Pic →ₗ[ℤ] ℤ => l.toAddMonoidHom) hpq
  · intro l
    obtain ⟨p, hp⟩ := hAdd.2 l.toAddMonoidHom
    refine ⟨p, ?_⟩
    apply LinearMap.ext
    intro q
    exact DFunLike.congr_fun hp q

/-- No original Picard class is lost by the integral numerical quotient when
the original intersection form is unimodular. -/
theorem picardIntegralNumericalMap_eq_zero_iff_of_picardUnimodular
    (hU : S.PicardUnimodular hS) (p : Additive S.toScheme.Pic) :
    S.picardIntegralNumericalMap p = 0 ↔ p = 0 := by
  refine ⟨fun hp => ?_, fun hp => by rw [hp, map_zero]⟩
  have hnum := (S.picardIntegralNumericalMap_eq_zero_iff p).mp hp
  apply (S.integralPicardIntersectionBilinForm_bijective_of_picardUnimodular hS hU).1
  apply LinearMap.ext
  intro q
  have hz : S.integralPicardIntersectionBilinForm hS p q = 0 := by
    rw [integralPicardIntersectionBilinForm_apply,
      S.picardPairing_symm hS p.toMul q.toMul]
    exact S.picardPairing_eq_zero_of_numericallyTrivial hS q.toMul p.toMul hnum
  simpa only [map_zero, LinearMap.zero_apply] using hz

theorem picardIntegralNumericalMap_injective_of_picardUnimodular
    (hU : S.PicardUnimodular hS) :
    Function.Injective S.picardIntegralNumericalMap := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply (S.picardIntegralNumericalMap_eq_zero_iff_of_picardUnimodular hS hU (p - q)).mp
  rw [map_sub, hpq, sub_self]

/-- The equivalence is the original quotient map, with its inverse supplied
by the just-proved injectivity and existing quotient surjectivity. -/
def picardIntegralNumericalEquiv_of_picardUnimodular
    (hU : S.PicardUnimodular hS) :
    Additive S.toScheme.Pic ≃ₗ[ℤ] S.IntegralNumericalClassGroup :=
  LinearEquiv.ofBijective S.picardIntegralNumericalMap
    ⟨S.picardIntegralNumericalMap_injective_of_picardUnimodular hS hU,
      S.picardIntegralNumericalMap_surjective⟩

@[simp]
theorem picardIntegralNumericalEquiv_of_picardUnimodular_apply
    (hU : S.PicardUnimodular hS) (p : Additive S.toScheme.Pic) :
    S.picardIntegralNumericalEquiv_of_picardUnimodular hS hU p =
      S.picardIntegralNumericalMap p := rfl

/-- Finite freeness belongs to the original integral Picard group. -/
theorem picard_free_and_finite_of_picardUnimodular
    (hU : S.PicardUnimodular hS) :
    Module.Free ℤ (Additive S.toScheme.Pic) ∧
      Module.Finite ℤ (Additive S.toScheme.Pic) := by
  letI : Module.Free ℤ S.IntegralNumericalClassGroup :=
    SurfaceNumericalFinitenessProved.integralNum_free S hS
  letI : Module.Finite ℤ S.IntegralNumericalClassGroup :=
    SurfaceNumericalFinitenessProved.integralNum_finite S hS
  let e := S.picardIntegralNumericalEquiv_of_picardUnimodular hS hU
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.picardIntegralNumericalEquiv_of_picardUnimodular
#print axioms KltDP.Geometry.NormalProjectiveSurface.picardIntegralNumericalEquiv_of_picardUnimodular
#check @KltDP.Geometry.NormalProjectiveSurface.picard_free_and_finite_of_picardUnimodular
#print axioms KltDP.Geometry.NormalProjectiveSurface.picard_free_and_finite_of_picardUnimodular
