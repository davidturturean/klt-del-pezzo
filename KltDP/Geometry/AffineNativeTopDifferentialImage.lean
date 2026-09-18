import KltDP.Geometry.AffineNativeTopDifferentialFrame
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# The actual native differential factors through the original parameter ideal

The proved coefficient formula gives the exact image ideal. Regularity of
the original parameter proves injectivity and hence an equivalence onto that
actual ideal. The whole differential factors through its original inclusion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.AffineNativeTopDifferential

open AffineKaehlerTildeDerivation AffineTopDifferentialFrame

universe u

variable (k : Type u) [CommRing k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
variable (φ : A →ₐ[k] B)
variable (β : Basis (Fin 2) A (KaehlerDifferential k A))
variable (γ : Basis (Fin 2) B (KaehlerDifferential k B))
variable (a b : A) (t : B)
variable (hβ0 : β 0 = KaehlerDifferential.D k A a)
variable (hβ1 : β 1 = KaehlerDifferential.D k A b)
variable (hγ0 : γ 0 = KaehlerDifferential.D k B (φ a))
variable (hγ1 : γ 1 = KaehlerDifferential.D k B t)
variable (hrel : φ a * t = φ b)

include hβ0 hβ1 hγ0 hγ1 hrel in
/-- The coefficient of every actual differential image lies in the original ideal. -/
theorem framedMap_mem_span (ω : (ModuleCat.extendScalars φ.toRingHom).obj
    ((differentialModule k A).exteriorPower 2)) :
    framedMap k φ γ ω ∈ Ideal.span {φ a} := by
  rw [framedMap_apply k φ β γ a b t hβ0 hβ1 hγ0 hγ1 hrel]
  exact (Ideal.span {φ a}).mul_mem_left _
    (Ideal.subset_span (Set.mem_singleton _))

/-- Restrict the actual coefficient map to its actual image ideal. -/
def toParameterIdeal : (ModuleCat.extendScalars φ.toRingHom).obj
    ((differentialModule k A).exteriorPower 2) →ₗ[B] Ideal.span {φ a} :=
  LinearMap.codRestrict (Ideal.span {φ a}) (framedMap k φ γ)
    (framedMap_mem_span k φ β γ a b t hβ0 hβ1 hγ0 hγ1 hrel)

/-- Every element of the actual parameter ideal is an actual coefficient image. -/
theorem toParameterIdeal_surjective :
    Function.Surjective (toParameterIdeal k φ β γ a b t hβ0 hβ1 hγ0 hγ1 hrel) := by
  intro z
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp z.property
  refine ⟨(extendedFrame k φ β).symm c, ?_⟩
  apply Subtype.ext
  change framedMap k φ γ ((extendedFrame k φ β).symm c) = (z : B)
  rw [framedMap_apply k φ β γ a b t hβ0 hβ1 hγ0 hγ1 hrel,
    LinearEquiv.apply_symm_apply]
  exact hc

include hβ0 hβ1 hγ0 hγ1 hrel in
/-- The exact image of the original coefficient map is the actual principal ideal. -/
theorem framedMap_range : LinearMap.range (framedMap k φ γ) = Ideal.span {φ a} := by
  apply le_antisymm
  · rintro z ⟨ω, rfl⟩
    exact framedMap_mem_span k φ β γ a b t hβ0 hβ1 hγ0 hγ1 hrel ω
  · intro z hz
    obtain ⟨ω, hω⟩ := toParameterIdeal_surjective k φ β γ a b t hβ0 hβ1 hγ0 hγ1 hrel
      (⟨z, hz⟩ : Ideal.span {φ a})
    exact ⟨ω, congrArg Subtype.val hω⟩

variable (hregular : φ a ∈ nonZeroDivisors B)

include hβ0 hβ1 hγ0 hγ1 hrel hregular in
/-- The original parameter's regularity makes the actual coefficient map injective. -/
theorem framedMap_injective : Function.Injective (framedMap k φ γ) := by
  intro ω η h
  apply (extendedFrame k φ β).injective
  rw [framedMap_apply k φ β γ a b t hβ0 hβ1 hγ0 hγ1 hrel,
    framedMap_apply k φ β γ a b t hβ0 hβ1 hγ0 hγ1 hrel] at h
  exact (mul_cancel_right_mem_nonZeroDivisors hregular).mp h

/-- The original differential coefficient map identifies its source with the
actual parameter ideal; no image or injectivity hypothesis is supplied. -/
def parameterIdealEquiv : (ModuleCat.extendScalars φ.toRingHom).obj
    ((differentialModule k A).exteriorPower 2) ≃ₗ[B] Ideal.span {φ a} :=
  LinearEquiv.ofBijective (toParameterIdeal k φ β γ a b t hβ0 hβ1 hγ0 hγ1 hrel)
    ⟨fun _ _ h => framedMap_injective k φ β γ a b t hβ0 hβ1 hγ0 hγ1 hrel hregular
      (congrArg Subtype.val h),
      toParameterIdeal_surjective k φ β γ a b t hβ0 hβ1 hγ0 hγ1 hrel⟩

/-- Factor the whole original native differential through the original ideal inclusion. -/
theorem map_factor :
    (determinantEquiv γ).symm.toLinearMap.comp
      ((Ideal.span {φ a}).subtype.comp
        (parameterIdealEquiv k φ β γ a b t hβ0 hβ1 hγ0 hγ1 hrel hregular).toLinearMap) =
      (map k φ 2).hom := by
  apply LinearMap.ext
  intro ω
  change (determinantEquiv γ).symm (determinantEquiv γ (map k φ 2 ω)) = _
  exact (determinantEquiv γ).symm_apply_apply _

end KltDP.Geometry.AffineNativeTopDifferential
