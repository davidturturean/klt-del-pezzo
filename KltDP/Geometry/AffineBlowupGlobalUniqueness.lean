import KltDP.Geometry.AffineBlowupPrincipalTarget
import KltDP.Geometry.AffineBlowupCover
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Global uniqueness for admissible affine blowup test maps

Flat ring maps preserve nonzerodivisors by the pinned tensor-regularity
theorem. Thus an actual affine open immersion preserves the regular equation
of an admissible test map. Pulling back the actual Rees chart cover along an
arbitrary candidate morphism, then taking Mathlib's affine refinement, reduces
uniqueness to the proved agreement of actual chart presentations.

The result applies to every morphism from the affine test scheme, without
assuming that it factors through a chosen chart. The derived coefficient
cover then gives existence and uniqueness for any globally principal regular
target ideal. Non-affine test schemes and ideal-sheaf formulations remain
separate adapters; no universal-property conclusion is assumed as data.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.RingTheory

universe u v

/-- Flatness preserves an actual nonzerodivisor under the algebra map. -/
theorem algebraMap_mem_nonZeroDivisors_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] {r : R} (hr : r ∈ nonZeroDivisors R) :
    algebraMap R S r ∈ nonZeroDivisors S := by
  have hR : IsSMulRegular R r := by
    intro x y hxy
    exact (mul_cancel_left_mem_nonZeroDivisors hr).mp hxy
  have hS : IsSMulRegular S r :=
    ((TensorProduct.rid R S).isSMulRegular_congr r).mp (hR.lTensor S)
  intro x hx
  apply hS
  simpa only [Algebra.smul_def, mul_zero, zero_mul, mul_comm] using hx

/-- The same preservation theorem for an actual flat ring homomorphism. -/
theorem map_mem_nonZeroDivisors_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) {r : R} (hr : r ∈ nonZeroDivisors R) :
    f r ∈ nonZeroDivisors S := by
  letI : Algebra R S := f.toAlgebra
  letI : Module.Flat R S := hf
  exact algebraMap_mem_nonZeroDivisors_of_flat hr

end KltDP.RingTheory

namespace KltDP.Geometry.AffineBlowup

universe u v w

/-- A principal generation condition remains true after any target ring map. -/
theorem map_comp_le_span_singleton
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    (I : Ideal R) (a : I) (φ : R →+* S)
    (hI : Ideal.map φ I ≤ Ideal.span {φ (a : R)}) (ρ : S →+* T) :
    Ideal.map (ρ.comp φ) I ≤ Ideal.span {(ρ.comp φ) (a : R)} := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr
  change ρ (φ r) ∈ Ideal.span {ρ (φ (a : R))}
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp (hI (Ideal.mem_map_of_mem φ hr))
  apply Ideal.mem_span_singleton.mpr
  exact ⟨ρ s, by rw [hs, map_mul]⟩

/-- An actual affine open immersion preserves a regular base equation. -/
theorem openImmersionSpecPreimage_mem_nonZeroDivisors
    {S T : Type u} [CommRing S] [CommRing T]
    (j : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) [IsOpenImmersion j]
    {r : S} (hr : r ∈ nonZeroDivisors S) :
    (Spec.preimage j).hom r ∈ nonZeroDivisors T := by
  have hj : (Spec.preimage j).hom.Flat := by
    apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)
      (φ := Spec.preimage j)).mp
    rw [Spec.map_preimage]
    infer_instance
  exact KltDP.RingTheory.map_mem_nonZeroDivisors_of_flat _ hj hr

variable {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (a : I) (φ : R →+* S)
    (hreg : φ (a : R) ∈ nonZeroDivisors S)
    (hI : Ideal.map φ I ≤ Ideal.span {φ (a : R)})

/-- Every candidate morphism over an admissible affine test map agrees with
the canonical lift. Its local chart presentations are constructed from the
actual pulled-back Rees cover, rather than assumed. -/
theorem affineLift_unique (j : Spec (CommRingCat.of S) ⟶ scheme I)
    (hj : j ≫ toSpec I = Spec.map (CommRingCat.ofHom φ)) :
    j = affineLift I a φ hreg hI := by
  let 𝒱 := (degreeOneAffineCover I).openCover
  let 𝒲 : (Spec (CommRingCat.of S)).OpenCover := 𝒱.pullbackCover j
  let 𝒰 := Scheme.OpenCover.affineRefinement 𝒲
  let η : 𝒰.openCover ⟶ 𝒲 := Scheme.OpenCover.fromAffineRefinement 𝒲
  apply 𝒰.openCover.hom_ext
  intro i
  change 𝒰.map i ≫ j = 𝒰.map i ≫ affineLift I a φ hreg hI
  let b : I := η.idx i
  let α := 𝒰.map i
  let γ := η.app i ≫ 𝒱.pullbackHom j b
  have hη : η.app i ≫ 𝒲.map b = α := η.w i
  have hγ : γ ≫ chartι I b = α ≫ j := by
    change (η.app i ≫ 𝒱.pullbackHom j b) ≫ 𝒱.map b = α ≫ j
    rw [Category.assoc, Scheme.Cover.pullbackHom_map, ← Category.assoc, hη]
  let ρ := (Spec.preimage α).hom
  let ψ := (Spec.preimage γ).hom
  have hρreg : (ρ.comp φ) (a : R) ∈ nonZeroDivisors (𝒰.obj i) :=
    openImmersionSpecPreimage_mem_nonZeroDivisors α hreg
  have hρI : Ideal.map (ρ.comp φ) I ≤ Ideal.span {(ρ.comp φ) (a : R)} :=
    map_comp_le_span_singleton I a φ hI ρ
  have hψ : ψ.comp (chartBaseMap I b) = ρ.comp φ := by
    have hcat : CommRingCat.ofHom (chartBaseMap I b) ≫ Spec.preimage γ =
        CommRingCat.ofHom φ ≫ Spec.preimage α := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
      have hchart : chartι I b ≫ toSpec I =
          Spec.map (CommRingCat.ofHom (chartBaseMap I b)) := chartι_toSpec I b
      rw [← hchart, ← Category.assoc, hγ, Category.assoc, hj]
    exact congrArg CommRingCat.Hom.hom hcat
  have hχ : (ρ.comp (chartLift I a φ hreg hI)).comp (chartBaseMap I a) = ρ.comp φ := by
    ext r
    change ρ (chartLift I a φ hreg hI (chartBaseMap I a r)) = ρ (φ r)
    rw [chartLift_baseMap]
  have he := chartMap_hom_ext I a (ρ.comp φ) hρreg hρI b a
    ψ (ρ.comp (chartLift I a φ hreg hI)) hψ hχ
  calc
    α ≫ j = γ ≫ chartι I b := hγ.symm
    _ = Spec.map (CommRingCat.ofHom ψ) ≫ chartι I b :=
      congrArg (fun f => f ≫ chartι I b) (Spec.map_preimage γ).symm
    _ = Spec.map (CommRingCat.ofHom (ρ.comp (chartLift I a φ hreg hI))) ≫
        chartι I a := he
    _ = α ≫ affineLift I a φ hreg hI := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      change Spec.map (Spec.preimage α) ≫ affineLift I a φ hreg hI = _
      rw [Spec.map_preimage]

section PrincipalTarget

variable (d : S) (hcenter : Ideal.map φ I = Ideal.span {d})
    (hregular : d ∈ nonZeroDivisors S)

/-- Uniqueness among all global candidate maps from an affine test scheme
whose extended center has an arbitrary principal regular equation. -/
theorem principalTargetLift_unique (j : Spec (CommRingCat.of S) ⟶ scheme I)
    (hj : j ≫ toSpec I = Spec.map (CommRingCat.ofHom φ)) :
    j = principalTargetLift I φ d hcenter hregular := by
  let 𝒰 := principalCoefficientCover I φ d hcenter hregular
  apply 𝒰.openCover.hom_ext
  intro b
  have hlocal : (𝒰.map b ≫ j) ≫ toSpec I =
      Spec.map (CommRingCat.ofHom (principalCoefficientMap I φ d hcenter b)) := by
    rw [Category.assoc, hj, principalCoefficientCover_map,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have h := affineLift_unique I b (principalCoefficientMap I φ d hcenter b)
    (principalCoefficientMap_equation_regular I φ d hcenter hregular b)
    (principalCoefficientMap_ideal_le I φ d hcenter b) (𝒰.map b ≫ j) hlocal
  change 𝒰.map b ≫ j = 𝒰.map b ≫ principalTargetLift I φ d hcenter hregular
  rw [principalTargetLift_restrict]
  exact h

include d hcenter hregular in
/-- The actual affine Rees Proj satisfies existence and uniqueness for every
affine test map whose extended center is principal with a nonzerodivisor equation. -/
theorem existsUnique_lift_of_principal_regular :
    ∃! j : Spec (CommRingCat.of S) ⟶ scheme I,
      j ≫ toSpec I = Spec.map (CommRingCat.ofHom φ) :=
  ⟨principalTargetLift I φ d hcenter hregular,
    principalTargetLift_toSpec I φ d hcenter hregular,
    fun j hj => principalTargetLift_unique I φ d hcenter hregular j hj⟩

end PrincipalTarget

end KltDP.Geometry.AffineBlowup
