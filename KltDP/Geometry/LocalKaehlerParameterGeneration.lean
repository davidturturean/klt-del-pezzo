import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.LocalRing.Module

/-!
# Differentials of actual local parameters generate the Kähler module

The existing conormal exact sequence first gives generation on the residue
fiber. Nakayama then lifts it to the original finite Kähler module.
Surjectivity of the ground-field scalar map onto the residue field is used
explicitly, so the conclusion concerns that same algebra structure.
-/

noncomputable section

open scoped TensorProduct
open IsLocalRing

namespace KltDP.Geometry.LocalKaehlerParameterGeneration

section Quotient

variable (k A B : Type*) [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]

/-- If the quotient has no relative differentials, the original kernel
differentials surject onto the base-changed Kähler module. -/
theorem kerToTensor_surjective
    (hAB : Function.Surjective (algebraMap A B))
    (hkB : Function.Surjective (algebraMap k B)) :
    Function.Surjective (KaehlerDifferential.kerToTensor k A B) := by
  letI : Subsingleton (KaehlerDifferential k B) :=
    KaehlerDifferential.subsingleton_of_surjective k B hkB
  have hcot : Function.Surjective (KaehlerDifferential.kerCotangentToTensor k A B) := by
    rw [← LinearMap.range_eq_top, KaehlerDifferential.range_kerCotangentToTensor k A B hAB]
    apply top_unique
    intro x _
    exact Subsingleton.elim _ _
  intro x
  obtain ⟨c, hc⟩ := hcot x
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ c
  exact ⟨a, hc⟩

/-- The differentials of the given kernel generators span the original fiber. -/
theorem kernelDifferentials_span {ι : Type*}
    (v : ι → RingHom.ker (algebraMap A B))
    (hv : Ideal.span (Set.range (fun i => (v i : A))) = RingHom.ker (algebraMap A B))
    (hAB : Function.Surjective (algebraMap A B))
    (hkB : Function.Surjective (algebraMap k B)) :
    Submodule.span A (Set.range (fun i => (1 : B) ⊗ₜ[A] KaehlerDifferential.D k A (v i))) = ⊤ := by
  have hmodule : Submodule.span A (Set.range v) = ⊤ := by
    apply (Submodule.map_injective_of_injective
      (Submodule.injective_subtype (RingHom.ker (algebraMap A B)))).eq_iff.mp
    rw [Submodule.map_span, ← Set.range_comp', Submodule.map_top, Submodule.range_subtype]
    exact hv
  have h := congrArg (Submodule.map (KaehlerDifferential.kerToTensor k A B)) hmodule
  rw [Submodule.map_span, ← Set.range_comp', Submodule.map_top,
    LinearMap.range_eq_top.mpr (kerToTensor_surjective k A B hAB hkB)] at h
  exact h

end Quotient

variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]

/-- At a local algebra with the original residue scalars surjective, actual
maximal-ideal generators give generators of its finite native Kähler module. -/
theorem span_derivatives [Module.Finite A (KaehlerDifferential k A)]
    {ι : Type*} (v : ι → maximalIdeal A)
    (hv : Ideal.span (Set.range (fun i => (v i : A))) = maximalIdeal A)
    (hscalar : Function.Surjective (algebraMap k (ResidueField A))) :
    Submodule.span A (Set.range (fun i => KaehlerDifferential.D k A (v i))) = ⊤ := by
  have hker : RingHom.ker (algebraMap A (ResidueField A)) = maximalIdeal A := by
    rw [ResidueField.algebraMap_eq, ker_residue]
  let w : ι → RingHom.ker (algebraMap A (ResidueField A)) :=
    fun i => ⟨v i, by rw [hker]; exact (v i).property⟩
  have hw : Ideal.span (Set.range (fun i => (w i : A))) =
      RingHom.ker (algebraMap A (ResidueField A)) := hv.trans hker.symm
  have hresidue : Function.Surjective (algebraMap A (ResidueField A)) := residue_surjective
  have hfiber := kernelDifferentials_span k A (ResidueField A) w hw hresidue hscalar
  apply IsLocalRing.map_tensorProduct_mk_eq_top.mp
  rw [Submodule.map_span, ← Set.range_comp']
  exact hfiber

end KltDP.Geometry.LocalKaehlerParameterGeneration
