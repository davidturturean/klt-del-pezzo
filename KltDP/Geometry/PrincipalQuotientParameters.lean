import KltDP.Geometry.TransverseBranchesCotangentQuotient
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Lifting a parameter of a principal quotient

A generator of the target maximal ideal lifts through an actual surjective
local map. Together with the original kernel generator it generates the
source maximal ideal. In a regular local ring of dimension two, that
kernel generator consequently has nonzero cotangent class.
-/

noncomputable section

open IsLocalRing

universe u

namespace KltDP.Geometry.PrincipalQuotientParameters

variable {R T : Type u} [CommRing R] [CommRing T]
  [IsLocalRing R] [IsLocalRing T] (φ : R →+* T) [IsLocalHom φ]

/-- The actual kernel generator extends to two maximal-ideal generators
when the original local quotient has a principal maximal ideal. -/
theorem exists_companion [(maximalIdeal T).IsPrincipal]
    (hφ : Function.Surjective φ) (f : R) (hker : RingHom.ker φ = Ideal.span {f}) :
    ∃ g : R, Ideal.span {f, g} = maximalIdeal R := by
  obtain ⟨g, hg⟩ := hφ (Submodule.IsPrincipal.generator (maximalIdeal T))
  have hmap : (Ideal.span {g}).map φ = maximalIdeal T := by
    rw [Ideal.map_span, Set.image_singleton, hg]
    exact Ideal.span_singleton_generator _
  have hcomap : (maximalIdeal T).comap φ = maximalIdeal R := by
    ext r
    change ¬ IsUnit (φ r) ↔ ¬ IsUnit r
    exact not_congr (isUnit_map_iff φ r)
  refine ⟨g, ?_⟩
  calc
    Ideal.span {f, g} = Ideal.span {g} ⊔ RingHom.ker φ := by
      rw [hker, Ideal.span_insert, sup_comm]
    _ = ((Ideal.span {g}).map φ).comap φ :=
      (Ideal.comap_map_of_surjective' φ hφ (Ideal.span {g})).symm
    _ = maximalIdeal R := by rw [hmap, hcomap]

/-- Either element of a two-element generating system in a regular
dimension-two local ring is a regular parameter. This statement records
the first element's nonzero class in the actual cotangent space. -/
theorem first_not_mem_square (hR : RegularLocal R) (hdim : ringKrullDim R = 2)
    (f g : R) (hspan : Ideal.span {f, g} = maximalIdeal R) :
    f ∉ (maximalIdeal R) ^ 2 := by
  have hf : f ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hg : g ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  let w : Fin 2 → maximalIdeal R := ![⟨f, hf⟩, ⟨g, hg⟩]
  have hind := RationalTreePicard.linearIndependent_toCotangent_of_span_pair_eq
    (RationalTreePicard.finrank_cotangentSpace_eq_two_of_regularLocal hR hdim) w hspan
  intro hsq
  have hzero : (maximalIdeal R).toCotangent (w 0) = 0 :=
    (Ideal.toCotangent_eq_zero _ (w 0)).mpr hsq
  exact hind.ne_zero 0 hzero

end KltDP.Geometry.PrincipalQuotientParameters
