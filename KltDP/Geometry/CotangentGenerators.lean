import KltDP.Geometry.SingularPoints
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic

/-!
# Cotangent dimension and minimal generators

For a Noetherian local ring, a basis of the actual cotangent space lifts to
a generating family of its maximal ideal. Conversely, every such family
bounds the cotangent dimension. These statements identify the embedding
dimension with the least number of generators, without assuming a bound
on the ring's Krull dimension.
-/

noncomputable section

open IsLocalRing Submodule

namespace KltDP.Geometry

variable {R : Type*} [CommRing R] [IsLocalRing R]

omit [IsLocalRing R] in
/-- A family in an ideal generates that ideal exactly when it spans the
ideal regarded as a module. -/
theorem span_ideal_family_eq_iff {I : Ideal R} {ι : Type*} (v : ι → I) :
    Ideal.span (Set.range (fun i => (v i : R))) = I ↔
      Submodule.span R (Set.range v) = ⊤ := by
  rw [← (Submodule.map_injective_of_injective
    (Submodule.injective_subtype I)).eq_iff,
    Submodule.map_span, ← Set.range_comp', Submodule.map_top,
    Submodule.range_subtype]
  rfl

/-- Nakayama's lemma compares an actual maximal-ideal generating family
with its images in the cotangent space. -/
theorem maximal_generators_iff_cotangent_spans [IsNoetherianRing R]
    {ι : Type*} (v : ι → maximalIdeal R) :
    Ideal.span (Set.range (fun i => (v i : R))) = maximalIdeal R ↔
      Submodule.span (ResidueField R)
        (Set.range (fun i => (maximalIdeal R).toCotangent (v i))) = ⊤ := by
  rw [span_ideal_family_eq_iff,
    ← CotangentSpace.span_image_eq_top_iff, ← Set.range_comp']

/-- Every finite generating family bounds the embedding dimension. -/
theorem finrank_cotangentSpace_le_card_of_generators [IsNoetherianRing R]
    {ι : Type*} [Fintype ι] (v : ι → maximalIdeal R)
    (hv : Ideal.span (Set.range (fun i => (v i : R))) = maximalIdeal R) :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤ Fintype.card ι :=
  finrank_le_of_span_eq_top ((maximal_generators_iff_cotangent_spans v).mp hv)

/-- A cotangent basis has actual lifts generating the maximal ideal. -/
theorem exists_maximal_generators_finrank (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    ∃ v : Fin (Module.finrank (ResidueField R) (CotangentSpace R)) → maximalIdeal R,
      Ideal.span (Set.range (fun i => (v i : R))) = maximalIdeal R := by
  let b := Module.finBasis (ResidueField R) (CotangentSpace R)
  choose v hv using fun i => (maximalIdeal R).toCotangent_surjective (b i)
  refine ⟨v, (maximal_generators_iff_cotangent_spans v).mpr ?_⟩
  have heq : (fun i => (maximalIdeal R).toCotangent (v i)) = b := funext hv
  rw [heq]
  exact b.span_eq

/-- The cotangent dimension is the least cardinality of a finite generating
family of the actual maximal ideal. This includes the zero-dimensional
cotangent space of a field and its empty generating family. -/
theorem finrank_cotangentSpace_eq_iff_minimal_generators [IsNoetherianRing R]
    (d : ℕ) :
    Module.finrank (ResidueField R) (CotangentSpace R) = d ↔
      (∃ v : Fin d → maximalIdeal R,
        Ideal.span (Set.range (fun i => (v i : R))) = maximalIdeal R) ∧
      (∀ (n : ℕ) (v : Fin n → maximalIdeal R),
        Ideal.span (Set.range (fun i => (v i : R))) = maximalIdeal R → d ≤ n) := by
  constructor
  · rintro rfl
    refine ⟨exists_maximal_generators_finrank R, ?_⟩
    intro n v hv
    simpa using finrank_cotangentSpace_le_card_of_generators v hv
  · rintro ⟨⟨v, hv⟩, hminimal⟩
    apply le_antisymm
    · simpa using finrank_cotangentSpace_le_card_of_generators v hv
    · obtain ⟨w, hw⟩ := exists_maximal_generators_finrank R
      exact hminimal _ w hw

/-- A regular local ring has a maximal-ideal generating family of size equal
to its Krull dimension. This is the forward comparison with the generator
formulation of regularity; the converse additionally needs Krull's dimension
bound and is not asserted here. -/
theorem regularLocal_exists_dimension_generators (hR : RegularLocal R) :
    ∃ (d : ℕ) (v : Fin d → maximalIdeal R),
      ringKrullDim R = (d : WithBot ℕ∞) ∧
        Ideal.span (Set.range (fun i => (v i : R))) = maximalIdeal R := by
  letI : IsNoetherianRing R := hR.1
  obtain ⟨v, hv⟩ := exists_maximal_generators_finrank R
  exact ⟨_, v, hR.2, hv⟩

end KltDP.Geometry
