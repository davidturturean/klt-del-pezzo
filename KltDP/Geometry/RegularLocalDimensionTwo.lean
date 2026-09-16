import KltDP.Geometry.CotangentGenerators
import KltDP.Geometry.SingularClosed

/-!
# Generator regularity for local domains of dimension at most two

For a Noetherian local domain of Krull dimension at most two, the Krull
dimension is bounded by the cotangent dimension. Cotangent rank zero gives
a field. Cotangent rank at most one gives a principal ideal domain through
the proved DVR characterizations. In the remaining case the cotangent rank
is at least two, which already bounds the ring dimension.

This proves the converse to the generator formulation of regularity needed
at actual normal-surface stalks. It does not assert the general-dimensional
Krull height theorem and does not assume any regular-locus openness result.
-/

noncomputable section

open IsLocalRing AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry

/-- The generator definition of a regular local ring: the actual maximal
ideal has a generating family whose size is the actual Krull dimension.
The subtype records that every generator belongs to the maximal ideal. -/
def RegularLocalByGenerators (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧
    ∃ (d : ℕ) (v : Fin d → maximalIdeal R),
      ringKrullDim R = (d : WithBot ℕ∞) ∧
        Ideal.span (Set.range (fun i => (v i : R))) = maximalIdeal R

/-- The project's cotangent definition implies the generator definition
without a dimension or domain assumption. -/
theorem regularLocalByGenerators_of_regularLocal {R : Type u}
    [CommRing R] [IsLocalRing R] (hR : RegularLocal R) :
    RegularLocalByGenerators R :=
  ⟨hR.1, regularLocal_exists_dimension_generators hR⟩

/-- Cotangent rank at most one bounds the Krull dimension of a Noetherian
local domain by one, using the proved prime-ideal characterization of DVRs. -/
theorem ringKrullDim_le_one_of_finrank_cotangentSpace_le_one
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    (hrank : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1) :
    ringKrullDim R ≤ 1 := by
  have hprime :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 5 3).mp hrank
  letI : Ring.KrullDimLE 1 R := Ring.KrullDimLE.mk₁' fun I hI hIP ↦ by
    rw [hprime.2 I hI hIP]
    exact maximalIdeal.isMaximal R
  exact Order.KrullDimLE.krullDim_le (n := 1) (α := PrimeSpectrum R)

/-- Krull dimension is at most the embedding dimension for Noetherian
local domains of Krull dimension at most two. -/
theorem ringKrullDim_le_finrank_cotangentSpace_of_le_two
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    (hdim : ringKrullDim R ≤ 2) :
    ringKrullDim R ≤
      (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) := by
  by_cases hzero : Module.finrank (ResidueField R) (CotangentSpace R) = 0
  · have hfield : IsField R := finrank_cotangentSpace_eq_zero_iff.mp hzero
    rw [hzero, ringKrullDim_eq_zero_of_isField hfield]
    exact le_rfl
  by_cases hone : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1
  · have hrank : Module.finrank (ResidueField R) (CotangentSpace R) = 1 :=
      Nat.le_antisymm hone (Nat.one_le_iff_ne_zero.mpr hzero)
    simpa only [hrank, Nat.cast_one] using
      ringKrullDim_le_one_of_finrank_cotangentSpace_le_one R hone
  · have htwo : 2 ≤ Module.finrank (ResidueField R) (CotangentSpace R) := by omega
    apply hdim.trans
    exact_mod_cast htwo

/-- On a local domain of dimension at most two, the literal generator
condition gives the project's cotangent-space regularity condition. -/
theorem regularLocal_of_generators_of_dimension_le_two
    {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
    (hdim : ringKrullDim R ≤ 2) (hR : RegularLocalByGenerators R) :
    RegularLocal R := by
  letI : IsNoetherianRing R := hR.1
  obtain ⟨d, v, hdim_eq, hv⟩ := hR.2
  have hrank_le : Module.finrank (ResidueField R) (CotangentSpace R) ≤ d := by
    simpa only [Fintype.card_fin] using finrank_cotangentSpace_le_card_of_generators v hv
  refine ⟨inferInstance, le_antisymm
    (ringKrullDim_le_finrank_cotangentSpace_of_le_two R hdim) ?_⟩
  rw [hdim_eq]
  exact_mod_cast hrank_le

/-- Equivalence of the source generator formulation and the project
cotangent formulation for local domains of dimension at most two. -/
theorem regularLocalByGenerators_iff_regularLocal_of_dimension_le_two
    {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
    (hdim : ringKrullDim R ≤ 2) :
    RegularLocalByGenerators R ↔ RegularLocal R :=
  ⟨regularLocal_of_generators_of_dimension_le_two hdim,
    regularLocalByGenerators_of_regularLocal⟩

/-- The Krull dimension of an actual scheme stalk is at most the ambient
topological Krull dimension. The proof uses its affine localization. -/
theorem ringKrullDim_stalk_le_topologicalKrullDim (X : Scheme.{u}) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  let U : X.Opens := (X.affineCover.map x).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.map x)
  let xu : U := ⟨x, X.affineCover.covers x⟩
  let p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf xu
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk xu
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk xu
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk x)]
  exact (Ideal.height_le_ringKrullDim_of_ne_top p.isPrime.ne_top).trans
    (ringKrullDim_sections_le_topologicalKrullDim X U hU)

/-- The source and project regularity predicates agree at every actual
stalk of a normal projective surface. -/
theorem normalSurface_regularLocalByGenerators_iff {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (x : X.Point) :
    RegularLocalByGenerators (X.stalk x) ↔ RegularPoint X.toScheme x :=
  regularLocalByGenerators_iff_regularLocal_of_dimension_le_two
    ((ringKrullDim_stalk_le_topologicalKrullDim X.toScheme x).trans_eq X.dimension_two)

end KltDP.Geometry
