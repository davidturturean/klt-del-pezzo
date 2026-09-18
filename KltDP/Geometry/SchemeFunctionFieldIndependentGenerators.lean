import KltDP.Geometry.AffineSectionsFunctionField
import KltDP.Geometry.PolynomialEmbeddingDimensionBound
import KltDP.Geometry.Positivity
import KltDP.Topology.DimensionOpenCover
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# Independent original rational functions of sufficient cardinality

Apply pinned Noether normalization to the actual algebra of an affine
open, and inject its polynomial algebra into the original function field.
The proved open-cover dimension bound ensures that at least one original
chart supplies as many independent functions as the original dimension.
No assertion identifying transcendence degree and dimension is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.BirationalSectionGrowth

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- A finite upper bound on the actual dimension bounds its natural value. -/
theorem natDim_le_of_topologicalKrullDim_le (X : Scheme.{u}) {d : ℕ}
    (h : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    Positivity.natDim X ≤ d := by
  apply ENat.toNat_le_of_le_coe
  exact (WithBot.unbotD_le_iff (fun _ => bot_le)).mpr h

/-- A cover with natural bounds has a member whose bound reaches the
actual natural dimension. Finiteness of the cover is not required. -/
theorem exists_cover_bound_ge_natDim (X : Scheme.{u}) [Nonempty X]
    {ι : Type*} (U : ι → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (d : ι → ℕ)
    (hbound : ∀ i, topologicalKrullDim (U i) ≤ (d i : WithBot ℕ∞)) :
    ∃ i, Positivity.natDim X ≤ d i := by
  by_contra! h
  obtain ⟨i, _⟩ := hcover (Classical.choice (inferInstance : Nonempty X))
  have hpos : 0 < Positivity.natDim X := (Nat.zero_le (d i)).trans_lt (h i)
  have hdim : topologicalKrullDim X ≤
      ((Positivity.natDim X - 1 : ℕ) : WithBot ℕ∞) := by
    apply KltDP.Topology.topologicalKrullDim_le_of_open_cover U hcover
    intro j
    have hj : d j ≤ Positivity.natDim X - 1 := by have := h j; omega
    exact (hbound j).trans (by exact_mod_cast hj)
  have := natDim_le_of_topologicalKrullDim_le X hdim
  omega

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]

/-- Noether normalization on an actual nonempty affine open yields
independent elements of the same original function field and base field. -/
theorem exists_affine_independent_functions {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] :
    letI := SectionMonomialGrowth.functionFieldAlgebra f
    ∃ (d : ℕ) (z : Fin d → X.functionField),
      AlgebraicIndependent k z ∧ ringKrullDim Γ(X, U) ≤ (d : WithBot ℕ∞) := by
  letI := affineSectionsAlgebra f hU
  letI := affineSectionsAlgebra_finiteType f hU
  letI := SectionMonomialGrowth.functionFieldAlgebra f
  obtain ⟨d, g, hg, hdim⟩ :=
    PolynomialEmbeddingDimensionBound.exists_embedding k Γ(X, U)
  let G : MvPolynomial (Fin d) k →ₐ[k] X.functionField :=
    (affineSectionsToFunctionField f hU).comp g
  refine ⟨d, G ∘ MvPolynomial.X, ?_, hdim⟩
  apply algebraicIndependent_iff_injective_aeval.mpr
  rw [← MvPolynomial.aeval_unique G]
  exact (affineSectionsToFunctionField_injective f hU).comp hg

/-- At least the original dimension many algebraically independent
rational functions exist over the original field. This is the precise
cardinality input for the original section-growth construction. -/
theorem exists_independent_functions_of_natDim_pos (hdim : 0 < Positivity.natDim X) :
    letI := SectionMonomialGrowth.functionFieldAlgebra f
    ∃ (d : ℕ) (z : Fin d → X.functionField),
      0 < d ∧ Positivity.natDim X ≤ d ∧ AlgebraicIndependent k z := by
  letI := SectionMonomialGrowth.functionFieldAlgebra f
  let U : X → X.Opens := fun x => (X.affineCover.map x).opensRange
  have hU (x : X) : IsAffineOpen (U x) :=
    isAffineOpen_opensRange (X.affineCover.map x)
  have hdata (x : X) : ∃ (d : ℕ) (z : Fin d → X.functionField),
      AlgebraicIndependent k z ∧ ringKrullDim Γ(X, U x) ≤ (d : WithBot ℕ∞) := by
    letI : Nonempty (U x) := ⟨⟨x, X.affineCover.covers x⟩⟩
    exact exists_affine_independent_functions f (hU x)
  choose d z hz hd using hdata
  have hcover : ∀ x : X, ∃ i, x ∈ U i := fun x => ⟨x, X.affineCover.covers x⟩
  have hbound (x : X) : topologicalKrullDim (U x) ≤ (d x : WithBot ℕ∞) := by
    calc
      _ = topologicalKrullDim (Spec Γ(X, U x)) :=
        IsHomeomorph.topologicalKrullDim_eq (hU x).isoSpec.schemeIsoToHomeo
          (hU x).isoSpec.schemeIsoToHomeo.isHomeomorph
      _ = ringKrullDim Γ(X, U x) :=
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U x)
      _ ≤ d x := hd x
  obtain ⟨x, hx⟩ := exists_cover_bound_ge_natDim X U hcover d hbound
  exact ⟨d x, z x, hdim.trans_le hx, hx, hz x⟩

end KltDP.Geometry.BirationalSectionGrowth
