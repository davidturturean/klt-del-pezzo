import KltDP.Geometry.FiniteTypeSurfaceRegularity
import KltDP.Literature.Stacks.FieldJ2

/-!
# Finite singular loci for normal finite-type surfaces

This applies the literal field case of Stacks 07PJ(1) to the general
proved finite-type adapter. Normality and dimension refer to the original
scheme and its stalks. No projectivity or integrality is required.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

/-- Every normal scheme locally of finite type over a field and of
 dimension at most two has open regular locus. -/
theorem normalLocallyFiniteType_regularLocus_isOpen
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 2) :
    IsOpen (regularLocus X) :=
  normalLocallyFiniteType_regularLocus_isOpen_of_J2 f hnormal hdim
    (Literature.Stacks.field_isJ2.{u, u} k)

/-- Finiteness of the actual singular locus for every normal finite-type
scheme of dimension at most two over a field. -/
theorem normalFiniteType_singularLocus_finite
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 2) :
    (singularLocus X).Finite :=
  normalFiniteType_singularLocus_finite_of_J2 f hnormal hdim
    (Literature.Stacks.field_isJ2.{u, u} k)

/-- A finite set with exactly the nonregular points as members. -/
theorem normalFiniteType_exists_singularPointFinset
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 2) :
    ∃ s : Finset X, ∀ x : X, x ∈ s ↔ ¬ RegularLocal (X.presheaf.stalk x) :=
  normalFiniteType_exists_singularPointFinset_of_J2 f hnormal hdim
    (Literature.Stacks.field_isJ2.{u, u} k)

/-- Counting follows the finiteness proof and is equivalent to the
explicit finite-set form required by the manuscript theorem. -/
theorem normalFiniteType_nSing_le_iff
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 2) (bound : ℕ) :
    nSing X (normalFiniteType_singularLocus_finite f hnormal hdim) ≤ bound ↔
      ∃ s : Finset X,
        (∀ x : X, x ∈ s ↔ ¬ RegularLocal (X.presheaf.stalk x)) ∧ s.card ≤ bound :=
  nSing_le_iff_exists_finset X (normalFiniteType_singularLocus_finite f hnormal hdim) bound

end KltDP.Geometry
