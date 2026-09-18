import KltDP.Geometry.QuadraticRootRegular
import KltDP.Geometry.QuadraticRamificationCharts
import KltDP.RingTheory.ConormalRestriction

/-!
# Original root conormal coordinates and their actual transition

The original branch equation proves regularity of the actual quotient
root. Its conormal class therefore gives a proved frame. The actual
quadratic coordinate map induces a conormal map, and its coordinate
multiplier is exactly the original unit after quotienting. No conormal
frame, regularity of the root, or transition equality is supplied.
-/

noncomputable section
universe u

namespace KltDP.Geometry.QuadraticCover

open KltDP.RingTheory

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The original root as an element of its actual principal ideal. -/
def rootIdealGenerator (s : R) : rootIdeal s :=
  ⟨root s, Ideal.subset_span (Set.mem_singleton (root s))⟩

/-- The actual root class is a conormal frame, derived from the branch equation. -/
def rootConormalEquiv (s : R) (hs : s ∈ nonZeroDivisors R) :
    (CoverAlgebra s ⧸ rootIdeal s) ≃ₗ[CoverAlgebra s ⧸ rootIdeal s]
      (rootIdeal s).Cotangent :=
  principalConormalEquiv (rootIdeal s) (rootIdealGenerator s) rfl
    (root_mem_nonZeroDivisors s hs)

@[simp]
theorem rootConormalEquiv_one (s : R) (hs : s ∈ nonZeroDivisors R) :
    rootConormalEquiv s hs 1 = (rootIdeal s).toCotangent (rootIdealGenerator s) :=
  principalConormalEquiv_one _ _ _ _

/-- The conormal map induced by the original coefficient and root-rescaling map. -/
def rootConormalMap (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) :
    (rootIdeal s).Cotangent →ₛₗ[rootZeroQuotientMap f s t v h] (rootIdeal t).Cotangent :=
  conormalMap (rootIdeal s) (rootIdeal t) (mappedRescaleHom f s t v h)
    (Ideal.map_le_iff_le_comap.mp
      (le_of_eq (map_rootIdeal_mappedRescaleHom f s t v h)))

/-- Actual conormal frames transform by the original quotient image of the unit. -/
theorem rootConormalMap_frame (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) (hs : s ∈ nonZeroDivisors R)
    (ht : t ∈ nonZeroDivisors S) (q : CoverAlgebra s ⧸ rootIdeal s) :
    rootConormalMap f s t v h (rootConormalEquiv s hs q) =
      rootConormalEquiv t ht
        (rootZeroQuotientMap f s t v h q *
          Ideal.Quotient.mk (rootIdeal t) (algebraMap S (CoverAlgebra t) (v : S))) :=
  conormalMap_principalConormalEquiv (rootIdeal s) (rootIdeal t)
    (mappedRescaleHom f s t v h) _
    (rootIdealGenerator s) rfl (root_mem_nonZeroDivisors s hs)
    (rootIdealGenerator t) rfl (root_mem_nonZeroDivisors t ht)
    (algebraMap S (CoverAlgebra t) (v : S)) (mappedRescaleHom_root f s t v h) q

/-- Inverse conormal coordinates retain that same actual unit multiplier. -/
theorem rootConormalEquiv_symm_map (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) (hs : s ∈ nonZeroDivisors R)
    (ht : t ∈ nonZeroDivisors S) (q : CoverAlgebra s ⧸ rootIdeal s) :
    (rootConormalEquiv t ht).symm
        (rootConormalMap f s t v h (rootConormalEquiv s hs q)) =
      rootZeroQuotientMap f s t v h q *
        Ideal.Quotient.mk (rootIdeal t) (algebraMap S (CoverAlgebra t) (v : S)) := by
  rw [rootConormalMap_frame, LinearEquiv.symm_apply_apply]

/-- Identifying the actual root quotient with the original branch quotient
carries the conormal transition multiplier to the original coefficient unit. -/
theorem rootConormalMultiplier_on_branch (t : S) (v : Sˣ) :
    rootQuotientEquiv t
        (Ideal.Quotient.mk (rootIdeal t) (algebraMap S (CoverAlgebra t) (v : S))) =
      Ideal.Quotient.mk (branchIdeal t) (v : S) :=
  rootQuotientEquiv_mk_algebraMap t (v : S)

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.rootConormalMap_frame
#print axioms KltDP.Geometry.QuadraticCover.rootConormalEquiv_symm_map
