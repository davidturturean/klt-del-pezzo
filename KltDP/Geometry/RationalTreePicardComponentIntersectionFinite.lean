import KltDP.Geometry.RationalTreePicardComponentLeaf
import Mathlib.Topology.KrullDimension
import Mathlib.Tactic.NormNum

/-!
# Finitely many actual component intersections on a curve

In dimension at most one, a point on two distinct original irreducible
components is closed: otherwise a strict specialization supplies a chain
of three irreducible closed subsets. The intersection-point set is closed
because the original scheme has finitely many components. Noetherian
irreducible decomposition and sobriety then make this set finite.

Thus the actual component-point leaf theorem needs no separate finiteness
hypothesis for a Noetherian curve. Neither intrinsic nodality nor reduced
scheme-theoretic intersections are asserted by this topological argument.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (X : Scheme.{u})

/-- In dimension at most one, an original point on two distinct original
components is closed. This does not require reducedness or nodality. -/
theorem isClosed_singleton_of_mem_componentIntersectionPoints
    (hdim : topologicalKrullDim X ≤ 1) {x : X}
    (hx : x ∈ componentIntersectionPoints X) : IsClosed ({x} : Set X) := by
  classical
  obtain ⟨C, D, hCD, hxC, hxD⟩ := hx
  apply closure_subset_iff_isClosed.mp
  intro y hy
  apply Set.mem_singleton_iff.mpr
  by_contra hne
  let A : IrreducibleCloseds X :=
    ⟨closure ({y} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
  let B : IrreducibleCloseds X :=
    ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
  let E : IrreducibleCloseds X :=
    ⟨C.1, C.2.1, isClosed_of_mem_irreducibleComponents C.1 C.2⟩
  have hAB : A < B := by
    refine lt_iff_le_and_ne.mpr ⟨?_, ?_⟩
    · exact closure_minimal (Set.singleton_subset_iff.mpr hy) isClosed_closure
    · intro h
      have hcl : closure ({y} : Set X) = closure ({x} : Set X) :=
        congrArg (fun Z : IrreducibleCloseds X => (Z : Set X)) h
      exact hne ((show IsGenericPoint y (closure ({x} : Set X)) from hcl).eq
        isGenericPoint_closure)
  have hBE : B < E := by
    refine lt_iff_le_and_ne.mpr ⟨?_, ?_⟩
    · exact closure_minimal (Set.singleton_subset_iff.mpr hxC) E.isClosed
    · intro h
      have hcl : closure ({x} : Set X) = C.1 :=
        congrArg (fun Z : IrreducibleCloseds X => (Z : Set X)) h
      have hle : C.1 ⊆ D.1 := by
        rw [← hcl]
        exact closure_minimal (Set.singleton_subset_iff.mpr hxD)
          (isClosed_of_mem_irreducibleComponents D.1 D.2)
      exact hCD (Subtype.ext (hle.antisymm (C.2.2 D.2.1 hle)))
  let p : LTSeries (IrreducibleCloseds X) :=
    ((RelSeries.singleton (· < ·) A).snoc B (by simpa using hAB)).snoc E
      (by simpa using hBE)
  have htwo : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X :=
    Order.le_krullDim_iff.mpr ⟨p, by simp [p]⟩
  have hbad : (2 : WithBot ℕ∞) ≤ 1 := htwo.trans hdim
  norm_num at hbad

variable [NoetherianSpace X]

/-- The original component-intersection locus is a closed set, even
without a dimension bound. -/
theorem componentIntersectionPoints_isClosed :
    IsClosed (componentIntersectionPoints X) := by
  classical
  letI : Finite ↥(irreducibleComponents X) := by
    rw [Set.finite_coe_iff]
    exact NoetherianSpace.finite_irreducibleComponents
  have hEq : componentIntersectionPoints X =
      ⋃ C : ↥(irreducibleComponents X),
        C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) := by
    ext x
    constructor
    · rintro ⟨C, D, hCD, hxC, hxD⟩
      refine Set.mem_iUnion.mpr ⟨C, hxC, ?_⟩
      exact (mem_componentClosedUnion X ({C}ᶜ) x).mpr
        ⟨D, fun h => hCD (Set.mem_singleton_iff.mp h).symm, hxD⟩
    · intro hx
      obtain ⟨C, hxC, hxOther⟩ := Set.mem_iUnion.mp hx
      obtain ⟨D, hD, hxD⟩ := (mem_componentClosedUnion X ({C}ᶜ) x).mp hxOther
      exact ⟨C, D, fun h => hD (Set.mem_singleton_iff.mpr h.symm), hxC, hxD⟩
  rw [hEq]
  exact isClosed_iUnion_of_finite (fun C =>
    (isClosed_of_mem_irreducibleComponents C.1 C.2).inter
      (componentClosedUnion X ({C}ᶜ)).isClosed)

/-- A Noetherian scheme of dimension at most one has only finitely many
original points belonging to distinct original irreducible components. -/
theorem componentIntersectionPoints_finite (hdim : topologicalKrullDim X ≤ 1) :
    (componentIntersectionPoints X).Finite := by
  obtain ⟨S, hSfin, hSclosed, hSirr, hSsup⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible
      (componentIntersectionPoints_isClosed X)
  rw [hSsup]
  refine Set.Finite.sUnion hSfin (fun t ht => ?_)
  obtain ⟨z, hz⟩ := QuasiSober.sober (hSirr t ht) (hSclosed t ht)
  have hzX : z ∈ componentIntersectionPoints X := by
    rw [hSsup]
    exact Set.mem_sUnion.mpr ⟨t, ht, hz.mem⟩
  have hzclosed := isClosed_singleton_of_mem_componentIntersectionPoints X hdim hzX
  have htpoint : t = {z} := by rw [← hz.def, hzclosed.closure_eq]
  rw [htpoint]
  exact Set.finite_singleton z

/-- The actual leaf and its original affine singleton support follow from
the curve's dimension bound and tree property, with finiteness proved above. -/
theorem exists_component_leaf_chart_support_of_dimension_le_one
    [Nontrivial ↥(irreducibleComponents X)]
    (hdim : topologicalKrullDim X ≤ 1)
    (hTree : (componentPointIncidenceGraph X).IsTree) :
    ∃ (C : ↥(irreducibleComponents X)) (q : X),
      C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q} ∧
      ∀ (U : X.affineOpens) (hq : q ∈ U.1),
        PrimeSpectrum.zeroLocus
            (componentChartIdeal X {C} U ⊔ componentChartIdeal X ({C}ᶜ) U :
              Ideal Γ(X, U.1)) =
          {U.2.primeIdealOf ⟨q, hq⟩} :=
  exists_component_leaf_chart_support X (componentIntersectionPoints_finite X hdim) hTree

end KltDP.Geometry.RationalTreePicard
