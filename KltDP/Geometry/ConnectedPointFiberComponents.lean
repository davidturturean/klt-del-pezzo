import KltDP.Topology.ConnectedNoetherianFibers
import KltDP.Geometry.PrimeCurveCodimension

/-!
An original connected closed point fiber containing an original contracted
prime curve has a nontrivial ambient irreducible closed subset through
every one of its points. No exhaustion by curves or image-component
correspondence is assumed. This isolates the ordinary topological step
needed before applying a surface's all-prime contraction criterion.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.ConnectedPointFiberComponents

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The original dimension-one carrier of a prime curve is nontrivial. -/
theorem primeCurve_nontrivial (C : X.PrimeCurve) : (C : Set X.toScheme).Nontrivial := by
  classical
  by_contra h
  letI : Subsingleton (C : Set X.toScheme) := (Set.not_nontrivial_iff.mp h).coe_sort
  have hd := topologicalKrullDim_nonpos_of_subsingleton (C : Set X.toScheme)
  rw [C.dimension_one] at hd
  exact (WithBot.coe_lt_coe.mpr (by simp : (0 : ℕ∞) < 1)).not_le hd

/-- Every point of a connected closed fiber containing a contracted
original prime lies on a nontrivial irreducible closed subset of that fiber. -/
theorem exists_irreducibleClosed_in_pointFiber {Y : Scheme.{u}}
    (f : X.toScheme ⟶ Y) (y : Y) (hy : IsClosed ({y} : Set Y))
    (hconnected : IsConnected (f.base ⁻¹' {y})) (C : X.PrimeCurve)
    (hC : ∀ z ∈ (C : Set X.toScheme), f.base z = y)
    (x : X.toScheme) (hx : f.base x = y) :
    ∃ Z : IrreducibleCloseds X.toScheme,
      x ∈ Z ∧ (Z : Set X.toScheme).Nontrivial ∧
        (Z : Set X.toScheme) ⊆ f.base ⁻¹' {y} := by
  have hCsub : (C : Set X.toScheme) ⊆ f.base ⁻¹' {y} := by
    intro z hz
    exact hC z hz
  exact KltDP.Topology.ConnectedNoetherianFibers.exists_nontrivial_irreducibleClosed_subset
    (f.base ⁻¹' {y}) (hy.preimage f.base.hom.continuous) hconnected
    ((primeCurve_nontrivial X C).mono hCsub) x hx

end KltDP.Geometry.ConnectedPointFiberComponents
