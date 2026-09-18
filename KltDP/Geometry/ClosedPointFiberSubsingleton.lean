import KltDP.Geometry.PointFiberPrimeThroughPoint
import KltDP.Geometry.PrimeCurvePointFiberFactorization

/-!
Closed connected fibers outside the images of all contracted prime curves
are subsingletons. The original nontrivial fiber itself supplies a prime
curve, using the proved Noetherian component and surface dimension lemmas.
No quasi-finiteness or exhaustion by a previously chosen curve is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ClosedPointFiberSubsingleton

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)
  {Y : Scheme.{u}} [Nontrivial Y] (π : X.toScheme ⟶ Y) [Surjective π]

/-- A nontrivial connected closed fiber contains an actual original prime
curve through each of its points. -/
theorem exists_primeCurve_of_nontrivial (y : Y) (hy : IsClosed ({y} : Set Y))
    (hconnected : IsConnected (π.base ⁻¹' {y}))
    (hnt : (π.base ⁻¹' {y}).Nontrivial) (x : X.toScheme) (hx : π.base x = y) :
    ∃ C : X.PrimeCurve, x ∈ (C : Set X.toScheme) ∧
      ∀ z ∈ (C : Set X.toScheme), π.base z = y := by
  obtain ⟨Z, hxZ, hZnt, hZsub⟩ :=
    KltDP.Topology.ConnectedNoetherianFibers.exists_nontrivial_irreducibleClosed_subset
      (π.base ⁻¹' {y}) (hy.preimage π.base.hom.continuous) hconnected hnt x hx
  have hne : (Z : Set X.toScheme) ≠ Set.univ := by
    intro hZ
    apply ConnectedPointFiberComponents.pointFiber_ne_univ X π y
    exact Set.Subset.antisymm (Set.subset_univ _) (hZ ▸ hZsub)
  exact ⟨ConnectedPointFiberComponents.primeCurveOfProperNontrivialClosed X Z hZnt hne,
    hxZ, fun z hz => hZsub hz⟩

/-- Outside the image of a set containing every contracted prime, a
connected closed point fiber has at most one point. -/
theorem subsingleton_off_contracted_support [IsAlgClosed k]
    (σ : Y ⟶ Spec (CommRingCat.of k)) (hπ : π ≫ σ = X.structureMorphism)
    (S : Set X.toScheme)
    (hS : ∀ C : X.PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _) →
      (C : Set X.toScheme) ⊆ S)
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hconnected : IsConnected (π.base ⁻¹' {y})) (hout : y ∉ π.base '' S) :
    (π.base ⁻¹' {y}).Subsingleton := by
  apply Set.not_nontrivial_iff.mp
  intro hnt
  obtain ⟨x, hx⟩ := hnt.nonempty
  obtain ⟨C, hxC, hC⟩ := exists_primeCurve_of_nontrivial X π y hy hconnected hnt x hx
  obtain ⟨p, hp, hpσ, _⟩ :=
    PrimeCurvePointFiberFactorization.exists_factor_of_constant X C σ π hπ y hC
  exact hout ⟨x, hS C ⟨p, hp, hpσ⟩ hxC, hx⟩

end KltDP.Geometry.ClosedPointFiberSubsingleton
