import KltDP.Topology.CurveConnectedFibers
import KltDP.Geometry.CartierDivisorPullback
import KltDP.Geometry.PrimeCurvePointFiberFactorization

/-!
# The original nonconstant curve map preserves generic points

A closed image of the source generic point would force the entire original
map to be constant. On the original integral target curve every nonclosed
point is generic, by the proved dimension-one topology. This supplies the
actual generic-point condition needed for signed Cartier pullback.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ProperNonconstantCurve

/-- A nonconstant map to the original integral Noetherian curve preserves
the original generic points. Properness is unnecessary for this topological step. -/
theorem genericPointPreserving_of_nonconstant_base
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [NoetherianSpace Y]
    (g : X ⟶ Y) (hdim : topologicalKrullDim Y ≤ 1)
    (hnonconstant : ¬ ∃ y : Y, ∀ x : X, g.base x = y) :
    GenericPointPreserving g := by
  have hnotclosed : ¬ IsClosed ({g.base (genericPoint X)} : Set Y) := by
    intro hclosed
    have hpre : IsClosed (g.base ⁻¹' {g.base (genericPoint X)}) :=
      hclosed.preimage (by fun_prop)
    have hmem : genericPoint X ∈ g.base ⁻¹' {g.base (genericPoint X)} := rfl
    have hall : (Set.univ : Set X) ⊆ g.base ⁻¹' {g.base (genericPoint X)} :=
      ((genericPoint_spec X).mem_closed_set_iff hpre).mp hmem
    exact hnonconstant ⟨g.base (genericPoint X), fun x => hall (Set.mem_univ x)⟩
  have hgeneric : IsGenericPoint (g.base (genericPoint X)) (Set.univ : Set Y) :=
    KltDP.Topology.closure_singleton_eq_univ_of_not_isClosed
      hdim (g.base (genericPoint X)) hnotclosed
  exact ⟨hgeneric.eq (genericPoint_spec Y)⟩

/-- The original field-compatible notion of nonconstancy supplies the
generic-point condition, with no dominant-map assumption. -/
theorem genericPointPreserving_of_not_factors_through_structure
    {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [NoetherianSpace Y]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (σ : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType σ]
    (g : X ⟶ Y) [IsProper g] (hg : g ≫ σ = f)
    (hdim : topologicalKrullDim Y ≤ 1)
    (hnonconstant : ¬ ∃ p : Spec (CommRingCat.of k) ⟶ Y, f ≫ p = g) :
    GenericPointPreserving g := by
  apply genericPointPreserving_of_nonconstant_base g hdim
  rintro ⟨y, hy⟩
  obtain ⟨p, hgp, _, _⟩ :=
    PrimeCurvePointFiberFactorization.exists_fieldPoint_of_constant_base f σ g hg y hy
  exact hnonconstant ⟨p, hgp.symm⟩

end KltDP.Geometry.ProperNonconstantCurve

#print axioms KltDP.Geometry.ProperNonconstantCurve.genericPointPreserving_of_nonconstant_base
#print axioms KltDP.Geometry.ProperNonconstantCurve.genericPointPreserving_of_not_factors_through_structure
