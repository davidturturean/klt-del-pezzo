import KltDP.Geometry.ProperNonconstantCurveFinite
import KltDP.Geometry.PrimeCurvePointFiberFactorization
import KltDP.Geometry.LocallyOfFiniteTypeNoetherian

/-!
The actual field-point notion of nonconstancy supplied by the genus-zero
linear system suffices for finiteness. All Noetherian hypotheses are
derived from the original structure morphisms.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ProperNonconstantCurve

/-- The original proper nonconstant morphism of a proper integral curve
to a finite-type scheme over the same algebraically closed field is finite. -/
theorem isFinite_of_not_factors_through_structure
    {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (σ : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType σ]
    (g : X ⟶ Y) [IsProper g] (hg : g ≫ σ = f)
    (hdim : topologicalKrullDim X ≤ 1)
    (hnonconstant : ¬ ∃ p : Spec (CommRingCat.of k) ⟶ Y, f ≫ p = g) :
    IsFinite g := by
  letI : NoetherianSpace X := noetherianSpace_of_locallyOfFiniteType_quasiCompact_spec f
  letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_locallyOfFiniteType_spec σ
  apply isFinite_of_nonconstant_base g hdim
  rintro ⟨y, hy⟩
  obtain ⟨p, hgp, _, _⟩ :=
    PrimeCurvePointFiberFactorization.exists_fieldPoint_of_constant_base f σ g hg y hy
  exact hnonconstant ⟨p, hgp.symm⟩

#check KltDP.Geometry.ProperNonconstantCurve.isFinite_of_not_factors_through_structure
#print axioms KltDP.Geometry.ProperNonconstantCurve.isFinite_of_not_factors_through_structure

end KltDP.Geometry.ProperNonconstantCurve
