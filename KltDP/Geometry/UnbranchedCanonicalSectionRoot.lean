import KltDP.Geometry.UnbranchedCanonicalSectionNonzero
import KltDP.Geometry.ProperGlobalSectionUnit
import KltDP.Geometry.ProperGlobalUnitSquareRoot

/-!
# A unit square root of the original pulled branch coefficient

The coefficient is computed from the actual adjunction-unit pullback of the
original canonical Cartier section in any actual global frame. Disjointness
from the original branch scheme proves it nonzero; properness and the
algebraically closed base then give a unit square root in the original ring.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u

namespace KltDP.Geometry.UnbranchedCanonicalSection

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- An actual global frame of the pulled Cartier module gives a nonzero
coefficient for the original canonical section. -/
theorem frame_coefficient_ne_zero {X C : Scheme.{u}} [IsIntegral X] [Nonempty C]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E) (f : C ⟶ X)
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base))
    (e : (schemeModulePullback f).obj (cartierDivisorModule X E) ≅
      _root_.SheafOfModules.unit C.ringCatSheaf) :
    e.hom.val.app (op (f ⁻¹ᵁ ⊤))
      (RationalTreePicard.pulledSection f (cartierDivisorModule X E) ⊤
        (effectiveCartierSection X E hE)) ≠ 0 := by
  let M := (schemeModulePullback f).obj (cartierDivisorModule X E)
  let s := RationalTreePicard.pulledSection f (cartierDivisorModule X E) ⊤
    (effectiveCartierSection X E hE)
  intro hz
  have hc : e.inv.val.app (op (f ⁻¹ᵁ ⊤))
      (e.hom.val.app (op (f ⁻¹ᵁ ⊤)) s) = s :=
    congrArg (fun a : M ⟶ M => a.val.app (op (f ⁻¹ᵁ ⊤)) s) e.hom_inv_id
  have h := congrArg (fun a => e.inv.val.app (op (f ⁻¹ᵁ ⊤)) a) hz
  change e.inv.val.app (op (f ⁻¹ᵁ ⊤))
    (e.hom.val.app (op (f ⁻¹ᵁ ⊤)) s) = e.inv.val.app (op (f ⁻¹ᵁ ⊤)) 0 at h
  rw [hc, map_zero] at h
  exact pulledSection_ne_zero E hE f hdisj h

/-- The original pulled branch section supplies a unit root; neither a
nonzero coefficient nor a chosen root is assumed. -/
theorem exists_unit_square_root {k : Type u} [Field k] [IsAlgClosed k]
    {X C : Scheme.{u}} [IsIntegral X] [IsIntegral C]
    (sC : C ⟶ Spec (CommRingCat.of k)) [UniversallyClosed sC] [LocallyOfFiniteType sC]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E) (f : C ⟶ X)
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base))
    (e : (schemeModulePullback f).obj (cartierDivisorModule X E) ≅
      _root_.SheafOfModules.unit C.ringCatSheaf) :
    ∃ b : Γ(C, ⊤)ˣ, (b : Γ(C, ⊤)) ^ 2 =
      e.hom.val.app (op (f ⁻¹ᵁ ⊤))
        (RationalTreePicard.pulledSection f (cartierDivisorModule X E) ⊤
          (effectiveCartierSection X E hE)) := by
  let a : Γ(C, ⊤) := e.hom.val.app (op (f ⁻¹ᵁ ⊤))
    (RationalTreePicard.pulledSection f (cartierDivisorModule X E) ⊤
      (effectiveCartierSection X E hE))
  have ha : a ≠ 0 := frame_coefficient_ne_zero E hE f hdisj e
  obtain ⟨u, hu⟩ := ProperGlobalSectionUnit.isUnit_of_ne_zero sC a ha
  obtain ⟨b, hb⟩ := ProperGlobalUnitSquareRoot.exists_sq sC u
  refine ⟨b, ?_⟩
  have h := congrArg (fun v : Γ(C, ⊤)ˣ => (v : Γ(C, ⊤))) hb
  change (b : Γ(C, ⊤)) ^ 2 = (u : Γ(C, ⊤)) at h
  exact h.trans hu

end KltDP.Geometry.UnbranchedCanonicalSection

#print axioms KltDP.Geometry.UnbranchedCanonicalSection.exists_unit_square_root
