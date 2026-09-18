import KltDP.Geometry.ProperConnectedReducedConstants
import KltDP.Geometry.UnbranchedCanonicalSectionRoot

/-!
# The original branch coefficient on a whole connected reduced proper scheme

The source may be reducible. The already proved original scalar-map theorem
and branch-disjoint nonvanishing supply a unit square root in its original
global section ring. This applies to an entire unbranched rational tree.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u

namespace KltDP.Geometry.UnbranchedCanonicalSection

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Reduced connected proper sources need not be integral for the actual
pulled branch coefficient to have a global unit square root. -/
theorem exists_unit_square_root_of_connected_reduced
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C : Scheme.{u}} [IsIntegral X] [IsReduced C] [ConnectedSpace C]
    (sC : C ⟶ Spec (CommRingCat.of k)) [IsProper sC]
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
  obtain ⟨c, hc⟩ :=
    (ProperConnectedReducedConstants.baseFieldToGlobalSections_bijective sC).surjective a
  have hc0 : c ≠ 0 := by
    intro h
    apply ha
    rw [← hc, h, map_zero]
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (show 0 < 2 by decide)
  have hd0 : d ≠ 0 := by
    intro h
    apply hc0
    simpa only [h, zero_pow (show 2 ≠ 0 by decide)] using hd.symm
  refine ⟨Units.map (baseFieldToGlobalSections sC).toMonoidHom (Units.mk0 d hd0), ?_⟩
  change (baseFieldToGlobalSections sC d) ^ 2 = a
  rw [← map_pow, hd, hc]

end KltDP.Geometry.UnbranchedCanonicalSection

#print axioms KltDP.Geometry.UnbranchedCanonicalSection.exists_unit_square_root_of_connected_reduced
