import KltDP.Geometry.CurvePreservedOnIsomorphismOpen

/-!
# Pair-kernel restriction on the original isomorphism open

The same actual open comparison used for conormal modules applies to
one curve's ideal pulled back to another curve. The two curves may meet.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.CurveOnIsomorphismOpen

/-- An open ambient map preserves the original two-map kernel restriction. -/
def pairKernelPostcompOpenIso {A B X Y : Scheme.{u}}
    (i : A ⟶ X) (j : B ⟶ X) (a : X ⟶ Y) [IsOpenImmersion a] :
    (schemeModulePullback (i ≫ a)).obj (schemeKernelIdeal (j ≫ a)) ≅
      (schemeModulePullback i).obj (schemeKernelIdeal j) :=
  ((schemeModulePullbackCompIso i a).app (schemeKernelIdeal (j ≫ a))).symm ≪≫
    (schemeModulePullback i).mapIso (schemeKernelPostcompOpenIso j a)

/-- Two original maps contained in the same isomorphism open retain their pair-kernel module. -/
def pairKernelIso {A B S T : Scheme.{u}} (i : A ⟶ S) (j : B ⟶ S)
    (b : S ⟶ T) (U : T.Opens) [IsIso (b ∣_ U)]
    (hi : Set.range i.base ⊆ ((b ⁻¹ᵁ U : S.Opens) : Set S))
    (hj : Set.range j.base ⊆ ((b ⁻¹ᵁ U : S.Opens) : Set S)) :
    (schemeModulePullback (i ≫ b)).obj (schemeKernelIdeal (j ≫ b)) ≅
      (schemeModulePullback i).obj (schemeKernelIdeal j) :=
  eqToIso (by rw [← comp_factor i b U hi, ← comp_factor j b U hj]) ≪≫
    pairKernelPostcompOpenIso (lift i b U hi ≫ (b ∣_ U))
      (lift j b U hj ≫ (b ∣_ U)) U.ι ≪≫
    pairKernelPostcompOpenIso (lift i b U hi) (lift j b U hj) (b ∣_ U) ≪≫
    (pairKernelPostcompOpenIso (lift i b U hi) (lift j b U hj) (b ⁻¹ᵁ U).ι).symm ≪≫
    eqToIso (by rw [lift_ι i b U hi, lift_ι j b U hj])

end KltDP.Geometry.CurveOnIsomorphismOpen

#print axioms KltDP.Geometry.CurveOnIsomorphismOpen.pairKernelIso
