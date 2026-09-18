import KltDP.Geometry.CartierIndependentSectionRatio
import KltDP.Geometry.ProperGlobalSectionsConstants
import KltDP.Geometry.CartierEquationUnits

/-! Independent original sections yield distinct original effective
Cartier shifts. Equality of those divisors would make the original ratio
a global unit and hence a scalar for the same base-field action. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open KltDP.Geometry.ModuleCohomology
universe u
namespace KltDP.Geometry.CartierIndependentSectionRatio

variable {k : Type u} [Field k] [IsAlgClosed k]
  {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k))
  [UniversallyClosed f] [LocallyOfFiniteType f]

/-- The divisors formed using the two original rational values are
distinct; no distinctness or nonconstant-ratio input is supplied. -/
theorem principalShifts_ne (D : CartierDivisor X)
    (s : Fin 2 → sections (cartierDivisorModule X D))
    (hs : letI := baseSectionsModule f (cartierDivisorModule X D); LinearIndependent k s)
    (q : Fin 2 → X.functionFieldˣ)
    (hq : ∀ i, (q i : X.functionField) = cartierGlobalSectionRationalValue X D (s i)) :
    D + principalCartierDivisorHom X (Additive.ofMul (q 0)) ≠
      D + principalCartierDivisorHom X (Additive.ofMul (q 1)) := by
  intro heq
  have hprincipal : cartierEquationClassHom X ⊤ (Additive.ofMul (q 0)) =
      cartierEquationClassHom X ⊤ (Additive.ofMul (q 1)) := add_left_cancel heq
  obtain ⟨a, ha⟩ := (cartierEquationClassHom_eq_iff X ⊤ (q 0) (q 1)).mp hprincipal
  obtain ⟨c, hc⟩ := (baseFieldToGlobalSections_bijective f).surjective (a : Γ(X, ⊤))
  have hvalue : X.germToFunctionField ⊤ (a : Γ(X, ⊤)) =
      (q 0 : X.functionField) / (q 1 : X.functionField) := by
    simpa only [Units.coe_map, Units.val_div_eq_div_val] using
      congrArg (fun z : X.functionFieldˣ => (z : X.functionField)) ha
  apply ratio_ne_scalar f D s hs c
  calc
    ratio X D s = (q 0 : X.functionField) / (q 1 : X.functionField) := by
      rw [hq 0, hq 1]
      rfl
    _ = X.germToFunctionField ⊤ (a : Γ(X, ⊤)) := hvalue.symm
    _ = baseFieldToFunctionField f c := by
      rw [← hc]
      rfl

end KltDP.Geometry.CartierIndependentSectionRatio

#check @KltDP.Geometry.CartierIndependentSectionRatio.principalShifts_ne
#print axioms KltDP.Geometry.CartierIndependentSectionRatio.principalShifts_ne
