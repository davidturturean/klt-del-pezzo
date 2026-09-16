import KltDP.Geometry.CartierPrincipalShift
import KltDP.Geometry.CartierPicardComparison
import KltDP.Geometry.EffectiveCartierSection

/-!
# An effective Cartier representative preserving an original nonzero section

On an integral scheme, represent the original invertible sheaf by the
already constructed Cartier module O(D). Its nonzero section has an actual
nonzero rational value q. Original fractional membership gives regular
equations f*q for E = D + div(q). The proved multiplication isomorphism
O(E) ≅ O(D) sends rational one to the supplied section.

Thus the final actual isomorphism O(E) ≅ L preserves the original section.
All local coefficients and their nonzerodivisor conditions are derived.
No separatedness, normality, Noetherianity, dimension or square-root
assumption is used. The closed-subscheme and structural-kernel comparison
remain a separate adapter; effectiveness here is the existing regular
equation condition on the actual Cartier quotient-sheaf section.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

/-- The rational value of the original global fractional-module section. -/
def cartierGlobalSectionRationalValue (D : CartierDivisor X)
    (s : (cartierDivisorModule X D).val.obj (op (⊤ : X.Opens))) : X.functionField :=
  rationalFunctionModuleSectionsEquiv X ⊤ s.val

/-- Its rational value is nonzero because both original maps are injective. -/
theorem cartierGlobalSectionRationalValue_ne_zero (D : CartierDivisor X)
    (s : (cartierDivisorModule X D).val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) :
    cartierGlobalSectionRationalValue X D s ≠ 0 := by
  intro h
  apply hs
  apply Subtype.ext
  apply (rationalFunctionModuleSectionsEquiv X ⊤).injective
  exact h.trans (map_zero (rationalFunctionModuleSectionsEquiv X ⊤)).symm

/-- The actual restriction represents exactly the same rational function. -/
theorem cartierGlobalSectionRationalValue_restrict (D : CartierDivisor X)
    (s : (cartierDivisorModule X D).val.obj (op (⊤ : X.Opens)))
    (U : X.Opens) [Nonempty U] :
    rationalFunctionModuleSectionsEquiv X U
        ((cartierDivisorModule X D).val.map (homOfLE (le_top : U ≤ ⊤)).op s).val =
      cartierGlobalSectionRationalValue X D s :=
  rationalFunctionModuleSectionsEquiv_naturality X (homOfLE (le_top : U ≤ ⊤)) s.val

/-- Shifting by the actual rational value produces original regular
Cartier equations, with coefficients supplied by original O(D) membership. -/
theorem cartierPrincipalShift_hasRegularEquations (D : CartierDivisor X)
    (s : (cartierDivisorModule X D).val.obj (op (⊤ : X.Opens)))
    (q : X.functionFieldˣ) (hq : (q : X.functionField) = cartierGlobalSectionRationalValue X D s) :
    HasRegularCartierEquations X
      (D + principalCartierDivisorHom X (Additive.ofMul q)) := by
  intro x
  obtain ⟨U, i, hxU, f, hf⟩ := exists_local_cartier_equation X ⊤ D x trivial
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hi : i = homOfLE (le_top : U ≤ ⊤) := Subsingleton.elim _ _
  have hf' : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op D := by
    simpa only [hi] using hf
  let t := (cartierDivisorModule X D).val.map (homOfLE (le_top : U ≤ ⊤)).op s
  have ht := (mem_cartierSectionSubmodule_iff X D U f hf' t.val).mp t.property
  obtain ⟨a, ha⟩ := (mem_principalEquationSubmodule_iff X U f _).mp ht
  have hvalue : rationalFunctionModuleSectionsEquiv X U t.val = (q : X.functionField) :=
    (cartierGlobalSectionRationalValue_restrict X D s U).trans hq.symm
  refine ⟨{
    chart := {
      openSet := U
      nonempty := inferInstance
      equation := f * q
      represents := cartierGlobalEquation_mul X D
        (principalCartierDivisorHom X (Additive.ofMul q)) U f q hf'
        (principalCartierDivisor_equation X q U) }
    coefficient := a
    germ_eq := ?_ }, hxU⟩
  exact ha.trans (congrArg (fun z : X.functionField => (f : X.functionField) * z) hvalue)

/-- Every derived regular Cartier coefficient is an actual nonzerodivisor
of its original section ring, including when the resulting divisor is empty. -/
theorem RegularCartierEquationChart.coefficient_mem_nonZeroDivisors
    (D : CartierDivisor X) (c : RegularCartierEquationChart X D) :
    c.coefficient ∈ nonZeroDivisors Γ(X, c.chart.openSet) :=
  mem_nonZeroDivisors_of_ne_zero (RegularCartierEquationChart.coefficient_ne_zero X D c)

/-- The actual multiplication isomorphism sends the constructed canonical
section to the original section having that rational value. -/
theorem cartierPrincipalShiftIso_canonicalSection (D : CartierDivisor X)
    (s : (cartierDivisorModule X D).val.obj (op (⊤ : X.Opens)))
    (q : X.functionFieldˣ) (hq : (q : X.functionField) = cartierGlobalSectionRationalValue X D s)
    (hE : HasRegularCartierEquations X
      (D + principalCartierDivisorHom X (Additive.ofMul q))) :
    (cartierPrincipalShiftIso X D q).hom.val.app (op (⊤ : X.Opens))
      (effectiveCartierSection X
        (D + principalCartierDivisorHom X (Additive.ofMul q)) hE) = s := by
  apply Subtype.ext
  apply (rationalFunctionModuleSectionsEquiv X ⊤).injective
  rw [cartierPrincipalShiftIso_hom_app_field]
  change (q : X.functionField) * rationalFunctionModuleSectionsEquiv X ⊤
      ((structureToRationalFunctionModule X).val.app (op (⊤ : X.Opens)) (1 : Γ(X, ⊤))) = _
  rw [rationalFunctionModuleSectionsEquiv_structure, map_one, mul_one]
  exact hq

/-- A nonzero original section of an invertible sheaf has an actual
effective Cartier representative whose canonical section maps to it. -/
theorem exists_effectiveCartier_of_nonzero_section (L : InvertibleSheaf X)
    (s : L.obj.val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) :
    ∃ (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
      (e : cartierDivisorModule X E ≅ L.obj),
      e.hom.val.app (op (⊤ : X.Opens)) (effectiveCartierSection X E hE) = s := by
  obtain ⟨D, ⟨a⟩⟩ := exists_cartierDivisor_module_iso X L.obj
  let t := a.hom.val.app (op (⊤ : X.Opens)) s
  have ht : t ≠ 0 := by
    let α := ((_root_.SheafOfModules.evaluation X.ringCatSheaf
      (op (⊤ : X.Opens))).mapIso a).toLinearEquiv
    intro h
    apply hs
    apply α.injective
    exact h.trans (map_zero α).symm
  let q : X.functionFieldˣ := Units.mk0 (cartierGlobalSectionRationalValue X D t)
    (cartierGlobalSectionRationalValue_ne_zero X D t ht)
  let E := D + principalCartierDivisorHom X (Additive.ofMul q)
  have hE : HasRegularCartierEquations X E :=
    cartierPrincipalShift_hasRegularEquations X D t q rfl
  refine ⟨E, hE, cartierPrincipalShiftIso X D q ≪≫ a.symm, ?_⟩
  change a.inv.val.app (op (⊤ : X.Opens))
    ((cartierPrincipalShiftIso X D q).hom.val.app (op (⊤ : X.Opens))
      (effectiveCartierSection X E hE)) = s
  rw [cartierPrincipalShiftIso_canonicalSection X D t q rfl hE]
  exact congrArg (fun f : L.obj ⟶ L.obj => f.val.app (op (⊤ : X.Opens)) s) a.hom_inv_id

end KltDP.Geometry
