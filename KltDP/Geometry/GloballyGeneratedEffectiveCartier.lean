import KltDP.Geometry.GloballyGeneratedUnitCoefficient
import KltDP.Geometry.SectionEffectiveCartier
import KltDP.Geometry.PrimeCurveCartierRestriction

/-!
# Effective Cartier representatives avoiding a prescribed point

For a globally generated invertible sheaf on an integral scheme, choose an
actual Cartier representative and a local equation at the prescribed point.
The generating-section theorem supplies an original section whose coefficient
in this equation frame is a unit in that stalk.  Shift the original Cartier
divisor by the section's actual rational value.  Its regular equation on the
chosen chart is exactly that coefficient, so the resulting effective Cartier
divisor avoids the point and represents the original invertible sheaf.

This is a scheme-level result: it requires neither a surface nor regularity,
properness, a closed point, a finite zero scheme, or any additional literal.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.GloballyGeneratedEffectiveCartier

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

/-- A section's coordinate in an original Cartier equation frame is the
equation multiplied by that section's original rational value. -/
theorem frame_coefficient_functionField (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op D)
    (s : (cartierDivisorModule X D).val.obj (op (⊤ : X.Opens))) :
    X.germToFunctionField U
        ((cartierEquationOverIso X D U f hf).inv.val.app (op (Over.mk (𝟙 U)))
          ((cartierDivisorModule X D).val.map (homOfLE (le_top : U ≤ ⊤)).op s)) =
      (f : X.functionField) * cartierGlobalSectionRationalValue X D s := by
  haveI : Nonempty (Over.mk (𝟙 U) : Over U).left := ‹Nonempty U›
  let τ := cartierEquationOverIso X D U f hf
  let t := (cartierDivisorModule X D).val.map (homOfLE (le_top : U ≤ ⊤)).op s
  let a : Γ(X, U) := τ.inv.val.app (op (Over.mk (𝟙 U))) t
  have hcancel : τ.hom.val.app (op (Over.mk (𝟙 U))) a = t :=
    congrArg (fun g : (cartierDivisorModule X D).over U ⟶
      (cartierDivisorModule X D).over U =>
        g.val.app (op (Over.mk (𝟙 U))) t) τ.inv_hom_id
  have hfield : rationalFunctionModuleSectionsEquiv X U
      (τ.hom.val.app (op (Over.mk (𝟙 U))) a).val =
      X.germToFunctionField U a * (↑(f⁻¹) : X.functionField) :=
    cartierEquationSectionEquivOn_apply_field X D U f hf (Over.mk (𝟙 U)) a
  rw [hcancel] at hfield
  have hvalue : rationalFunctionModuleSectionsEquiv X U t.val =
      cartierGlobalSectionRationalValue X D s :=
    cartierGlobalSectionRationalValue_restrict X D s U
  change X.germToFunctionField U a = _
  calc
    X.germToFunctionField U a =
        (X.germToFunctionField U a * (↑(f⁻¹) : X.functionField)) * (f : X.functionField) := by
      simp [mul_assoc]
    _ = cartierGlobalSectionRationalValue X D s * (f : X.functionField) := by
      rw [← hfield, hvalue]
    _ = (f : X.functionField) * cartierGlobalSectionRationalValue X D s := mul_comm _ _

/-- A globally generated original invertible sheaf has an effective
Cartier representative whose support avoids any prescribed point. -/
theorem exists_effectiveCartier_avoiding_point (L : InvertibleSheaf X)
    (hL : Positivity.IsGloballyGenerated L.obj) (x : X) :
    ∃ (E : CartierDivisor X) (hE : HasRegularCartierEquations X E),
      x ∉ (effectiveCartierIdealDataOfRegularEquations X E hE).support ∧
        Nonempty (cartierDivisorModule X E ≅ L.obj) := by
  obtain ⟨D, ⟨e⟩⟩ := exists_cartierDivisor_module_iso X L.obj
  have hD : Positivity.IsGloballyGenerated (cartierDivisorModule X D) := by
    obtain ⟨I, φ, hφ⟩ := hL
    letI := hφ
    exact ⟨I, φ ≫ e.hom, inferInstance⟩
  obtain ⟨U, i, hxU, f, hf⟩ := exists_local_cartier_equation X ⊤ D x trivial
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hi : i = homOfLE (le_top : U ≤ ⊤) := Subsingleton.elim _ _
  have hf' : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op D := by
    simpa only [hi] using hf
  let τ := cartierEquationOverIso X D U f hf'
  obtain ⟨s, hs, hunit⟩ := GloballyGeneratedUnitCoefficient.exists_section_unit_coefficient
    hD U x hxU τ.symm
  let q : X.functionFieldˣ := Units.mk0 (cartierGlobalSectionRationalValue X D s)
    (cartierGlobalSectionRationalValue_ne_zero X D s hs)
  let E := D + principalCartierDivisorHom X (Additive.ofMul q)
  have hE : HasRegularCartierEquations X E :=
    cartierPrincipalShift_hasRegularEquations X D s q rfl
  let a : Γ(X, U) := τ.inv.val.app (op (Over.mk (𝟙 U)))
    ((cartierDivisorModule X D).val.map (homOfLE (le_top : U ≤ ⊤)).op s)
  let c : RegularCartierEquationChart X E := {
    chart := {
      openSet := U
      nonempty := inferInstance
      equation := f * q
      represents := cartierGlobalEquation_mul X D
        (principalCartierDivisorHom X (Additive.ofMul q)) U f q hf'
        (principalCartierDivisor_equation X q U) }
    coefficient := a
    germ_eq := frame_coefficient_functionField X D U f hf' s }
  refine ⟨E, hE, ?_, ⟨cartierPrincipalShiftIso X D q ≪≫ e.symm⟩⟩
  intro hmem
  exact (NormalProjectiveSurface.PrimeCurve.mem_support_iff_not_isUnit_germ
    E hE c x hxU).1 hmem hunit

end KltDP.Geometry.GloballyGeneratedEffectiveCartier
