import KltDP.Geometry.CartierDivisorTrivialization

/-!
# An original Cartier-module map on an actual equation chart

The existing equation-section linear equivalence writes every section as a
regular multiple of the original frame 1/f. Linearity then computes the
actual rational value of a module map from its value on that same frame.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierModuleIsoMultiplier

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)
    (a : cartierDivisorModule X D ⟶ rationalFunctionModule X)

/-- The original function-field value of the actual image section. -/
def value (U : X.Opens) [Nonempty U]
    (s : (cartierDivisorModule X D).val.obj (op U)) : X.functionField :=
  rationalFunctionModuleSectionsEquiv X U (a.val.app (op U) s)

/-- Actual linearity is multiplication by the original regular-function germ. -/
theorem value_smul (U : X.Opens) [Nonempty U] (r : Γ(X, U))
    (s : (cartierDivisorModule X D).val.obj (op U)) :
    value X D a U (r • s) =
      (X.germToFunctionField U).hom r * value X D a U s := by
  unfold value
  rw [((a.val.app (op U)).hom).map_smul, LinearEquiv.map_smul]
  rfl

/-- The value retains the actual module-map restriction square. -/
theorem value_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : V ⟶ U) (s : (cartierDivisorModule X D).val.obj (op U)) :
    value X D a V ((cartierDivisorModule X D).val.map i.op s) =
      value X D a U s := by
  unfold value
  rw [_root_.PresheafOfModules.naturality_apply a.val i.op s,
    rationalFunctionModuleSectionsEquiv_naturality X i (a.val.app (op U) s)]

/-- On an original equation chart, the map is multiplication by its actual
frame value times the original equation f. No multiplier is an input. -/
theorem value_eq_frame_multiplier (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op D)
    (s : (cartierDivisorModule X D).val.obj (op U)) :
    value X D a U s =
      (value X D a U ((cartierEquationSectionEquiv X D U f hf) 1) *
          (f : X.functionField)) * rationalFunctionModuleSectionsEquiv X U s.val := by
  let t := cartierEquationSectionEquiv X D U f hf
  let r : Γ(X, U) := t.symm s
  have hs : r • t 1 = s := by
    calc
      _ = t (r * 1) := (t.map_smul r (1 : Γ(X, U))).symm
      _ = s := by
        rw [mul_one]
        exact t.apply_symm_apply s
  have hv : rationalFunctionModuleSectionsEquiv X U s.val =
      (X.germToFunctionField U).hom r * (↑(f⁻¹) : X.functionField) := by
    exact (congrArg (fun z : (cartierDivisorModule X D).val.obj (op U) =>
      rationalFunctionModuleSectionsEquiv X U z.val)
        (t.apply_symm_apply s).symm).trans
      (cartierEquationSectionEquiv_apply_field X D U f hf r)
  have ha : value X D a U s =
      (X.germToFunctionField U).hom r * value X D a U (t 1) :=
    (congrArg (value X D a U) hs.symm).trans (value_smul X D a U r (t 1))
  have hfinv : (f : X.functionField) * (↑(f⁻¹) : X.functionField) = 1 :=
    congrArg Units.val (mul_inv_cancel f)
  rw [ha, hv]
  change (X.germToFunctionField U).hom r * value X D a U (t 1) =
    (value X D a U (t 1) * (f : X.functionField)) *
      ((X.germToFunctionField U).hom r * (↑(f⁻¹) : X.functionField))
  calc
    _ = ((X.germToFunctionField U).hom r * value X D a U (t 1)) *
        ((f : X.functionField) * (↑(f⁻¹) : X.functionField)) := by rw [hfinv, mul_one]
    _ = _ := by ring

end KltDP.Geometry.CartierModuleIsoMultiplier

#check @KltDP.Geometry.CartierModuleIsoMultiplier.value_eq_frame_multiplier
#print axioms KltDP.Geometry.CartierModuleIsoMultiplier.value_eq_frame_multiplier
