import KltDP.Geometry.CartierModuleHomOnEquation

/-!
# The original frame multiplier on every nonempty open

Nonempty opens of the original integral scheme meet. The actual Cartier
frame restricts to the frame of the same equation on the intersection.
Both the given module map and the original rational coordinates commute
with restriction, so the multiplier computed on one chart works everywhere.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierModuleIsoMultiplier

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)

/-- Restriction carries the actual 1/f frame to the actual 1/f frame
of the same original equation on the smaller open. -/
theorem equationFrame_restrict
    (U V : X.Opens) [Nonempty U] [Nonempty V] (i : V ⟶ U)
    (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op D) :
    (cartierDivisorModule X D).val.map i.op
        ((cartierEquationSectionEquiv X D U f hf) 1) =
      (cartierEquationSectionEquiv X D V f
        (cartierGlobalEquation_restrict X D i f hf)) 1 := by
  apply Subtype.ext
  apply (rationalFunctionModuleSectionsEquiv X V).injective
  change rationalFunctionModuleSectionsEquiv X V
      ((rationalFunctionModule X).val.map i.op
        (((cartierEquationSectionEquiv X D U f hf) 1).val)) = _
  rw [rationalFunctionModuleSectionsEquiv_naturality]
  simp only [cartierEquationSectionEquiv_apply_field, map_one, one_mul]

variable (a : cartierDivisorModule X D ⟶ rationalFunctionModule X)

/-- The multiplier is determined by the given map and the original frame. -/
def multiplier (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op D) :
    X.functionField :=
  value X D a U ((cartierEquationSectionEquiv X D U f hf) 1) * (f : X.functionField)

/-- The value computed from the original frame is unchanged on any
nonempty smaller open carrying that same equation. -/
theorem multiplier_restrict
    (U V : X.Opens) [Nonempty U] [Nonempty V] (i : V ⟶ U)
    (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op D) :
    multiplier X D a V f (cartierGlobalEquation_restrict X D i f hf) =
      multiplier X D a U f hf := by
  unfold multiplier
  rw [← equationFrame_restrict X D U V i f hf, value_restrict]

/-- One original equation chart determines the given morphism's rational
multiplier on every original nonempty open, with no compatibility premise. -/
theorem value_eq_multiplier
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op D)
    (V : X.Opens) [Nonempty V]
    (s : (cartierDivisorModule X D).val.obj (op V)) :
    value X D a V s =
      multiplier X D a U f hf * rationalFunctionModuleSectionsEquiv X V s.val := by
  let W : X.Opens := V ⊓ U
  letI : Nonempty W := ⟨⟨genericPoint X, genericPoint_mem_nonempty_open X V,
    genericPoint_mem_nonempty_open X U⟩⟩
  let iV : W ⟶ V := homOfLE inf_le_left
  let iU : W ⟶ U := homOfLE inf_le_right
  let t := (cartierDivisorModule X D).val.map iV.op s
  have hs : rationalFunctionModuleSectionsEquiv X W t.val =
      rationalFunctionModuleSectionsEquiv X V s.val :=
    rationalFunctionModuleSectionsEquiv_naturality X iV s.val
  calc
    value X D a V s = value X D a W t :=
      (value_restrict X D a iV s).symm
    _ = multiplier X D a W f (cartierGlobalEquation_restrict X D iU f hf) *
        rationalFunctionModuleSectionsEquiv X W t.val :=
      value_eq_frame_multiplier X D a W f
        (cartierGlobalEquation_restrict X D iU f hf) t
    _ = multiplier X D a U f hf * rationalFunctionModuleSectionsEquiv X V s.val :=
      congrArg₂ (· * ·) (multiplier_restrict X D a U W iU f hf) hs

end KltDP.Geometry.CartierModuleIsoMultiplier

#check @KltDP.Geometry.CartierModuleIsoMultiplier.value_eq_multiplier
#print axioms KltDP.Geometry.CartierModuleIsoMultiplier.value_eq_multiplier
