import KltDP.Geometry.NormalizedFrameDifferentialSquare
import KltDP.Geometry.RationalDifferentialSquareValueComp

/-!
# The original pulled differential section in a normalized frame

The actual normalization witness supplies the open square. Evaluating that
proved square gives the exact original function-field value of every
original differential section pulled through the original morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.NormalizedFrameDifferentialValue

open NormalModelCanonical CartierRationalCoordinate

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance targetOpenIntegral {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

/-- A normalized frame evaluates the literal original differential pullback
by the original function-field map. Its rational value is proved, not supplied. -/
theorem field_value
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (U : X.toScheme.Opens) [Nonempty U.toScheme]
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    {V : Scheme.{u}} [IsIntegral V] (v : V ⟶ X.toScheme) (x : V)
    (F : LocalFrame (v ≫ X.structureMorphism) x)
    (hF : IsNormalized X U KU eKU v x F)
    (p : F.neighborhood ⟶ U.toScheme) [GenericPointPreserving p]
    (hp : p ≫ U.ι = F.toModel ≫ v)
    (T : U.toScheme.Opens) [Nonempty T]
    (s : (SmoothCanonicalExteriorComparison.relativeDifferentialExterior
      (U.ι ≫ X.structureMorphism) 2).val.obj (op T)) :
    let sU := U.ι ≫ X.structureMorphism
    let sF := F.toModel ≫ (v ≫ X.structureMorphism)
    let hpbase : p ≫ sU = sF := by
      simpa only [Category.assoc] using congrArg (fun a => a ≫ X.structureMorphism) hp
    rationalFunctionModuleSectionsEquiv F.neighborhood (p ⁻¹ᵁ T)
      ((coordinate F.neighborhood F.divisor
          (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sF 2)
          F.canonicalIso).val.app (op (p ⁻¹ᵁ T))
        ((SchemeKaehlerExteriorPullbackTransport.map sU p sF hpbase 2).val.app
          (op (p ⁻¹ᵁ T)) (pullbackSection p
            (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sU 2) T s))) =
      functionFieldMap p
        (rationalFunctionModuleSectionsEquiv U.toScheme T
          ((coordinate U.toScheme KU
            (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sU 2)
            eKU).val.app (op T) s)) := by
  obtain ⟨Z, hne, ht, hsquare⟩ :=
    NormalizedFrameDifferentialSquare.exists_original_differential_coordinate_square
      X U KU eKU v x F hF p hp
  letI := hne
  letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
  letI := ht
  exact RationalDifferentialSquareValue.field_value_of_open_square_comp p Z.ι
    (SmoothCanonicalExteriorComparison.relativeDifferentialExterior
      (U.ι ≫ X.structureMorphism) 2) _ _ _ _ hsquare T s

end KltDP.Geometry.NormalizedFrameDifferentialValue

#check @KltDP.Geometry.NormalizedFrameDifferentialValue.field_value
#print axioms KltDP.Geometry.NormalizedFrameDifferentialValue.field_value
