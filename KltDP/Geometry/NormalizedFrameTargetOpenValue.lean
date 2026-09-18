import KltDP.Geometry.NormalizedFrameTargetOpenSquare
import KltDP.Geometry.RationalDifferentialExistsSquareValue

/-!
# The actual differential value on an open chart of the target reference

The chart divisor and canonical identification are the original normalized
pullbacks. The original normalization predicate supplies the square, and
the original adjunction and field maps evaluate it on every actual section.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.NormalizedFrameTargetOpenValue

open NormalModelCanonical CartierRationalCoordinate

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance targetOpenIntegral {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

local instance openGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- Every actual target-chart differential section has the original field
pullback as its value in the existing normalized model frame. -/
theorem field_value
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (U : X.toScheme.Opens) [Nonempty U.toScheme]
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    {A : Scheme.{u}} [IsIntegral A] (i : A ⟶ U.toScheme) [IsOpenImmersion i]
    (sA : A ⟶ Spec (CommRingCat.of k))
    (hi : i ≫ (U.ι ≫ X.structureMorphism) = sA)
    {V : Scheme.{u}} [IsIntegral V] (v : V ⟶ X.toScheme) (x : V)
    (F : LocalFrame (v ≫ X.structureMorphism) x)
    (hF : IsNormalized X U KU eKU v x F)
    (q : F.neighborhood ⟶ A) [GenericPointPreserving q]
    (hq : (q ≫ i) ≫ U.ι = F.toModel ≫ v)
    (T : A.Opens) [Nonempty T]
    (s : (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2).val.obj
      (op T)) :
    let sF := F.toModel ≫ (v ≫ X.structureMorphism)
    let hqbase : q ≫ sA = sF := by
      rw [← hi]
      simpa only [Category.assoc] using
        congrArg (fun a => a ≫ X.structureMorphism) hq
    let DA := DominantCartierPullback.pullbackHom i KU
    let eDA := canonicalOpenPullbackIso i (U.ι ≫ X.structureMorphism) sA hi KU eKU
    rationalFunctionModuleSectionsEquiv F.neighborhood (q ⁻¹ᵁ T)
      ((coordinate F.neighborhood F.divisor
          (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sF 2)
          F.canonicalIso).val.app (op (q ⁻¹ᵁ T))
        ((SchemeKaehlerExteriorPullbackTransport.map sA q sF hqbase 2).val.app
          (op (q ⁻¹ᵁ T)) (pullbackSection q
            (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) T s))) =
      functionFieldMap q
        (rationalFunctionModuleSectionsEquiv A T
          ((coordinate A DA
            (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2)
            eDA).val.app (op T) s)) := by
  exact RationalDifferentialSquareValue.field_value_of_exists_open_square_comp q
    (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) _ _ _ _
    (NormalizedFrameTargetOpenSquare.exists_original_differential_coordinate_square
      X U KU eKU i sA hi v x F hF q hq) T s

end KltDP.Geometry.NormalizedFrameTargetOpenValue

#check @KltDP.Geometry.NormalizedFrameTargetOpenValue.field_value
#print axioms KltDP.Geometry.NormalizedFrameTargetOpenValue.field_value
