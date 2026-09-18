import KltDP.Geometry.RationalDifferentialSquareValueComp

/-!
# Evaluating an existing open square with abstract module objects

Eliminate the actual nonempty-open witness before specializing the module
objects to canonical differential sheaves. This preserves the original maps
and the original square while keeping dependent elimination small.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.RationalDifferentialSquareValue

open OpenImmersionRational

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance existsSquareOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- The existing open square determines the value of every original section. -/
theorem field_value_of_exists_open_square_comp
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ X) [GenericPointPreserving p]
    (M : X.Modules) (N : Y.Modules)
    (d : (schemeModulePullback p).obj M ⟶ N)
    (b : N ⟶ rationalFunctionModule Y)
    (c : M ⟶ rationalFunctionModule X)
    (h : ∃ (Z : Y.Opens) (hne : Nonempty Z.toScheme),
      letI : Nonempty Z.toScheme := hne
      letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
      ∃ ht : IsOpenImmersion (Z.ι ≫ p),
        letI : IsOpenImmersion (Z.ι ≫ p) := ht
        (schemeModulePullback Z.ι).map (d ≫ b) ≫ (rationalModulePullbackIso Z.ι).hom =
          (schemeModulePullbackCompIso Z.ι p).hom.app M ≫
            (schemeModulePullback (Z.ι ≫ p)).map c ≫
              (rationalModulePullbackIso (Z.ι ≫ p)).hom)
    (U : X.Opens) [Nonempty U] (s : M.val.obj (op U)) :
    rationalFunctionModuleSectionsEquiv Y (p ⁻¹ᵁ U)
        (b.val.app (op (p ⁻¹ᵁ U))
          (d.val.app (op (p ⁻¹ᵁ U)) (pullbackSection p M U s))) =
      functionFieldMap p
        (rationalFunctionModuleSectionsEquiv X U (c.val.app (op U) s)) := by
  obtain ⟨Z, hne, ht, hsquare⟩ := h
  letI := hne
  letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
  letI := ht
  exact field_value_of_open_square_comp p Z.ι M N d b c hsquare U s

end KltDP.Geometry.RationalDifferentialSquareValue

#print axioms KltDP.Geometry.RationalDifferentialSquareValue.field_value_of_exists_open_square_comp
