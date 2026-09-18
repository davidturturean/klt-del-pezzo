import KltDP.Geometry.NormalTwistedAdjunctionTensorChart
import KltDP.Geometry.NormalTwistedAdjunctionChartRestriction
import KltDP.Geometry.AffineModuleTildeTensorPullbackRestriction

/-!
# The original sheaf-tensor adjunction chart respects the actual restriction

Compose the original scheme Kähler chart square with the original extended
tensor comparison square. The two target components retain the original
ambient top-form and normal-module restriction maps. The ambient component
is still expressed through the original affine pullback isomorphisms; its
identification with the global ambient restriction is a separate obligation.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u
namespace KltDP.Geometry.NormalTwistedAdjunctionTensorChartRestriction

open KltDP.RingTheory.SmoothPrincipalDeterminantRestriction
open KltDP.RingTheory.NormalTwistedAdjunctionRestriction
open AffineModuleTildeSemilinearMap SchemeKaehlerSheaf SchemeKaehlerOpenRestriction

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem compose_squares {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {S T U : C} {S' T' U' : D}
    (a : S ⟶ T) (b : T ⟶ U) (a' : S' ⟶ T') (b' : T' ⟶ U')
    (s : F.obj S ⟶ S') (t : F.obj T ⟶ T') (v : F.obj U ⟶ U')
    (ha : F.map a ≫ t = s ≫ a') (hb : F.map b ≫ v = t ≫ b') :
    F.map (a ≫ b) ≫ v = s ≫ a' ≫ b' := by
  rw [F.map_comp, Category.assoc, hb, ← Category.assoc, ha, Category.assoc]

private theorem compose_squares_middle_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {S T U : C} {S' T' U' : D}
    (a : S ⟶ T) (b : T ⟶ U) (a' : S' ⟶ T') (b' : T' ⟶ U')
    (s : F.obj S ⟶ S') (t₁ t₂ : F.obj T ⟶ T') (v : F.obj U ⟶ U')
    (ha : F.map a ≫ t₁ = s ≫ a') (hb : F.map b ≫ v = t₂ ≫ b')
    (ht : t₂ = t₁) : F.map (a ≫ b) ≫ v = s ≫ a' ≫ b' :=
  compose_squares F a b a' b' s t₁ v ha
    (hb.trans (congrArg (fun t => t ≫ b') ht))

private theorem associate_base_maps
    {C : Type*} [Category C] {S P Q T : C}
    {r : S ⟶ T} {p : S ⟶ P} {q : P ⟶ Q} {a : Q ⟶ T}
    (h : r = p ≫ q ≫ a) : r = (p ≫ q) ≫ a :=
  h.trans (Category.assoc p q a).symm

variable (R A A' : Type u) [CommRing R] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
  (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))
  (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)
  (hJ' : Ideal.span {(mappedEquation A A' J J' hφ d : A')} = J')
  (hd' : (mappedEquation A A' J J' hφ d : A') ∈ nonZeroDivisors A')

/-- The original ambient and normal restrictions through the actual sheaf tensor. -/
def restrictionMap :=
  AffineModuleTildeTensorPullbackRestriction.componentRestriction
    (Ideal.Quotient.mk J) (Ideal.Quotient.mk J') (quotientMap A A' J J' hφ)
    (M := ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A)))
    (N := NormalTwistedAdjunctionTensorChart.normalModule A J)
    (M' := ModuleCat.of A' (⋀[A']^2 (KaehlerDifferential R A')))
    (N' := NormalTwistedAdjunctionTensorChart.normalModule A' J')
    (KltDP.RingTheory.SmoothPrincipalTopFormRestriction.ambientTopTensorMap R A A' J J' hφ)
    (normalRestriction A A' J J' hφ d hJ hd hJ' hd')

private theorem tensor_map_eq (R A A' : Type u)
    [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))
    (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)
    (hJ' : Ideal.span {(mappedEquation A A' J J' hφ d : A')} = J')
    (hd' : (mappedEquation A A' J J' hφ d : A') ∈ nonZeroDivisors A') :
    AffineModuleTildeTensorPullbackRestriction.tensorRestriction
      (Ideal.Quotient.mk J) (Ideal.Quotient.mk J') (quotientMap A A' J J' hφ)
      (M := ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A)))
      (N := NormalTwistedAdjunctionTensorChart.normalModule A J)
      (M' := ModuleCat.of A' (⋀[A']^2 (KaehlerDifferential R A')))
      (N' := NormalTwistedAdjunctionTensorChart.normalModule A' J')
      (KltDP.RingTheory.SmoothPrincipalTopFormRestriction.ambientTopTensorMap R A A' J J' hφ)
      (normalRestriction A A' J J' hφ d hJ hd hJ' hd') =
    twistedRestriction R A A' J J' hφ d hJ hd hJ' hd' := rfl

private def middle_map_eq (R A A' : Type u)
    [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))
    (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)
    (hJ' : Ideal.span {(mappedEquation A A' J J' hφ d : A')} = J')
    (hd' : (mappedEquation A A' J J' hφ d : A') ∈ nonZeroDivisors A') :=
  congrArg (pullbackMap (quotientMap A A' J J' hφ)
    (M := AffineModuleTildeTensorPullback.tensorModule (Ideal.Quotient.mk J)
      (ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A)))
      (NormalTwistedAdjunctionTensorChart.normalModule A J))
    (N := AffineModuleTildeTensorPullback.tensorModule (Ideal.Quotient.mk J')
      (ModuleCat.of A' (⋀[A']^2 (KaehlerDifferential R A')))
      (NormalTwistedAdjunctionTensorChart.normalModule A' J')))
    (tensor_map_eq R A A' J J' hφ d hJ hd hJ' hd')

private def tensor_square_proof (R A A' : Type u)
    [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))
    (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)
    (hJ' : Ideal.span {(mappedEquation A A' J J' hφ d : A')} = J')
    (hd' : (mappedEquation A A' J J' hφ d : A') ∈ nonZeroDivisors A') :=
  AffineModuleTildeTensorPullbackRestriction.iso_hom_pullback_square
    (Ideal.Quotient.mk J) (Ideal.Quotient.mk J') (quotientMap A A' J J' hφ)
    (M := ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A)))
    (N := NormalTwistedAdjunctionTensorChart.normalModule A J)
    (M' := ModuleCat.of A' (⋀[A']^2 (KaehlerDifferential R A')))
    (N' := NormalTwistedAdjunctionTensorChart.normalModule A' J')
    (KltDP.RingTheory.SmoothPrincipalTopFormRestriction.ambientTopTensorMap R A A' J J' hφ)
    (normalRestriction A A' J J' hφ d hJ hd hJ' hd')

private def iso_restriction_proof (R A A' : Type u)
    [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))
    (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)
    (hJ' : Ideal.span {(mappedEquation A A' J J' hφ d : A')} = J')
    (hd' : (mappedEquation A A' J J' hφ d : A') ∈ nonZeroDivisors A')
    [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
    [Algebra.IsStandardSmoothOfRelativeDimension 2 R A']
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A' ⧸ J')]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (quotientMap A A' J J' hφ)))] :=
  compose_squares_middle_eq (schemeModulePullback
      (Spec.map (CommRingCat.ofHom (quotientMap A A' J J' hφ))))
    _ _ _ _ _ _ _ _
    (associate_base_maps
      (NormalTwistedAdjunctionChartRestriction.iso_restriction R A A' J J' hφ d hJ hd hJ' hd'))
    (tensor_square_proof R A A' J J' hφ d hJ hd hJ' hd')
    (middle_map_eq R A A' J J' hφ d hJ hd hJ' hd')

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

variable [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
  [Algebra.IsStandardSmoothOfRelativeDimension 2 R A']
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A' ⧸ J')]
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom (quotientMap A A' J J' hφ)))]

/-- The original sheaf-tensor adjunction isomorphism commutes with the actual
scheme Kähler pullback and original component restrictions. Its inferred
proposition unfolds only the two original tensor-chart isomorphisms. -/
theorem iso_restriction :
    statementOf (iso_restriction_proof R A A' J J' hφ d hJ hd hJ' hd') :=
  iso_restriction_proof R A A' J J' hφ d hJ hd hJ' hd'

end KltDP.Geometry.NormalTwistedAdjunctionTensorChartRestriction
