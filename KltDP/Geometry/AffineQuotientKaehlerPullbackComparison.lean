import KltDP.Geometry.AffineKaehlerPullbackComparison
import KltDP.RingTheory.SmoothPrincipalDeterminantRestriction

/-!
# The original quotient differential restriction through original scheme pullback

The native quotient differential is the already compiled affine differential
under the original quotient scalar tower. Replace only that native map in
the proved affine square. Its original forward scheme map remains at the
already checked inferred type; no new comparison or compatibility is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.AffineQuotientKaehlerPullbackComparison

open KltDP.RingTheory.SmoothPrincipalDeterminantRestriction
open AffineModuleTildeSemilinearMap SchemeKaehlerSheaf SchemeKaehlerOpenRestriction

private theorem replace_right_factor {C : Type*} [Category C] {X Y Z : C}
    (a : X ⟶ Y) {b b' : Y ⟶ Z} {c : X ⟶ Z}
    (hb : b = b') (h : a ≫ b' = c) : a ≫ b = c :=
  (congrArg (fun t => a ≫ t) hb).trans h

variable (R A A' : Type u) [CommRing R] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
  (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))

/-- The original quotient scheme map is over the original base ring. -/
theorem quotientBaseMap_comp :
    Spec.map (CommRingCat.ofHom (quotientMap A A' J J' hφ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ J))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (A' ⧸ J'))) := by
  letI : Algebra (A ⧸ J) (A' ⧸ J') := (quotientMap A A' J J' hφ).toAlgebra
  letI : IsScalarTower R (A ⧸ J) (A' ⧸ J') := quotientMapTowerR R A A' J J' hφ
  exact AffineKaehlerPullbackComparison.baseMap_comp R (A ⧸ J) (A' ⧸ J')

/-- The two native semilinear maps are the same original map of differentials. -/
private theorem nativeDifferential_eq :
    letI : Algebra (A ⧸ J) (A' ⧸ J') := (quotientMap A A' J J' hφ).toAlgebra
    letI : IsScalarTower R (A ⧸ J) (A' ⧸ J') := quotientMapTowerR R A A' J J' hφ
    quotientDifferentialMap R A A' J J' hφ =
      AffineKaehlerPullbackComparison.differentialMap R (A ⧸ J) (A' ⧸ J') := by
  letI : Algebra (A ⧸ J) (A' ⧸ J') := (quotientMap A A' J J' hφ).toAlgebra
  letI : IsScalarTower R (A ⧸ J) (A' ⧸ J') := quotientMapTowerR R A A' J J' hφ
  ext m
  rfl

/-- Apply the original semilinear-to-sheaf map before composing any scheme square. -/
private def nativeSheafMap_eq (R A A' : Type u)
    [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A')) :=
  letI : Algebra (A ⧸ J) (A' ⧸ J') := (quotientMap A A' J J' hφ).toAlgebra
  letI : IsScalarTower R (A ⧸ J) (A' ⧸ J') := quotientMapTowerR R A A' J J' hφ
  congrArg (pullbackMap (quotientMap A A' J J' hφ)
    (M := AffineKaehlerTildeDerivation.differentialModule R (A ⧸ J))
    (N := AffineKaehlerTildeDerivation.differentialModule R (A' ⧸ J')))
    (nativeDifferential_eq R A A' J J' hφ)

private def quotientDifferential_square_proof (R A A' : Type u)
    [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (quotientMap A A' J J' hφ)))] :=
  letI : Algebra (A ⧸ J) (A' ⧸ J') := (quotientMap A A' J J' hφ).toAlgebra
  letI : IsScalarTower R (A ⧸ J) (A' ⧸ J') := quotientMapTowerR R A A' J J' hφ
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ J) (A' ⧸ J')))) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (quotientMap A A' J J' hφ)))
    infer_instance
  replace_right_factor
    ((schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap A A' J J' hφ)))).map
      (AffineKaehlerTildeLocalization.iso R (A ⧸ J)).hom)
    (nativeSheafMap_eq R A A' J J' hφ)
    (AffineKaehlerPullbackComparison.pullback_square R (A ⧸ J) (A' ⧸ J'))

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

variable [IsOpenImmersion (Spec.map (CommRingCat.ofHom (quotientMap A A' J J' hφ)))]

/-- The actual quotient differential restriction commutes with the original affine
Kähler isomorphisms and the original open-immersion pullback map. The transparent
inferred proposition retains the original quotient map and differential map. -/
theorem quotientDifferential_square :
    statementOf (quotientDifferential_square_proof R A A' J J' hφ) :=
  quotientDifferential_square_proof R A A' J J' hφ

end KltDP.Geometry.AffineQuotientKaehlerPullbackComparison
