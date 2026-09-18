import KltDP.Geometry.NormalTwistedAdjunctionChart
import KltDP.Geometry.NormalTwistedAdjunctionTildeRestriction
import KltDP.Geometry.AffineQuotientKaehlerPullbackComparison

/-!
# Restriction of the original normal-twisted affine adjunction chart

The existing chart isomorphism starts at the actual scheme Kähler sheaf.
Its restriction square follows by composing the original affine Kähler
comparison square with the proved original native adjunction square.
The target retains the actual ambient top-form and normal-module tensor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalTwistedAdjunctionChartRestriction

open KltDP.RingTheory.SmoothPrincipalDeterminantRestriction
open KltDP.RingTheory.NormalTwistedAdjunctionRestriction
open AffineModuleTildeSemilinearMap SchemeKaehlerSheaf SchemeKaehlerOpenRestriction
open NormalTwistedAdjunctionTildeRestriction AffineQuotientKaehlerPullbackComparison

private theorem paste_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P Q S : C} {T U V W : D}
    (a : P ⟶ Q) (u : Q ⟶ S)
    (b : F.obj Q ⟶ T) (t : F.obj S ⟶ W)
    (p : F.obj P ⟶ U) (q : U ⟶ V)
    (a' : V ⟶ T) (u' : T ⟶ W)
    (ha : F.map a ≫ b = p ≫ q ≫ a')
    (hu : F.map u ≫ t = b ≫ u') :
    F.map (a ≫ u) ≫ t = p ≫ q ≫ (a' ≫ u') := by
  rw [F.map_comp, Category.assoc, hu, ← Category.assoc, ha]
  simp only [Category.assoc]

private theorem replace_chart_maps
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P Q S : C} {T U V W : D}
    {s : P ⟶ S} {a : P ⟶ Q} {u : Q ⟶ S}
    {t : F.obj S ⟶ W} {p : F.obj P ⟶ U} {q : U ⟶ V}
    {a' : V ⟶ T} {u' : T ⟶ W} {s' : V ⟶ W}
    (hs : s = a ≫ u) (hs' : s' = a' ≫ u')
    (h : F.map (a ≫ u) ≫ t = p ≫ q ≫ (a' ≫ u')) :
    F.map s ≫ t = p ≫ q ≫ s' := by
  rw [hs, hs']
  exact h

private theorem chart_iso_hom (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] (J : Ideal A)
    [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]
    (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A) :
    (NormalTwistedAdjunctionChart.iso R A J d hJ hd).hom =
      (AffineKaehlerTildeLocalization.iso R (A ⧸ J)).hom ≫
        (AffineModuleTilde.linearEquivIso
          (M := differentialModule R A J) (N := twistedModule R A J)
          (KltDP.RingTheory.NormalTwistedAdjunction.equiv R A J d hJ hd)).hom := rfl

private theorem replace_source_map
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P S : C} {W : D} {a s : P ⟶ S}
    {t : F.obj S ⟶ W} {r : F.obj P ⟶ W}
    (h : F.map a ≫ t = r) (hs : s = a) : F.map s ≫ t = r := by
  rw [hs]
  exact h

private theorem replace_target_map
    {C : Type*} [Category C] {P Q V W : C}
    {p : P ⟶ Q} {q : Q ⟶ V} {a s : V ⟶ W} {r : P ⟶ W}
    (h : r = p ≫ q ≫ a) (hs : s = a) : r = p ≫ q ≫ s := by
  rw [hs]
  exact h

private theorem replace_subsingleton_argument
    {α : Sort*} [Subsingleton α] (P : α → Prop) (a b : α) (h : P a) : P b :=
  Eq.mp (congrArg P (Subsingleton.elim a b)) h

private theorem replace_base_identity
    {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)} {j : Y ⟶ X} [IsOpenImmersion j]
    {g : Y ⟶ Spec (CommRingCat.of k)} {hg : j ≫ f = g}
    {M : Y.Modules} {a : baseRingSheaf g ⟶ M}
    {r : (schemeModulePullback j).obj (baseRingSheaf f) ⟶ M}
    (h : r = (pullbackIso f j).hom ≫
      (eqToIso (congrArg baseRingSheaf hg)).hom ≫ a) (hg' : j ≫ f = g) :
    r = (pullbackIso f j).hom ≫
      (eqToIso (congrArg baseRingSheaf hg')).hom ≫ a :=
  replace_subsingleton_argument
    (fun e : j ≫ f = g => r = (pullbackIso f j).hom ≫
      (eqToIso (congrArg baseRingSheaf e)).hom ≫ a) hg hg' h

private theorem eqToIso_hom_eq
    {C : Type*} [Category C] {X Y : C} (p q : X = Y) :
    (eqToIso p).hom = (eqToIso q).hom :=
  congrArg (fun e : X = Y => (eqToIso e).hom) (Subsingleton.elim p q)

private theorem replace_middle_map
    {C : Type*} [Category C] {P Q V W : C}
    {p : P ⟶ Q} {q q' : Q ⟶ V} {a : V ⟶ W} {r : P ⟶ W}
    (h : r = p ≫ q ≫ a) (hq : q' = q) : r = p ≫ q' ≫ a := by
  rw [hq]
  exact h

private theorem sheaf_map_values {X : Scheme.{u}} {M N : X.Modules}
    {a b : M ⟶ N} (h : a = b) (V : X.Opensᵒᵖ) (s : M.val.obj V) :
    (a.val.app V).hom s = (b.val.app V).hom s :=
  congrArg (fun f : M ⟶ N => (f.val.app V).hom s) h

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
  -- Infer the seven remaining arrows from the two already proved squares.
  paste_square
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap A A' J J' hφ))))
    (AffineKaehlerTildeLocalization.iso R (A ⧸ J)).hom
    _ _ _ _ _ _ _
    (quotientDifferential_square R A A' J J' hφ)
    (NormalTwistedAdjunctionTildeRestriction.iso_restriction R A J A' J' hφ d hJ hd hJ' hd')

private def iso_restriction_source_proof (R A A' : Type u)
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
  replace_source_map
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap A A' J J' hφ))))
    (iso_restriction_proof R A A' J J' hφ d hJ hd hJ' hd')
    (chart_iso_hom R A J d hJ hd)

private def iso_restriction_target_proof (R A A' : Type u)
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
  replace_target_map
    (iso_restriction_source_proof R A A' J J' hφ d hJ hd hJ' hd')
    (chart_iso_hom R A' J' (mappedEquation A A' J J' hφ d) hJ' hd')

private def base_identity_factor_proof (R A A' : Type u)
    [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A')) :=
  letI : Algebra (A ⧸ J) (A' ⧸ J') := (quotientMap A A' J J' hφ).toAlgebra
  letI : IsScalarTower R (A ⧸ J) (A' ⧸ J') := quotientMapTowerR R A A' J J' hφ
  let hg :
      Spec.map (CommRingCat.ofHom (quotientMap A A' J J' hφ)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ J))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (A' ⧸ J'))) :=
    AffineKaehlerPullbackComparison.baseMap_comp R (A ⧸ J) (A' ⧸ J')
  eqToIso_hom_eq
    (congrArg baseRingSheaf (quotientBaseMap_comp R A A' J J' hφ))
    (congrArg baseRingSheaf hg)

private def iso_restriction_chart_proof (R A A' : Type u)
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
  replace_middle_map
    (iso_restriction_target_proof R A A' J J' hφ d hJ hd hJ' hd')
    (base_identity_factor_proof R A A' J J' hφ)

private def iso_restriction_values_proof (R A A' : Type u)
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
  sheaf_map_values (iso_restriction_chart_proof R A A' J J' hφ d hJ hd hJ' hd')

-- Retain the computed dictionaries of the already proved equality's carrier.
local instance quotientSemiring (B : Type u) [CommRing B] (I : Ideal B) :
    Semiring (B ⧸ I) :=
  @CommSemiring.toSemiring (B ⧸ I)
    (@CommRing.toCommSemiring (B ⧸ I) (inferInstance : CommRing (B ⧸ I)))

local instance quotientOpensPreorder (B : Type u) [CommRing B] (I : Ideal B) :
    Preorder (Spec (CommRingCat.of (B ⧸ I))).Opens :=
  @PartialOrder.toPreorder (Spec (CommRingCat.of (B ⧸ I))).Opens
    (@OmegaCompletePartialOrder.toPartialOrder (Spec (CommRingCat.of (B ⧸ I))).Opens
      (inferInstance : OmegaCompletePartialOrder (Spec (CommRingCat.of (B ⧸ I))).Opens))

attribute [local instance] Ideal.instAlgebraQuotient

variable (R A A' : Type u) [CommRing R] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
  (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))
  (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)
  (hJ' : Ideal.span {(mappedEquation A A' J J' hφ d : A')} = J')
  (hd' : (mappedEquation A A' J J' hφ d : A') ∈ nonZeroDivisors A')
  [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
  [Algebra.IsStandardSmoothOfRelativeDimension 2 R A']
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A' ⧸ J')]
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom (quotientMap A A' J J' hφ)))]

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

/-- The original affine adjunction chart commutes with the actual Kähler pullback
and the actual normal-twisted module restriction on the original quotient schemes.
The transparent inferred proposition retains the original chart maps, quotient map,
normal-twisted restriction, and transport along `quotientBaseMap_comp`. -/
theorem iso_restriction :
    statementOf (iso_restriction_chart_proof R A A' J J' hφ d hJ hd hJ' hd') :=
  iso_restriction_chart_proof R A A' J J' hφ d hJ hd hJ' hd'

end KltDP.Geometry.NormalTwistedAdjunctionChartRestriction
