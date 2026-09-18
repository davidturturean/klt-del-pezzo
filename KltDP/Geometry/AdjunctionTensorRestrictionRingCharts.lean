import KltDP.Geometry.AdjunctionTensorRestrictionRingDictionaries

/-!
# Fold the original tensor charts before specializing section rings

The native restriction equation and both tensor-chart folds are combined
over abstract rings. The chosen smaller regular equation is retained as an
explicit argument, using the proved independence of the original chart map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.AdjunctionTensorRestrictionRingCharts

open KltDP.RingTheory.SmoothPrincipalDeterminantRestriction

private theorem fold_tensor_maps {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {S T : C} {S' T' : D}
    {a₀ a : S ⟶ T} {a₀' a' : S' ⟶ T'}
    {s : F.obj S ⟶ S'} {t : F.obj T ⟶ T'}
    (h : F.map a₀ ≫ t = s ≫ a₀') (ha : a₀ = a) (ha' : a₀' = a') :
    F.map a ≫ t = s ≫ a' := by
  cases ha
  cases ha'
  exact h

private def tensor_chart_hom (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (J : Ideal A)
    [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]
    (d : J) (hJ : Ideal.span {(d : A)} = J)
    (hd : (d : A) ∈ nonZeroDivisors A) := by
  have h := Eq.refl ((NormalTwistedAdjunctionTensorChart.iso R A J d hJ hd).hom)
  conv at h =>
    lhs
    unfold NormalTwistedAdjunctionTensorChart.iso
    simp only [Iso.trans_hom]
  exact h

private def tensor_chart_hom_as (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (J : Ideal A)
    [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]
    (d : J) (hJ : Ideal.span {(d : A)} = J)
    (hd : (d : A) ∈ nonZeroDivisors A)
    (e : J) (hE : Ideal.span {(e : A)} = J)
    (he : (e : A) ∈ nonZeroDivisors A) :=
  (tensor_chart_hom R A J d hJ hd).trans
    (congrArg (fun q => q.hom)
      (NormalTwistedAdjunctionTensorChart.iso_eq R A J e hE he d hJ hd))

/-- The original restriction square with both named tensor charts, retaining
the actual chosen smaller equation through the proved equation independence. -/
def ring_square (R : Type u) [CommRing R] {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    {φ : A →+* B} {J : Ideal A} {J' : Ideal B} (hφ : J ≤ J'.comap φ)
    (d : J) (hJ : Ideal.span {(d : A)} = J)
    (hd : (d : A) ∈ nonZeroDivisors A)
    (hJ' : Ideal.span {φ (d : A)} = J')
    (hd' : φ (d : A) ∈ nonZeroDivisors B)
    (e : J') (hE : Ideal.span {(e : B)} = J')
    (he : (e : B) ∈ nonZeroDivisors B) :=
  let _ : Algebra A B := φ.toAlgebra
  fun (hTower : IsScalarTower R A B)
      (hA : Algebra.IsStandardSmoothOfRelativeDimension 2 R A)
      (hB : Algebra.IsStandardSmoothOfRelativeDimension 2 R B)
      (hQ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J))
      (hQ' : Algebra.IsStandardSmoothOfRelativeDimension 1 R (B ⧸ J'))
      (hOpen : IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap J' φ hφ)))) =>
    let _ : IsScalarTower R A B := hTower
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R A := hA
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R B := hB
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J) := hQ
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (B ⧸ J') := hQ'
    fold_tensor_maps
      (AdjunctionTensorRestrictionRingDictionaries.ring_square R hφ
        d hJ hd hJ' hd' hTower hA hB hQ hQ' hOpen)
      (tensor_chart_hom R A J d hJ hd)
      (tensor_chart_hom_as R B J' (mappedEquation A B J J' hφ d) hJ' hd' e hE he)

end KltDP.Geometry.AdjunctionTensorRestrictionRingCharts
