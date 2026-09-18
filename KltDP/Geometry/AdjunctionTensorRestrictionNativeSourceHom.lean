import KltDP.Geometry.AdjunctionTensorRestrictionRingCharts

/-!
# Fold only the two literal source isomorphisms of the stored equation

The original equation supplies both isomorphisms and every object annotation.
No replacement base-map proof, ring morphism, or source presentation is built.
The native projection carrier check matched all eight stored annotations.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.AdjunctionTensorRestrictionNativeSourceHom

private theorem fold_native_source {C : Type*} [Category C] {S P U T : C}
    {e : S ≅ P} {e' : P ≅ U} {l : S ⟶ T} {a : U ⟶ T}
    (h : l = (e.hom ≫ e'.hom) ≫ a) : l = (e ≪≫ e').hom ≫ a :=
  h.trans (congrArg (fun q => q ≫ a) (Iso.trans_hom e e').symm)

/-- The same original ring equation, with its two native source isomorphisms grouped. -/
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
    fold_native_source
      (AdjunctionTensorRestrictionRingCharts.ring_square R hφ
        d hJ hd hJ' hd' e hE he hTower hA hB hQ hQ' hOpen)

end KltDP.Geometry.AdjunctionTensorRestrictionNativeSourceHom
