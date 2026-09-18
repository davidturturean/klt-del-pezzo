import KltDP.Geometry.GluedAdjunctionSourceRingMap

/-!
# The two literal quotient-map presentations in the cotangent source word

Keep the category and object constructors abstract while normalizing the
native quotient-map source and the induced-algebra-map intermediate object.
The result is heterogeneous equality, so no concrete pullback carrier is
reconstructed by this lemma.
-/

noncomputable section
open CategoryTheory
universe u v w
namespace KltDP.Geometry.GluedAdjunctionQuotientSourceWord

/-- Normalize the original quotient and induced-algebra presentations before
instantiating the scheme pullback and differential-sheaf constructors. -/
theorem word_heq {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} {J : Ideal A} {J' : Ideal B} (hφ : J ≤ J'.comap φ)
    {C : Type v} [Category.{w} C]
    (P Q : (A ⧸ J →+* B ⧸ J') → C)
    (Open : (A ⧸ J →+* B ⧸ J') → Prop)
    (e : ∀ ψ, Open ψ → (P ψ ≅ Q ψ)) :
    letI : Algebra A B := φ.toAlgebra
    let ψ := KltDP.RingTheory.SmoothPrincipalDeterminantRestriction.quotientMap A B J J' hφ
    let ψA := @algebraMap (A ⧸ J) (B ⧸ J') _ _ ψ.toAlgebra
    ∀ (hA : Open ψA) (hO : Open (Ideal.quotientMap J' φ hφ))
      {T : C} (hBA : Q ψA = T) (hBO : Q (Ideal.quotientMap J' φ hφ) = T),
      HEq
        (@CategoryStruct.comp C _ (P ψ) (Q ψA) T
          (@Iso.hom C _ (P ψ) (Q ψA) (e ψA hA)) (eqToIso hBA).hom)
        ((e (Ideal.quotientMap J' φ hφ) hO).hom ≫ (eqToIso hBO).hom) := by
  intros
  rfl

end KltDP.Geometry.GluedAdjunctionQuotientSourceWord
