import KltDP.Geometry.GluedAdjunctionAffineNativeCompositeNormalization

/-!
# The literal native Iso projector with abstract object constructors

Keep the category, native-module realization, exterior-object constructor,
and differential-object constructor as independent parameters. The original
source and target annotations are thus normalized before any differential
sheaf is instantiated. This lemma does not cancel the original chart maps.
-/

noncomputable section
open CategoryTheory
universe u v w
namespace KltDP.Geometry.GluedAdjunctionAffineLiteralProjector

/-- Normalize only the native hom projection's measured source and target annotations. -/
theorem hom_heq {R : Type u} [CommRing R]
    (C : CommRingCat.{u} → Type v) [∀ A, Category.{w} (C A)]
    (F : ∀ A : CommRingCat.{u}, ModuleCat.{u} A → C A)
    (G : ∀ A : CommRingCat.{u}, C A → C A)
    (B : ∀ A : CommRingCat.{u}, (R →+* A) → C A)
    (A : CommRingCat.{u}) (φ : R →+* A)
    (V : Type u) [AddCommGroup V] [Module A V] (n : ℕ)
    (e : F (CommRingCat.of A) ((ModuleCat.of A V).exteriorPower n) ≅
      G (CommRingCat.of A) (B (CommRingCat.of A) φ)) :
    HEq
      (@Iso.hom (C A) _
        (F A (ModuleCat.of A (⋀[A]^n V)))
        (G A (B (CommRingCat.of A) φ)) e)
      (@Iso.hom (C A) _
        (F A ((ModuleCat.of A V).exteriorPower n))
        (G A (B A φ)) e) := by
  cases A
  rfl

end KltDP.Geometry.GluedAdjunctionAffineLiteralProjector
