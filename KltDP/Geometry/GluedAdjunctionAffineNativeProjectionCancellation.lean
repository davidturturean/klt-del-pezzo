import KltDP.Geometry.GluedAdjunctionAffineLiteralProjector

/-!
# Cancel literal projections with all object constructors still abstract

Unlike the failed concrete-sheaf header, this statement mentions only
independent category and object-constructor variables. It first concludes
HEq of the original arrows; their final homogeneous carrier conversion is
a separate affine consumer.
-/

noncomputable section
open CategoryTheory
universe u v w
namespace KltDP.Geometry.GluedAdjunctionAffineNativeProjectionCancellation

/-- Cancel the literal native projections before specializing any differential sheaf. -/
theorem cancel_abstract_projections {R : Type u} [CommRing R]
    (C : CommRingCat.{u} → Type v) [∀ A, Category.{w} (C A)]
    (F : ∀ A : CommRingCat.{u}, ModuleCat.{u} A → C A)
    (G : ∀ A : CommRingCat.{u}, C A → C A)
    (B : ∀ A : CommRingCat.{u}, (R →+* A) → C A)
    (A : CommRingCat.{u}) (φ : R →+* A)
    (V : Type u) [AddCommGroup V] [Module A V] (n : ℕ)
    (e : F (CommRingCat.of A) ((ModuleCat.of A V).exteriorPower n) ≅
      G (CommRingCat.of A) (B (CommRingCat.of A) φ))
    {S : C A}
    {x : S ⟶ F A (ModuleCat.of A (⋀[A]^n V))}
    {y : S ⟶ F A ((ModuleCat.of A V).exteriorPower n)}
    (h : HEq
      (x ≫ @Iso.hom (C A) _
        (F A (ModuleCat.of A (⋀[A]^n V)))
        (G A (B (CommRingCat.of A) φ)) e)
      (y ≫ @Iso.hom (C A) _
        (F A ((ModuleCat.of A V).exteriorPower n))
        (G A (B A φ)) e)) : HEq x y := by
  cases A
  exact heq_of_eq ((cancel_mono e.hom).mp (eq_of_heq h))

end KltDP.Geometry.GluedAdjunctionAffineNativeProjectionCancellation
