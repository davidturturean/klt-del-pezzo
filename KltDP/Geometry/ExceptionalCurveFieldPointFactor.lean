import KltDP.Geometry.Resolution
import KltDP.Geometry.PrimeCurvePointFiberFactorization

/-!
The original exceptional-curve predicate gives a field-point factorization
of the original curve morphism. The factorization follows from the proved
constant-morphism theorem for proper reduced connected curves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]
  {X Y : NormalProjectiveSurface k}

/-- A topologically contracted original prime factors through an actual
field point over the original structure morphisms. -/
theorem IsExceptionalCurve.exists_fieldPoint_factor
    (π : X.toScheme ⟶ Y.toScheme)
    (hπ : π ≫ Y.structureMorphism = X.structureMorphism)
    (C : X.PrimeCurve) (hC : IsExceptionalCurve π C) :
    ∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
      C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _ := by
  obtain ⟨y, hy⟩ := hC
  have hbase : ∀ x ∈ (C : Set X.toScheme), π.base x = y := by
    intro x hx
    have hmem := Set.mem_image_of_mem π.base hx
    rw [hy] at hmem
    exact hmem
  obtain ⟨p, hp, hpk, _⟩ :=
    PrimeCurvePointFiberFactorization.exists_factor_of_constant
      X C Y.structureMorphism π hπ y hbase
  exact ⟨p, hp, hpk⟩

end KltDP.Geometry
