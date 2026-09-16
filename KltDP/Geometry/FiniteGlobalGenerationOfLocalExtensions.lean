import KltDP.Geometry.GlobalGenerationOfLocalExtensions

/-!
# Finite original global generators from finite local generators

The original sheaf-gluing epimorphism retains a finite index: choose one
global extension for each of the finitely many original local generators.
No affineness, coherence, or additional presentation is assumed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.FiniteGlobalGenerationOfLocalExtensions

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open GlobalGenerationOfLocalExtensions

variable {X : Scheme.{u}}

/-- Extending a finite original generating family on a finite cover gives
an actual finite original global generating family. -/
theorem exists_finite_generatingSections (M : X.Modules)
    {I : Type u} [Finite I] (U : I → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (G : ∀ i, (M.over (U i)).GeneratingSections)
    (hfinite : ∀ i, Finite (G i).I)
    (hG : ∀ i, ∀ k : (G i).I, ∃ t : M.val.obj (op (⊤ : X.Opens)),
      M.val.map (homOfLE (show U i ≤ ⊤ from le_top)).op t =
        ((G i).s k).val (op (Over.mk (𝟙 (U i))))) :
    ∃ H : M.GeneratingSections, Finite H.I := by
  classical
  choose t ht using hG
  letI (i : I) : Finite (G i).I := hfinite i
  let J := Σ i : I, (G i).I
  let T : J → M.sections := fun j => sectionOfTop M (t j.1 j.2)
  have hT : Epi (M.freeHomEquiv.symm T) :=
    epi_of_generator_extensions M U hcover G T (by
      intro i k
      exact ⟨⟨i, k⟩, ht i k⟩)
  let H : M.GeneratingSections := { I := J, s := T, epi := hT }
  exact ⟨H, inferInstanceAs (Finite J)⟩

end KltDP.Geometry.FiniteGlobalGenerationOfLocalExtensions
