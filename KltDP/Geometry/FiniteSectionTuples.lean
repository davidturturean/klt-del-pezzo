import KltDP.Geometry.FiniteNonvanishingGenerators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.EquivFin

/-!
# A finite tuple of original global sections covering a quasi-compact scheme

Choose a finite subcover from the original generating sections, adjoin a
zero section, and enumerate the resulting nonempty finite index. This
also handles the empty scheme and an empty original generator family.
The resulting tuple has the projective-coordinate index Fin (n + 1).
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.FiniteSectionTuples

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

/-- A finite tuple of original global generators, with an additional zero
section, covers the original quasi-compact scheme by nonvanishing opens. -/
theorem exists_tuple_of_generatingSections (hX : IsCompact (Set.univ : Set X))
    (G : L.obj.GeneratingSections) :
    ∃ (n : ℕ) (s : Fin (n + 1) → L.obj.sections),
      (⨆ i, nonvanishingOpen X L (s i)) = ⊤ := by
  classical
  obtain ⟨S, hS⟩ := FiniteNonvanishingGenerators.exists_finite_nonvanishing_subcover L hX G
  let e : Option ↥S ≃ Fin (Fintype.card ↥S + 1) :=
    (Fintype.equivFin (Option ↥S)).trans (finCongr Fintype.card_option)
  let t : Option ↥S → L.obj.sections
    | none => L.obj.unitHomEquiv 0
    | some j => G.s j.val
  let s : Fin (Fintype.card ↥S + 1) → L.obj.sections := fun j => t (e.symm j)
  refine ⟨Fintype.card ↥S, s, top_unique ?_⟩
  intro x hx
  have hxS : x ∈ ⨆ a : S, nonvanishingOpen X L (G.s a.val) := by
    rw [hS]
    trivial
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hxS
  refine Opens.mem_iSup.mpr ⟨e (some a), ?_⟩
  change x ∈ nonvanishingOpen X L (t (e.symm (e (some a))))
  rw [Equiv.symm_apply_apply]
  exact ha

/-- Global generation alone supplies the finite projective-coordinate tuple. -/
theorem exists_tuple_of_globallyGenerated (hX : IsCompact (Set.univ : Set X))
    (hL : Positivity.IsGloballyGenerated L.obj) :
    ∃ (n : ℕ) (s : Fin (n + 1) → L.obj.sections),
      (⨆ i, nonvanishingOpen X L (s i)) = ⊤ := by
  obtain ⟨I, φ, hφ⟩ := hL
  letI := hφ
  exact exists_tuple_of_generatingSections L hX
    ((_root_.SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).ofEpi φ)

end KltDP.Geometry.FiniteSectionTuples
