import KltDP.Geometry.SectionLinearCombinations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

/-!
# Nonvanishing of a finite original linear combination

If a finite combination is nonvanishing at a point, at least one original
section is nonvanishing there. In any original frame this is the local
ring fact that its maximal ideal is closed under finite sums.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u v

namespace KltDP.Geometry.SectionLinearCombinations

attribute [local instance] Types.instFunLike Types.instConcreteCategory
open TransitionUnitExtraction InvertibleSectionNonvanishingOpen

private theorem exists_unit_of_sum_unit {R I : Type*} [CommRing R]
    [IsLocalRing R] [Fintype I] (a : I → R) (ha : IsUnit (∑ i, a i)) :
    ∃ i, IsUnit (a i) := by
  classical
  by_contra h
  have hi : ∀ i, a i ∈ IsLocalRing.maximalIdeal R := by
    intro i
    exact fun hui => h ⟨i, hui⟩
  have hs : ∑ i, a i ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.maximalIdeal R).sum_mem (fun i _ => hi i)
  exact hs ha

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
  {I : Type v} [Fintype I] (s : I → L.obj.sections) (a : I → k)

/-- The combination's original nonvanishing open is contained in the union
of the original input sections' nonvanishing opens. -/
theorem nonvanishingOpen_combination_le :
    nonvanishingOpen X L (combination f L.obj s a) ≤
      ⨆ i, nonvanishingOpen X L (s i) := by
  classical
  intro x hx
  let t := L.localTrivializations
  have hcover : x ∈ ⨆ i, t.X i := by
    rw [chartOpens_cover X L.obj t]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hcover
  have hu := (mem_nonvanishingOpen_iff_isUnit_germ X L
    (combination f L.obj s a) t i x hi).mp hx
  change IsUnit (X.presheaf.germ (t.X i) x hi
    (LinearSystemMorphism.coefficient L (combination f L.obj s a) i le_rfl)) at hu
  rw [coefficient_combination, map_sum] at hu
  obtain ⟨j, hj⟩ := exists_unit_of_sum_unit _ hu
  rw [map_mul] at hj
  have hv := isUnit_of_mul_isUnit_right hj
  exact Opens.mem_iSup.mpr ⟨j,
    (mem_nonvanishingOpen_iff_isUnit_germ X L (s j) t i x hi).mpr hv⟩

end KltDP.Geometry.SectionLinearCombinations
