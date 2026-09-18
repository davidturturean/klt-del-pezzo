import KltDP.Geometry.BirationalRestriction

/-!
# Birationality in an original square of open inclusions

An original commuting square derives generic-point preservation of its
top map. Since both original vertical open inclusions are birational,
the original composition criterion transfers birationality across the square.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.BirationalOpenSquare

variable {T X V Y : Scheme.{u}}
  [IsIntegral T] [IsIntegral X] [IsIntegral V] [IsIntegral Y]
  (f : X ⟶ Y) [GenericPointPreserving f]
  (j : T ⟶ X) [IsOpenImmersion j] (i : V ⟶ Y) [IsOpenImmersion i]
  (a : T ⟶ V) (h : a ≫ i = j ≫ f)

include f j i h in
/-- The original top map preserves generic points by the actual square. -/
theorem genericPointPreserving : GenericPointPreserving a := by
  constructor
  apply i.isOpenEmbedding.injective
  rw [genericPoint_eq_of_isOpenImmersion i]
  have hc := congrArg (fun q : T ⟶ Y => q.base (genericPoint T)) h
  change i.base (a.base (genericPoint T)) = f.base (j.base (genericPoint T)) at hc
  rw [genericPoint_eq_of_isOpenImmersion j,
    GenericPointPreserving.base_genericPoint (π := f)] at hc
  exact hc

include j i h in
/-- Birationality is equivalent for the two original horizontal maps. -/
theorem isBirationalScheme_iff : IsBirationalScheme a ↔ IsBirationalScheme f := by
  letI := genericPointPreserving f j i a h
  letI : GenericPointPreserving j := ⟨genericPoint_eq_of_isOpenImmersion j⟩
  letI : GenericPointPreserving i := ⟨genericPoint_eq_of_isOpenImmersion i⟩
  have hj := ImmersionBirational.isBirationalScheme_of_isOpenImmersion j
  have hi := ImmersionBirational.isBirationalScheme_of_isOpenImmersion i
  calc
    IsBirationalScheme a ↔ IsBirationalScheme (a ≫ i) := by
      rw [BirationalComposition.isBirationalScheme_comp_iff a i, and_iff_left hi]
    _ ↔ IsBirationalScheme (j ≫ f) := by rw [h]
    _ ↔ IsBirationalScheme f := by
      rw [BirationalComposition.isBirationalScheme_comp_iff j f, and_iff_right hj]

end KltDP.Geometry.BirationalOpenSquare
