import KltDP.Geometry.ReducedClosedImmersionOpenRange
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smoothness from a finite disjoint closed cover of a reduced scheme

The actual closed-image family is an open cover: each image is the
complement of the finite union of the others. The preceding reduced
closed-immersion adapter gives actual open immersions. Source locality
then proves smoothness of the original structure morphism.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u v

namespace KltDP.Geometry

variable {Y B : Scheme.{u}} {ι : Type v} [Finite ι]
    (C : ι → Scheme.{u}) (c : ∀ i, C i ⟶ Y) [∀ i, IsClosedImmersion (c i)]

/-- Every original closed image in a finite disjoint cover is open. -/
theorem isOpen_range_of_finite_disjoint_closed_cover
    (hcover : ∀ y : Y, ∃ i, y ∈ Set.range (c i).base)
    (hdisj : Pairwise fun i j => Disjoint (Set.range (c i).base) (Set.range (c j).base))
    (i : ι) : IsOpen (Set.range (c i).base) := by
  classical
  have heq : (Set.range (c i).base)ᶜ =
      ⋃ j : {j : ι // j ≠ i}, Set.range (c j.val).base := by
    ext y
    constructor
    · intro hy
      obtain ⟨j, hj⟩ := hcover y
      have hji : j ≠ i := by intro h; subst j; exact hy hj
      exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
    · intro hy hi
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
      exact Set.disjoint_left.mp (hdisj j.property.symm) hi hj
  rw [← isClosed_compl_iff, heq]
  exact isClosed_iUnion_of_finite fun j => (c j.val).isClosedEmbedding.isClosed_range

/-- A reduced scheme covered by finitely many disjoint actual closed smooth schemes is smooth. -/
theorem isSmooth_of_finite_disjoint_closed_cover [IsReduced Y]
    (σ : Y ⟶ B)
    (hcover : ∀ y : Y, ∃ i, y ∈ Set.range (c i).base)
    (hdisj : Pairwise fun i j => Disjoint (Set.range (c i).base) (Set.range (c j).base))
    (hsm : ∀ i, IsSmooth (c i ≫ σ)) : IsSmooth σ := by
  letI (i : ι) : IsOpenImmersion (c i) :=
    isOpenImmersion_of_isClosedImmersion_of_open_range (c i)
      (isOpen_range_of_finite_disjoint_closed_cover C c hcover hdisj i)
  let 𝒰 : Y.OpenCover :=
    { J := ι
      obj := C
      map := c
      f := fun y => (hcover y).choose
      covers := fun y => (hcover y).choose_spec
      map_prop := fun _ => inferInstance }
  exact IsLocalAtSource.of_openCover (P := @IsSmooth) 𝒰 hsm

end KltDP.Geometry

#print axioms KltDP.Geometry.isOpen_range_of_finite_disjoint_closed_cover
#print axioms KltDP.Geometry.isSmooth_of_finite_disjoint_closed_cover
