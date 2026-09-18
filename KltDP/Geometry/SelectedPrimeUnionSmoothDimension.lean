import KltDP.Geometry.SelectedPrimeUnionSmooth
import KltDP.Geometry.RationalCurveSmooth

/-!
# Relative dimension of the original disjoint selected branch

The already proved finite closed cover consists of actual open immersions.
Source locality retains the fixed relative dimension of each original curve.
No dimension or smoothness property of the union is an extra premise.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u v
namespace KltDP.Geometry

theorem isSmoothOfRelativeDimension_of_finite_disjoint_closed_cover
    {Y B : Scheme.{u}} {ι : Type v} [Finite ι] [IsReduced Y]
    (n : ℕ) (C : ι → Scheme.{u}) (c : ∀ i, C i ⟶ Y)
    [∀ i, IsClosedImmersion (c i)] (σ : Y ⟶ B)
    (hcover : ∀ y : Y, ∃ i, y ∈ Set.range (c i).base)
    (hdisj : Pairwise fun i j => Disjoint (Set.range (c i).base) (Set.range (c j).base))
    (hsm : ∀ i, IsSmoothOfRelativeDimension n (c i ≫ σ)) :
    IsSmoothOfRelativeDimension n σ := by
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
  exact IsLocalAtSource.of_openCover (P := @IsSmoothOfRelativeDimension n) 𝒰 hsm

namespace NormalProjectiveSurface

theorem selectedPrimeUnion_isSmoothOfRelativeDimension
    {k : Type u} [Field k] (S : NormalProjectiveSurface k) (n : ℕ)
    (N : Finset S.PrimeCurve)
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hsm : ∀ C ∈ N, IsSmoothOfRelativeDimension n C.toSpec) :
    IsSmoothOfRelativeDimension n
      ((S.selectedPrimeUnionIdeal N).gluedTo ≫ S.structureMorphism) := by
  let J := S.selectedPrimeUnionIdeal N
  letI : IsReduced J.glueData.glued :=
    J.glued_isReduced (Scheme.IdealSheafData.vanishingIdeal_support (I := J)).symm
  apply isSmoothOfRelativeDimension_of_finite_disjoint_closed_cover n
    (fun C : {C : S.PrimeCurve // C ∈ N} => C.val.toScheme)
    (S.selectedPrimeUnionCurveMap N)
    (J.gluedTo ≫ S.structureMorphism) (S.selectedPrimeUnionCurveMap_cover N)
  · intro C D hCD
    rw [S.range_selectedPrimeUnionCurveMap N C, S.range_selectedPrimeUnionCurveMap N D]
    apply Set.disjoint_left.mpr
    intro z hzC hzD
    exact Set.disjoint_left.mp
      (hdisj C.property D.property (fun h => hCD (Subtype.ext h))) hzC hzD
  · intro C
    rw [← Category.assoc, selectedPrimeUnionCurveMap_comp]
    exact hsm C.val C.property

theorem selectedRationalPrimeUnion_isSmoothOne
    {k : Type u} [Field k] (S : NormalProjectiveSurface k) (N : Finset S.PrimeCurve)
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hrat : ∀ C ∈ N, ∃ e : C.toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec) :
    IsSmoothOfRelativeDimension 1
      ((S.selectedPrimeUnionIdeal N).gluedTo ≫ S.structureMorphism) := by
  apply S.selectedPrimeUnion_isSmoothOfRelativeDimension 1 N hdisj
  intro C hC
  obtain ⟨e, he⟩ := hrat C hC
  exact smoothOne_of_projectiveLineIso C.toSpec e he

end NormalProjectiveSurface
end KltDP.Geometry
#print axioms KltDP.Geometry.isSmoothOfRelativeDimension_of_finite_disjoint_closed_cover
#print axioms KltDP.Geometry.NormalProjectiveSurface.selectedRationalPrimeUnion_isSmoothOne
