import KltDP.Geometry.LinearSystemMatrixSections
import KltDP.Geometry.LinearSystemMapPullback

/-!
# The original matrix square gives the actual pulled combination cover

The compiled matrix-domain preimage identity and the original commuting
square show that the pulled combination sections cover the whole source.
The same square identifies the original two field structure maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemMatrixMorphism

open InvertibleSectionNonvanishingOpen SectionLinearCombinations

variable {k : Type u} [Field k] {X : Scheme.{u}} (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections) (f : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)
  {m : ℕ} (a : Fin (m + 1) → Fin (n + 1) → k)

/-- Exactly the original section combinations specified by the original matrix. -/
abbrev combinationSections : Fin (m + 1) → L.obj.sections :=
  fun j => combination f L.obj s (a j)

variable {T : Scheme.{u}} (v : T ⟶ X) (w : T ⟶ (ProjectiveLinearForms.domain k n a).toScheme)
  (hsq : v ≫ LinearSystemMorphism.morphism L s f hcover =
    w ≫ (ProjectiveLinearForms.domain k n a).ι)

include hcover w hsq in
/-- The original square derives the actual covering condition for the pulled combinations. -/
theorem combinationSections_pullback_cover :
    (⨆ j, nonvanishingOpen T (pullbackInvertibleSheaf v L)
      (LinearSystemNaturality.pullbackSections v L (combinationSections L s f a) j)) = ⊤ := by
  let U := ProjectiveLinearForms.domain k n a
  let g := LinearSystemMorphism.morphism L s f hcover
  calc
    _ = ⨆ j, v ⁻¹ᵁ nonvanishingOpen X L (combinationSections L s f a j) :=
      iSup_congr (fun j => InvertibleSectionNonvanishingPullback.nonvanishingOpen_pullback
        v L (combinationSections L s f a j))
    _ = v ⁻¹ᵁ LinearSystemRationalMap.nonBaseOpen L (combinationSections L s f a) :=
      (v.preimage_iSup (fun j => nonvanishingOpen X L (combinationSections L s f a j))).symm
    _ = v ⁻¹ᵁ (g ⁻¹ᵁ U) :=
      congrArg (fun V : X.Opens => v ⁻¹ᵁ V)
        (LinearSystemMatrixSections.preimage_matrixDomain L s f hcover a).symm
    _ = (v ≫ g) ⁻¹ᵁ U := rfl
    _ = (w ≫ U.ι) ⁻¹ᵁ U := congrArg (fun q : T ⟶ projectiveSpace k n => q ⁻¹ᵁ U) hsq
    _ = w ⁻¹ᵁ (U.ι ⁻¹ᵁ U) := rfl
    _ = w ⁻¹ᵁ ⊤ := congrArg (fun V : U.toScheme.Opens => w ⁻¹ᵁ V) U.ι_preimage_self
    _ = ⊤ := rfl

include hcover hsq in
/-- Both original paths in the square induce exactly the same original field structure. -/
theorem matrixSquare_structure :
    w ≫ ((ProjectiveLinearForms.domain k n a).ι ≫ projectiveSpaceToSpec k n) = v ≫ f := by
  calc
    _ = (w ≫ (ProjectiveLinearForms.domain k n a).ι) ≫ projectiveSpaceToSpec k n :=
      (Category.assoc _ _ _).symm
    _ = (v ≫ LinearSystemMorphism.morphism L s f hcover) ≫ projectiveSpaceToSpec k n :=
      congrArg (fun q : T ⟶ projectiveSpace k n => q ≫ projectiveSpaceToSpec k n) hsq.symm
    _ = v ≫ (LinearSystemMorphism.morphism L s f hcover ≫ projectiveSpaceToSpec k n) :=
      Category.assoc _ _ _
    _ = v ≫ f := congrArg (fun q => v ≫ q) (LinearSystemMorphism.morphism_structure L s f hcover)

end KltDP.Geometry.LinearSystemMatrixMorphism
