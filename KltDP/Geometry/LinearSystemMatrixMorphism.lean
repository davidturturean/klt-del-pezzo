import KltDP.Geometry.LinearSystemMatrixPullbackIso
import KltDP.Geometry.LinearSystemSectionIsoMorphism

/-!
# The original projective matrix projection triangle

On any original commuting square into the matrix domain, the original
matrix morphism agrees with the actual linear-system morphism of the
pulled original combinations. The square itself supplies their cover.
The canonical restriction is the existing scheme morphism restriction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemMatrixMorphism

open InvertibleSectionNonvanishingOpen ProjectiveSpaceDegreeOneSheaf

variable {k : Type u} [Field k] {X : Scheme.{u}} (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections) (f : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)
  {m : ℕ} (a : Fin (m + 1) → Fin (n + 1) → k)

/-- The actual matrix projection triangle on any original commuting square. -/
theorem matrix_morphism_commutes {T : Scheme.{u}}
    (v : T ⟶ X) (w : T ⟶ (ProjectiveLinearForms.domain k n a).toScheme)
    (hsq : v ≫ LinearSystemMorphism.morphism L s f hcover =
      w ≫ (ProjectiveLinearForms.domain k n a).ι) :
    w ≫ ProjectiveLinearForms.morphism k n a =
      LinearSystemMorphism.morphism (pullbackInvertibleSheaf v L)
        (LinearSystemNaturality.pullbackSections v L (combinationSections L s f a))
        (v ≫ f) (combinationSections_pullback_cover L s f hcover a v w hsq) := by
  let P := degreeOne k n
  let b : Fin (m + 1) → P.obj.sections := fun j => ProjectiveLinearForms.formSection k n (a j)
  let R := LinearSystemRationalMap.restrictedLine P b
  let t := LinearSystemRationalMap.restrictedSections P b
  let hR := LinearSystemRationalMap.restrictedSections_cover P b
  let hT := LinearSystemNaturality.pullbackSections_cover w R t hR
  calc
    _ = LinearSystemMorphism.morphism (pullbackInvertibleSheaf w R)
        (LinearSystemNaturality.pullbackSections w R t)
        (w ≫ ((ProjectiveLinearForms.domain k n a).ι ≫ projectiveSpaceToSpec k n)) hT :=
      (LinearSystemNaturality.morphism_pullback w R t
        ((ProjectiveLinearForms.domain k n a).ι ≫ projectiveSpaceToSpec k n) hR).symm
    _ = _ := LinearSystemNaturality.morphism_eq_of_iso_sections
      (pullbackInvertibleSheaf w R) (pullbackInvertibleSheaf v L)
      (pulledCombinationIso L s f hcover a v w hsq)
      (LinearSystemNaturality.pullbackSections w R t)
      (LinearSystemNaturality.pullbackSections v L (combinationSections L s f a))
      (w ≫ ((ProjectiveLinearForms.domain k n a).ι ≫ projectiveSpaceToSpec k n)) (v ≫ f)
      hT (combinationSections_pullback_cover L s f hcover a v w hsq)
      (pulledCombinationIso_sectionsMap L s f hcover a v w hsq)
      (matrixSquare_structure L s f hcover a v w hsq)

/-- The literal inverse image of the original projective matrix domain. -/
abbrev matrixPreimage : X.Opens :=
  LinearSystemMorphism.morphism L s f hcover ⁻¹ᵁ ProjectiveLinearForms.domain k n a

/-- The projection triangle for the original restriction to the actual matrix-domain preimage. -/
theorem restricted_matrix_morphism :
    (LinearSystemMorphism.morphism L s f hcover ∣_ ProjectiveLinearForms.domain k n a) ≫
        ProjectiveLinearForms.morphism k n a =
      LinearSystemMorphism.morphism
        (pullbackInvertibleSheaf (matrixPreimage L s f hcover a).ι L)
        (LinearSystemNaturality.pullbackSections (matrixPreimage L s f hcover a).ι L
          (combinationSections L s f a))
        ((matrixPreimage L s f hcover a).ι ≫ f)
        (combinationSections_pullback_cover L s f hcover a (matrixPreimage L s f hcover a).ι
          (LinearSystemMorphism.morphism L s f hcover ∣_ ProjectiveLinearForms.domain k n a)
          (morphismRestrict_ι (LinearSystemMorphism.morphism L s f hcover)
            (ProjectiveLinearForms.domain k n a)).symm) :=
  matrix_morphism_commutes L s f hcover a (matrixPreimage L s f hcover a).ι
    (LinearSystemMorphism.morphism L s f hcover ∣_ ProjectiveLinearForms.domain k n a)
    (morphismRestrict_ι (LinearSystemMorphism.morphism L s f hcover)
      (ProjectiveLinearForms.domain k n a)).symm

end KltDP.Geometry.LinearSystemMatrixMorphism
