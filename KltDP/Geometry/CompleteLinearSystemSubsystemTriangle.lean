import KltDP.Geometry.CompleteLinearSystemSubsystemDomain
import KltDP.Geometry.LinearSystemMatrixMorphism

/-!
# The actual complete-system subsystem triangle

On the original isomorphism open, the actual matrix projection of the
complete map is the original subsystem morphism. The original coefficient
rows, section pullbacks, map isomorphism, and map naturality prove the
triangle; no projective-map equality is assumed in the public consumer.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.CompleteLinearSystemSubsystem

open CompleteLinearSystemSections InvertibleSectionNonvanishingOpen
  LinearSystemNaturality LinearSystemMatrixMorphism

private theorem matrix_morphism_of_lift {k : Type u} [Field k] {X : Scheme.{u}}
    (L : InvertibleSheaf X) {n : ℕ} (s : Fin (n + 1) → L.obj.sections)
    (f : X ⟶ Spec (CommRingCat.of k))
    (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)
    {m : ℕ} (a : Fin (m + 1) → Fin (n + 1) → k)
    (hcomb : (⨆ j, nonvanishingOpen X L (combinationSections L s f a j)) = ⊤)
    (w : X ⟶ (ProjectiveLinearForms.domain k n a).toScheme)
    (hsq : w ≫ (ProjectiveLinearForms.domain k n a).ι =
      LinearSystemMorphism.morphism L s f hcover) :
    w ≫ ProjectiveLinearForms.morphism k n a =
      LinearSystemMorphism.morphism L (combinationSections L s f a) f hcomb := by
  have hsq' : (𝟙 X) ≫ LinearSystemMorphism.morphism L s f hcover =
      w ≫ (ProjectiveLinearForms.domain k n a).ι :=
    (Category.id_comp _).trans hsq.symm
  exact (matrix_morphism_commutes L s f hcover a (𝟙 X) w hsq').trans
    ((morphism_pullback (𝟙 X) L (combinationSections L s f a) f hcomb).trans
      (Category.id_comp _))

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (H L : InvertibleSheaf X) {m : ℕ} (s : Fin (m + 1) → H.obj.sections)
  (σ : H.obj ⟶ L.obj) (hpos : 0 < dimension f L)
  (hcover : (⨆ j, nonvanishingOpen X H (s j)) = ⊤)
  (U : X.Opens) [IsIso ((schemeModulePullback U.ι).map σ)]

/-- The original matrix projection of the complete system recovers the original subsystem map. -/
theorem matrix_triangle :
    matrixMap f H L s σ hpos hcover U ≫
      ProjectiveLinearForms.morphism k (dimension f L - 1) (matrix f H L s σ hpos) =
        U.ι ≫ LinearSystemMorphism.morphism H s f hcover := by
  let LP := pullbackInvertibleSheaf U.ι L
  let b := pullbackSections U.ι L (positiveBasisSections f L hpos)
  let a := matrix f H L s σ hpos
  let t := pullbackSections U.ι L (fun j => _root_.SheafOfModules.sectionsMap σ (s j))
  let hb := LinearSystemRationalMap.subopenSections_cover L
    (positiveBasisSections f L hpos) U (isoOpen_le_nonBase f H L s σ hpos hcover U)
  let ht := SubsystemNonbaseOpen.pulled_image_sections_cover H L s σ hcover U
  have hc : (⨆ j, nonvanishingOpen U.toScheme LP
      (combinationSections LP b (U.ι ≫ f) a j)) = ⊤ := by
    calc
      _ = ⨆ j, nonvanishingOpen U.toScheme LP (t j) :=
        iSup_congr (fun j => congrArg (nonvanishingOpen U.toScheme LP)
          (pulled_combination f H L s σ hpos U j))
      _ = ⊤ := ht
  have he (j : Fin (m + 1)) :
      _root_.SheafOfModules.sectionsMap (Iso.refl LP.obj).hom
        (combinationSections LP b (U.ι ≫ f) a j) = t j :=
    (_root_.SheafOfModules.sectionsMap_id _).trans
      (pulled_combination f H L s σ hpos U j)
  exact (matrix_morphism_of_lift LP b (U.ι ≫ f) hb a hc
    (matrixMap f H L s σ hpos hcover U)
    (matrixMap_inclusion f H L s σ hpos hcover U)).trans
      ((morphism_eq_of_iso_sections LP LP (Iso.refl LP.obj)
        (combinationSections LP b (U.ι ≫ f) a) t (U.ι ≫ f) (U.ι ≫ f)
        hc ht he rfl).trans
          (SubsystemNonbaseOpen.mapped_morphism_eq H L s σ f hcover U))

end KltDP.Geometry.CompleteLinearSystemSubsystem
