import KltDP.Geometry.GeneratedCompleteSystemNormalFactor
import KltDP.Geometry.ProjectiveMapTrivialPullback
import KltDP.Geometry.FiniteFactorConstant

/-!
# Actual point factorizations in the generated complete-system normal factor

A proper connected reduced source whose original restricted line is trivial
maps to a genuine point of the actual normal factor. First the original
projective composite is constant. Its point lifts through the actual finite
normal-factor map followed by the original closed image inclusion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.GeneratedCompleteSystemNormalFactor

open CompleteLinearSystemSections CompleteLinearSystemMap
  ProjectiveSpaceDegreeOneSheaf

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
  [IsProper f] [IsIntegral X] (hpos : 0 < dimension f L)
  (hG : Positivity.IsGloballyGenerated L.obj)

/-- An actual trivial restricted line makes the original normal-factor map
constant on any proper connected reduced source over the original field. -/
theorem exists_point_of_trivial_pullback {C : Scheme.{u}}
    (σ : C ⟶ Spec (CommRingCat.of k)) [IsProper σ] [IsReduced C] [ConnectedSpace C]
    (γ : C ⟶ X) (hγ : γ ≫ f = σ)
    (e : (pullbackInvertibleSheaf γ L).obj ≅
      _root_.SheafOfModules.unit C.ringCatSheaf) :
    ∃ z : Spec (CommRingCat.of k) ⟶ target f L hpos hG,
      γ ≫ fromSource f L hpos hG = σ ≫ z ∧
        z ≫ structureMorphism f L hpos hG = 𝟙 _ := by
  let b : target f L hpos hG ⟶ projectiveSpace k (dimension f L - 1) :=
    toImage f L hpos hG ≫ SchematicImageGlued.inclusion (morphism f L hpos)
  let δ : C ⟶ target f L hpos hG := γ ≫ fromSource f L hpos hG
  let O := degreeOne k (dimension f L - 1)
  let eB : (pullbackInvertibleSheaf b O).obj ≅ (line f L hpos hG).obj :=
    ((schemeModulePullbackCompIso (toImage f L hpos hG)
      (SchematicImageGlued.inclusion (morphism f L hpos))).app O.obj).symm
  let eδ : (pullbackInvertibleSheaf δ (line f L hpos hG)).obj ≅
      _root_.SheafOfModules.unit C.ringCatSheaf :=
    ((schemeModulePullbackCompIso γ (fromSource f L hpos hG)).app
      (line f L hpos hG).obj).symm ≪≫
        (schemeModulePullback γ).mapIso (fromSource_pullbackLineIso f L hpos hG) ≪≫ e
  let eP : (pullbackInvertibleSheaf (δ ≫ b) O).obj ≅
      _root_.SheafOfModules.unit C.ringCatSheaf :=
    ((schemeModulePullbackCompIso δ b).app O.obj).symm ≪≫
      (schemeModulePullback δ).mapIso eB ≪≫ eδ
  have hb : b ≫ projectiveSpaceToSpec k (dimension f L - 1) =
      structureMorphism f L hpos hG := by
    dsimp only [b, structureMorphism, imageStructure]
    rw [Category.assoc]
  have hδ : δ ≫ structureMorphism f L hpos hG = σ := by
    dsimp only [δ]
    rw [Category.assoc, fromSource_structure, hγ]
  have hP : (δ ≫ b) ≫ projectiveSpaceToSpec k (dimension f L - 1) = σ := by
    rw [Category.assoc, hb, hδ]
  obtain ⟨p, hp, _⟩ :=
    ProjectiveMapTrivialPullback.factors_through_structure σ (δ ≫ b) eP hP
  letI : IsFinite (toImage f L hpos hG) := toImage_isFinite f L hpos hG
  letI : IsFinite b := by
    dsimp only [b]
    infer_instance
  obtain ⟨z, _, hz⟩ := FiniteFactorConstant.exists_point_lift σ b p δ hp
  refine ⟨z, hz, ?_⟩
  apply FiniteFactorConstant.structure_comp_injective σ
  change σ ≫ (z ≫ structureMorphism f L hpos hG) = σ ≫ 𝟙 _
  rw [← Category.assoc, ← hz, hδ, Category.comp_id]

end KltDP.Geometry.GeneratedCompleteSystemNormalFactor
