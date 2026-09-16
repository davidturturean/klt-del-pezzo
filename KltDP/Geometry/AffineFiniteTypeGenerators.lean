/-
Original pinned-API adapter following Vilin97/MazurTheorem at
9327963d4ec14fba49c7b14b004fd00707ffc2e9,
SchemeModuleQuasicoherent.lean:1648-1688,1739-1808. Apache 2.0.
-/
import KltDP.Geometry.AffineFiniteTypeSections

/-!
# Finite generators on original affine opens

Finite original affine sections give an actual finite free epimorphism
through the proved affine tilde counit. The original affine chart and
open/Over comparisons carry this epimorphism back to the original open.
The final theorem derives these generators from local finite type.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace KltDP.Geometry.AffineFiniteTypeGenerators

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction AffineModuleTilde

variable {X : Scheme.{u}} (M : X.Modules)

local instance originalSectionModule (V : X.Opens) :
    Module Γ(X, V) (M.val.obj (op V)) := (M.val.obj (op V)).isModule

private def restrictionCompIso {Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g] :
    restriction f ⋙ restriction g ≅ restriction (g ≫ f) :=
  isoWhiskerRight (restrictionIsoPullback f) (restriction g) ≪≫
    isoWhiskerLeft (schemeModulePullback f) (restrictionIsoPullback g) ≪≫
      schemeModulePullbackCompIso g f ≪≫ (restrictionIsoPullback (g ≫ f)).symm

private def restrictionObjectIsoOfEq {Y : Scheme.{u}}
    {f g : Y ⟶ X} [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) : (restriction f).obj M ≅ (restriction g).obj M := by
  cases h
  exact Iso.refl _

private def affineChartReturnIso {U : X.Opens} (hU : IsAffineOpen U) :
    (restriction hU.isoSpec.hom).obj ((restriction hU.fromSpec).obj M) ≅
      (restriction U.ι).obj M :=
  (restrictionCompIso hU.fromSpec hU.isoSpec.hom).app M ≪≫
    restrictionObjectIsoOfEq M (by
      change hU.isoSpec.hom ≫ hU.isoSpec.inv ≫ U.ι = U.ι
      exact hU.isoSpec.hom_inv_id_assoc U.ι)

/-- Finite original affine sections yield a finite generating family on
the actual open subscheme. -/
theorem exists_on_open_of_sections_finite [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) (M.val.obj (op U))] :
    ∃ G : ((restriction U.ι).obj M).GeneratingSections, Finite G.I := by
  let N := (restriction hU.fromSpec).obj M
  letI : Module.Finite Γ(X, U) (sectionModule N ⊤) :=
    Module.Finite.equiv (AffineOpenFiniteGenerators.sectionsFromSpecLinearEquiv M hU).symm
  obtain ⟨G, hG⟩ := exists_finite_generatingSections_of_globalSections_finite N
  letI : Finite G.I := hG
  let F := restriction hU.isoSpec.hom
  letI : PreservesColimitsOfSize.{u, u} F :=
    (restrictionAdjunction hU.isoSpec.hom).leftAdjoint_preservesColimits
  let G' := (G.map F (restrictionUnitIso hU.isoSpec.hom).symm).ofEpi
    (affineChartReturnIso M hU).hom
  exact ⟨G', inferInstanceAs (Finite G.I)⟩

/-- The same actual finite family on the original Over site. -/
def generatingSectionsOverOfOpen (U : X.Opens)
    (G : ((restriction U.ι).obj M).GeneratingSections) :
    (M.over U).GeneratingSections :=
  (G.map (openToOverFunctor U) (openToOverUnitIso U)).ofEpi
    (openToOverRestrictionIso U M).hom

/-- Finite original affine sections yield finite original Over generators. -/
theorem exists_over_of_sections_finite [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) (M.val.obj (op U))] :
    ∃ G : (M.over U).GeneratingSections, Finite G.I := by
  obtain ⟨G, hG⟩ := exists_on_open_of_sections_finite M hU
  letI : Finite G.I := hG
  exact ⟨generatingSectionsOverOfOpen M U G, inferInstanceAs (Finite G.I)⟩

/-- Local finite type derives a finite original generating family on every
original affine open; no global finite presentation is assumed. -/
theorem exists_over [M.IsQuasicoherent] [M.IsFiniteType]
    {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ G : (M.over U).GeneratingSections, Finite G.I := by
  letI : Module.Finite Γ(X, U) (M.val.obj (op U)) :=
    AffineFiniteTypeSections.sections_finite M hU
  exact exists_over_of_sections_finite M hU

end KltDP.Geometry.AffineFiniteTypeGenerators
