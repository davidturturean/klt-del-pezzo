import KltDP.Geometry.SurfaceBirationalPointBlowupDominationTarget
import KltDP.Geometry.SchemePointBlowupSurfaceSequence
import KltDP.Geometry.SmoothSurfaceRegularity

/-!
# A common resolution retaining both original birational maps

Starting with a smooth projective model T and any normal projective model V
over the same original surface X, the actual point-blowup domination gives
a common smooth resolution. The original scheme Z, both maps, their equation
over X, and their agreement with the original rational map are retained.
The source's regularity and projectivity are derived from the actual sequence.

This uses the already isolated full Stacks 0AHI and Hartshorne projectivity
statements through the imported constructions. It makes no discrepancy claim.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

open SurfaceBirationalGraphDominationInput
open SurfaceBirationalPointBlowupDomination

/-- Any original projective birational model has a common smooth resolution
with the given smooth model, obtained by point blowups of that smooth model. -/
theorem exists_common_resolution_of_smooth_model
    {k : Type u} [Field k] [IsAlgClosed k]
    (T V X : NormalProjectiveSurface k) [IsSmooth T.structureMorphism]
    (t : T.toScheme ⟶ X.toScheme) (v : V.toScheme ⟶ X.toScheme)
    (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)
    (htk : t ≫ X.structureMorphism = T.structureMorphism)
    (hvk : v ≫ X.structureMorphism = V.structureMorphism) :
    letI : IsProper v := isProper_of_comp_structureMorphism v hvk
    ∃ (S : NormalProjectiveSurface k) (b : S.toScheme ⟶ T.toScheme)
        (q : S.toScheme ⟶ V.toScheme),
      IsResolution S T b ∧ IsResolution S V q ∧ IsSmooth S.structureMorphism ∧
      IsPointBlowupSequence S T b ∧
      SchemePointBlowup.SequenceAway T.toScheme
        ((representative T t v ht hv).domain : Set T.toScheme) S.toScheme b ∧
      IsIso (b ∣_ (representative T t v ht hv).domain) ∧
      q ≫ v = b ≫ t ∧
      ∃ j : (representative T t v ht hv).domain.toScheme ⟶ S.toScheme,
        j ≫ b = (representative T t v ht hv).domain.ι ∧
        j ≫ q = (representative T t v ht hv).hom := by
  letI : IsProper t := isProper_of_comp_structureMorphism t htk
  letI : IsProper v := isProper_of_comp_structureMorphism v hvk
  obtain ⟨Z, b, q, hZ, h⟩ :=
    exists_common_proper_domination_of_regular T t v ht hv T.regularPoints_of_isSmooth
  letI := hZ
  obtain ⟨hb, hbirb, hbirq, hproperb, hproperq, hproperk, hnoeth,
    hdim, hiso, hq, j, hjb, hjq⟩ := h
  let S : NormalProjectiveSurface k := hb.sourceSurface T
  have hreg : ∀ y : S.toScheme, RegularPoint S.toScheme y := hb.source_regular T
  have hbk : b ≫ T.structureMorphism = S.structureMorphism := rfl
  have hqk : q ≫ V.structureMorphism = S.structureMorphism := by
    change q ≫ V.structureMorphism = b ≫ T.structureMorphism
    rw [← hvk, ← Category.assoc, hq, Category.assoc, htk]
  have hbR : IsResolution S T b :=
    ⟨hbk, hreg, ⟨hbirb.map_genericPoint, hbirb.isIso_stalkMap_genericPoint⟩⟩
  have hqR : IsResolution S V q :=
    ⟨hqk, hreg, ⟨hbirq.map_genericPoint, hbirq.isIso_stalkMap_genericPoint⟩⟩
  have hsmooth : IsSmooth S.structureMorphism := hb.source_isSmooth T
  exact ⟨S, b, q, hbR, hqR, hsmooth, hb.toSurfaceSequence T, hb, hiso, hq, j, hjb, hjq⟩

end KltDP.Geometry

#check @KltDP.Geometry.exists_common_resolution_of_smooth_model
#print axioms KltDP.Geometry.exists_common_resolution_of_smooth_model
