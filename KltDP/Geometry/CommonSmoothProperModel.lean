import KltDP.Geometry.SurfaceBirationalPointBlowupDominationTarget
import KltDP.Geometry.SchemePointBlowupSurfaceSequence
import KltDP.Geometry.SmoothSurfaceRegularity

/-!
# Common smooth projective domination of an arbitrary proper integral model

The second model V is an arbitrary integral scheme with a proper birational
map to the original surface. It is not supplied with projectivity, normality,
regularity, or a surface package. The actual point-blowup sequence from the
given smooth model supplies a smooth projective source and proper birational
maps to both original models. Every original map and open-domain equation is
retained. This extends the projective-model common-resolution interface.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

open SurfaceBirationalGraphDominationInput
open SurfaceBirationalPointBlowupDomination

/-- A given smooth model and any original proper integral birational model
have an actual smooth projective common domination by point blowups. -/
theorem exists_common_smooth_projective_domination
    {k : Type u} [Field k] [IsAlgClosed k]
    (T X : NormalProjectiveSurface k) [IsSmooth T.structureMorphism]
    {V : Scheme.{u}} [IsIntegral V]
    (t : T.toScheme ⟶ X.toScheme) (v : V ⟶ X.toScheme) [IsProper v]
    (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)
    (htk : t ≫ X.structureMorphism = T.structureMorphism) :
    ∃ (S : NormalProjectiveSurface k) (b : S.toScheme ⟶ T.toScheme)
        (q : S.toScheme ⟶ V),
      IsResolution S T b ∧ IsSmooth S.structureMorphism ∧
      IsPointBlowupSequence S T b ∧ IsBirationalScheme q ∧ IsProper q ∧
      q ≫ (v ≫ X.structureMorphism) = S.structureMorphism ∧
      SchemePointBlowup.SequenceAway T.toScheme
        ((representative T t v ht hv).domain : Set T.toScheme) S.toScheme b ∧
      IsIso (b ∣_ (representative T t v ht hv).domain) ∧ q ≫ v = b ≫ t ∧
      ∃ j : (representative T t v ht hv).domain.toScheme ⟶ S.toScheme,
        j ≫ b = (representative T t v ht hv).domain.ι ∧
        j ≫ q = (representative T t v ht hv).hom := by
  letI : IsProper t := isProper_of_comp_structureMorphism t htk
  obtain ⟨Z, b, q, hZ, h⟩ :=
    exists_common_proper_domination_of_regular T t v ht hv T.regularPoints_of_isSmooth
  letI := hZ
  obtain ⟨hb, hbirb, hbirq, hproperb, hproperq, hproperk, hnoeth,
    hdim, hiso, hq, j, hjb, hjq⟩ := h
  let S : NormalProjectiveSurface k := hb.sourceSurface T
  have hbR : IsResolution S T b :=
    ⟨rfl, hb.source_regular T,
      ⟨hbirb.map_genericPoint, hbirb.isIso_stalkMap_genericPoint⟩⟩
  have hqk : q ≫ (v ≫ X.structureMorphism) = S.structureMorphism := by
    change q ≫ (v ≫ X.structureMorphism) = b ≫ T.structureMorphism
    rw [← Category.assoc, hq, Category.assoc, htk]
  exact ⟨S, b, q, hbR, hb.source_isSmooth T, hb.toSurfaceSequence T,
    hbirq, hproperq, hqk, hb, hiso, hq, j, hjb, hjq⟩

end KltDP.Geometry

#check @KltDP.Geometry.exists_common_smooth_projective_domination
#print axioms KltDP.Geometry.exists_common_smooth_projective_domination
