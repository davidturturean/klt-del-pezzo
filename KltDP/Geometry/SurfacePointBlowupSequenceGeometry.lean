import KltDP.Geometry.SchemePointBlowupSequenceSmooth
import KltDP.Geometry.PointBlowupSurface
import KltDP.Geometry.CartierDivisorPullbackComp

/-!
# Geometry of the original surface point-blowup sequence

The original field triangle is part of each actual surface step and is
preserved under composition. The existing scheme-sequence smoothness
theorem then applies to the same schemes and maps. Generic-point
preservation follows from the original glued projection, transported
through the actual scheme isomorphism in each original blowup step.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace KltDP.Geometry
attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- Every original surface sequence preserves its original field structure. -/
theorem IsPointBlowupSequence.over_base
    {S T : NormalProjectiveSurface k} {f : S.toScheme ⟶ T.toScheme}
    (h : IsPointBlowupSequence S T f) :
    f ≫ T.structureMorphism = S.structureMorphism := by
  induction h with
  | of_isIso f hf hover => exact hover
  | step b g x hb hg ih => rw [Category.assoc, ih, hb.over_base]

/-- An actual original surface point blowup preserves the generic point. -/
theorem IsPointBlowupAt.genericPointPreserving
    {S T : NormalProjectiveSurface k} {f : S.toScheme ⟶ T.toScheme} {x : T.Point}
    (h : IsPointBlowupAt S T f x) : GenericPointPreserving f := by
  obtain ⟨c, e, he⟩ := h.blowup
  letI := c.instCommRing
  letI := c.instOpenImmersion
  letI := c.instMaximal
  letI : IsIntegral c.scheme :=
    PointBlowupGluing.surface_scheme_isIntegral T c.j c.q c.isClosed
  refine ⟨?_⟩
  rw [← he, Scheme.comp_base_apply, genericPoint_eq_of_isOpenImmersion e.hom]
  exact PointBlowupGluing.surface_projection_genericPoint T c.j c.q c.isClosed

/-- The actual composite of any original surface point-blowup sequence
preserves the original generic point. -/
theorem IsPointBlowupSequence.genericPointPreserving
    {S T : NormalProjectiveSurface k} {f : S.toScheme ⟶ T.toScheme}
    (h : IsPointBlowupSequence S T f) : GenericPointPreserving f := by
  induction h with
  | of_isIso f hf hover =>
      letI := hf
      exact ⟨genericPoint_eq_of_isOpenImmersion f⟩
  | step b g x hb hg ih =>
      letI : GenericPointPreserving b := hb.genericPointPreserving
      letI : GenericPointPreserving g := ih
      exact CartierDivisorPullbackComp.genericPointPreserving_comp b g

/-- Smoothness of the original field structure is preserved by an actual
surface point blowup, using its unchanged scheme-level presentation. -/
theorem IsPointBlowupAt.source_isSmooth [IsAlgClosed k]
    {S T : NormalProjectiveSurface k} [IsSmooth T.structureMorphism]
    {f : S.toScheme ⟶ T.toScheme} {x : T.Point} (h : IsPointBlowupAt S T f x) :
    IsSmooth S.structureMorphism := by
  have hs : IsSmooth (f ≫ T.structureMorphism) :=
    h.toSchemeIsAt.isSmooth_comp_structure T
  rwa [h.over_base] at hs

/-- The source of the original finite sequence is smooth over the original
field whenever its original target is smooth over that field. -/
theorem IsPointBlowupSequence.source_isSmooth [IsAlgClosed k]
    {S T : NormalProjectiveSurface k} [IsSmooth T.structureMorphism]
    {f : S.toScheme ⟶ T.toScheme} (h : IsPointBlowupSequence S T f) :
    IsSmooth S.structureMorphism := by
  have hs : IsSmooth (f ≫ T.structureMorphism) :=
    h.toSchemeSequence.source_isSmooth T
  rwa [h.over_base] at hs

end KltDP.Geometry

#print axioms KltDP.Geometry.IsPointBlowupSequence.over_base
#print axioms KltDP.Geometry.IsPointBlowupSequence.genericPointPreserving
#print axioms KltDP.Geometry.IsPointBlowupSequence.source_isSmooth
