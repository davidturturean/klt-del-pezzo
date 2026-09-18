import KltDP.Geometry.SchemePointBlowupSequenceProper
import KltDP.Geometry.SchemePointBlowupSequenceRestriction
import KltDP.Geometry.PointBlowupSurface
import KltDP.Geometry.BirationalComposition

/-!
# Properness and birationality of the original surface blowup sequence

The existing scheme-level properness theorem applies to each original
step. Its original closed centre is not the surface generic point, so
the actual unchanged complement is nonempty and proves birationality.
The original finite sequence then gives properness and birationality
of its literal composite morphism.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace KltDP.Geometry
attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- An actual point blowup between the original surfaces is proper. -/
theorem IsPointBlowupAt.isProper
    {S T : NormalProjectiveSurface k} {f : S.toScheme ⟶ T.toScheme} {x : T.Point}
    (h : IsPointBlowupAt S T f x) : IsProper f := by
  letI : IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian
  exact h.toSchemeIsAt.isProper

/-- The literal complement of the actual closed centre proves that the
original surface blowup map is birational. -/
theorem IsPointBlowupAt.isBirationalScheme
    {S T : NormalProjectiveSurface k} {f : S.toScheme ⟶ T.toScheme} {x : T.Point}
    (h : IsPointBlowupAt S T f x) : IsBirationalScheme f := by
  have hx : IsClosed ({x} : Set T.toScheme) := h.toSchemeIsAt.isClosed
  let U : T.toScheme.Opens := ⟨({x} : Set T.toScheme)ᶜ, hx.isOpen_compl⟩
  letI : Nonempty U.toScheme := ⟨⟨genericPoint T.toScheme, by
    change genericPoint T.toScheme ≠ x
    exact (T.closedPoint_ne_genericPoint x hx).symm⟩⟩
  letI : IsIso (f ∣_ U) := h.toSchemeIsAt.isIso_restrict U (by simp [U])
  exact isBirationalScheme_of_isIso_restrict f U

/-- The actual composite of an original surface point-blowup sequence is proper. -/
theorem IsPointBlowupSequence.isProper
    {S T : NormalProjectiveSurface k} {f : S.toScheme ⟶ T.toScheme}
    (h : IsPointBlowupSequence S T f) : IsProper f := by
  letI : LocallyOfFiniteType T.structureMorphism := T.projective.locallyOfFiniteType
  exact h.toSchemeSequence.isProper_over_noetherian_base T.structureMorphism

/-- Birationality composes along the actual original surface sequence. -/
theorem IsPointBlowupSequence.isBirationalScheme
    {S T : NormalProjectiveSurface k} {f : S.toScheme ⟶ T.toScheme}
    (h : IsPointBlowupSequence S T f) : IsBirationalScheme f := by
  induction h with
  | of_isIso f hf hover =>
      letI := hf
      exact ⟨genericPoint_eq_of_isOpenImmersion f, inferInstance⟩
  | step b g x hb hg ih =>
      have hbir := hb.isBirationalScheme
      letI : GenericPointPreserving b := ⟨hbir.map_genericPoint⟩
      letI : GenericPointPreserving g := ⟨ih.map_genericPoint⟩
      exact (BirationalComposition.isBirationalScheme_comp_iff b g).mpr ⟨hbir, ih⟩

end KltDP.Geometry

#print axioms KltDP.Geometry.IsPointBlowupAt.isProper
#print axioms KltDP.Geometry.IsPointBlowupAt.isBirationalScheme
#print axioms KltDP.Geometry.IsPointBlowupSequence.isProper
#print axioms KltDP.Geometry.IsPointBlowupSequence.isBirationalScheme
