import KltDP.Geometry.SchemePointBlowupSequence
import KltDP.Geometry.PointBlowupProper
import KltDP.Geometry.LocallyOfFiniteTypeNoetherian

/-!
# Properness of actual finite point-blowup sequences

The original glued Rees projection is proper over a locally Noetherian
target. For a sequence over a Noetherian affine base, every intermediate
scheme acquires local Noetherianity from its actual structure morphism.
Thus properness and Noetherianity of the final source are consequences of
the sequence, without extra fields in the definition or a supplied model.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemePointBlowup

/-- An actual point blowup over a locally Noetherian scheme is proper. -/
theorem IsAt.isProper {S T : Scheme.{u}} [IsLocallyNoetherian T]
    {f : S ⟶ T} {x : T} (h : IsAt f x) : IsProper f := by
  obtain ⟨c, e, he⟩ := h
  letI := c.instCommRing
  letI := c.instOpenImmersion
  letI := c.instMaximal
  letI : IsProper c.projection :=
    PointBlowupGluing.projection_isProper_of_locallyNoetherian c.j c.q c.isClosed
  rw [← he]
  infer_instance

/-- The actual composite of a finite sequence is proper. Its target's
original finite-type morphism to the Noetherian base supplies local
Noetherianity at every step. -/
theorem SequenceAway.isProper_over_noetherian_base
    {R : CommRingCat.{u}} [IsNoetherianRing R] {S T : Scheme.{u}}
    (t : T ⟶ Spec R) [LocallyOfFiniteType t]
    {U : Set T} {f : S ⟶ T} (h : SequenceAway T U S f) : IsProper f := by
  induction h with
  | of_isIso f hf =>
      letI := hf
      infer_instance
  | step b g x hb hx hg ih =>
      letI := ih
      letI : IsLocallyNoetherian _ :=
        isLocallyNoetherian_of_locallyOfFiniteType_spec (g ≫ t)
      letI : IsProper b := hb.isProper
      infer_instance

/-- Over a proper Noetherian affine base morphism, the final source is
Noetherian. The original sequence map determines its structure morphism. -/
theorem SequenceAway.source_isNoetherian
    {R : CommRingCat.{u}} [IsNoetherianRing R] {S T : Scheme.{u}}
    (t : T ⟶ Spec R) [IsProper t]
    {U : Set T} {f : S ⟶ T} (h : SequenceAway T U S f) : IsNoetherian S := by
  letI : IsProper f := h.isProper_over_noetherian_base t
  exact isNoetherian_of_locallyOfFiniteType_quasiCompact_spec (f ≫ t)

end KltDP.Geometry.SchemePointBlowup
