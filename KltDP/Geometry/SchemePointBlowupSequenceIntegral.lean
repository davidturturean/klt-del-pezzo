import KltDP.Geometry.SchemePointBlowupSequenceRestriction
import KltDP.Geometry.BirationalAdapters

/-!
# Integrality and birationality of domain-preserving point-blowup sequences

A nonempty unchanged original open prevents each centre from being the
generic point of its integral intermediate target. Its actual affine ideal
is therefore nonzero. The existing Rees-gluing integrality theorem applies
at every step. No source-integrality or birationality field is added to the
sequence definition, and no surface, field, or regularity hypothesis is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.SchemePointBlowup

/-- Blowing up an actual non-generic point of an integral scheme has
integral source, for the given map and its original Rees chart. -/
theorem IsAt.source_isIntegral {S T : Scheme.{u}} [IsIntegral T]
    {f : S ⟶ T} {x : T} (h : IsAt f x) (hx : x ≠ genericPoint T) :
    IsIntegral S := by
  obtain ⟨c, e, he⟩ := h
  letI := c.instCommRing
  letI := c.instOpenImmersion
  letI := c.instMaximal
  letI : Nonempty (Spec (CommRingCat.of c.R)) := ⟨c.q⟩
  letI : IsIntegral (Spec (CommRingCat.of c.R)) := isIntegral_of_isOpenImmersion c.j
  letI : IsDomain c.R :=
    PointBlowupGluing.affine_open_chart_isDomain_of_integral c.j c.q
  have hq : c.q.asIdeal ≠ ⊥ := by
    intro hz
    have hqbot : c.q = (⊥ : PrimeSpectrum c.R) := PrimeSpectrum.ext hz
    apply hx
    rw [← c.base_eq, hqbot, ← genericPoint_eq_bot_of_affine (CommRingCat.of c.R)]
    exact genericPoint_eq_of_isOpenImmersion c.j
  letI : IsIntegral c.scheme := PointBlowupGluing.scheme_isIntegral c.j c.q c.isClosed hq
  letI : Nonempty S := ⟨e.inv.base (genericPoint c.scheme)⟩
  exact isIntegral_of_isOpenImmersion e.hom

/-- A finite sequence preserving a nonempty original open has integral
source. Intermediate integrality is proved inductively on the actual sequence. -/
theorem SequenceAway.source_isIntegral {S T : Scheme.{u}} [IsIntegral T]
    (U : T.Opens) [Nonempty U.toScheme] {f : S ⟶ T}
    (h : SequenceAway T (U : Set T) S f) : IsIntegral S := by
  induction h with
  | of_isIso f hf =>
      letI := hf
      letI : Nonempty _ := ⟨(inv f).base (genericPoint T)⟩
      exact isIntegral_of_isOpenImmersion f
  | step b g x hb hx hg ih =>
      letI := ih
      letI : IsIso (g ∣_ U) := hg.isIso_restrict U
      apply hb.source_isIntegral
      intro hgen
      subst x
      exact hx (genericPoint_mem_preimage_of_isIso_restrict g U)

/-- The same original sequence composite is birational. This uses the
derived integral source and the proved isomorphism over the unchanged open. -/
theorem SequenceAway.isBirationalScheme {S T : Scheme.{u}} [IsIntegral T]
    (U : T.Opens) [Nonempty U.toScheme] {f : S ⟶ T}
    (h : SequenceAway T (U : Set T) S f) :
    letI := h.source_isIntegral U
    IsBirationalScheme f := by
  letI := h.source_isIntegral U
  letI : IsIso (f ∣_ U) := h.isIso_restrict U
  exact isBirationalScheme_of_isIso_restrict f U

end KltDP.Geometry.SchemePointBlowup
