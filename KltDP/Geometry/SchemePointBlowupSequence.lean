import KltDP.Geometry.Resolution

/-!
Actual point blowups and finite sequences for arbitrary schemes. The
centres avoid a specified subset of the ORIGINAL target under the
original composite morphism. This retains the domain information needed
in point-blowup domination statements. No domination theorem is assumed.

Each step is the existing Rees blowup glued to the unchanged complement,
up to an isomorphism over its target. Existing surface blowup sequences
map to this scheme-level definition without changing any morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemePointBlowup

/-- An actual point blowup, using the existing glued Rees construction. -/
def IsAt {S T : Scheme.{u}} (f : S ⟶ T) (x : T) : Prop :=
  ∃ (c : PointBlowupChart T x) (e : S ≅ c.scheme), e.hom ≫ c.projection = f

/-- The glued chart projection is itself an actual point blowup. -/
theorem isAt_projection {T : Scheme.{u}} {x : T} (c : PointBlowupChart T x) :
    IsAt c.projection x := by
  exact ⟨c, Iso.refl _, by simp⟩

/-- Closedness belongs to the actual centre, not to an auxiliary label. -/
theorem IsAt.isClosed {S T : Scheme.{u}} {f : S ⟶ T} {x : T}
    (h : IsAt f x) : IsClosed ({x} : Set T) := by
  obtain ⟨c, e, he⟩ := h
  simpa only [c.base_eq] using c.isClosed

/-- A finite sequence of actual point blowups whose centres lie outside
the inverse image of the specified original domain. The empty sequence
is represented up to isomorphism over the target. -/
inductive SequenceAway (T : Scheme.{u}) (U : Set T) :
    (S : Scheme.{u}) → (S ⟶ T) → Prop
  | of_isIso {S : Scheme.{u}} (f : S ⟶ T) (hf : IsIso f) : SequenceAway T U S f
  | step {S S' : Scheme.{u}} (b : S ⟶ S') (g : S' ⟶ T) (x : S')
      (hb : IsAt b x) (hx : g.base x ∉ U)
      (hg : SequenceAway T U S' g) : SequenceAway T U S (b ≫ g)

/-- Avoiding a domain also avoids each smaller domain. -/
theorem SequenceAway.mono {S T : Scheme.{u}} {f : S ⟶ T} {U V : Set T}
    (h : SequenceAway T U S f) (hVU : V ⊆ U) : SequenceAway T V S f := by
  induction h with
  | of_isIso f hf => exact .of_isIso f hf
  | step b g x hb hx hg ih =>
      exact .step b g x hb (fun hV => hx (hVU hV)) ih

/-- Forget only the domain-avoidance condition, retaining the original
finite sequence and its composite morphism. -/
theorem SequenceAway.forget {S T : Scheme.{u}} {f : S ⟶ T} {U : Set T}
    (h : SequenceAway T U S f) : SequenceAway T ∅ S f :=
  h.mono (Set.empty_subset U)

end KltDP.Geometry.SchemePointBlowup

namespace KltDP.Geometry

variable {k : Type u} [Field k]

/-- The existing surface point blowup is the same scheme point blowup. -/
theorem IsPointBlowupAt.toSchemeIsAt {S T : NormalProjectiveSurface k}
    {f : S.toScheme ⟶ T.toScheme} {x : T.Point}
    (h : IsPointBlowupAt S T f x) : SchemePointBlowup.IsAt f x := h.blowup

/-- Every existing surface sequence gives an actual scheme sequence;
this adapter assumes no factorization or domination result. -/
theorem IsPointBlowupSequence.toSchemeSequence
    {S T : NormalProjectiveSurface k} {f : S.toScheme ⟶ T.toScheme}
    (h : IsPointBlowupSequence S T f) :
    SchemePointBlowup.SequenceAway T.toScheme ∅ S.toScheme f := by
  induction h with
  | of_isIso f hf hover => exact .of_isIso f hf
  | step b g x hb hg ih => exact .step b g x hb.toSchemeIsAt (by simp) ih

end KltDP.Geometry
