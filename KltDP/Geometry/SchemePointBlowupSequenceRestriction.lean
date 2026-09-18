import KltDP.Geometry.SchemePointBlowupSequence

/-!
An actual sequence whose centres avoid the original open domain is an
isomorphism over that same domain. This supplies domain preservation for
point-blowup domination without assuming an isomorphism as part of the
sequence definition. Pinned restriction-of-restriction and the existing
glued blowup puncture isomorphism provide the two local inputs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- An isomorphism over an open remains an isomorphism over a smaller
open, with the original morphism retained. -/
theorem isIso_morphismRestrict_of_le {S T : Scheme.{u}}
    (f : S ⟶ T) {U V : T.Opens} [IsIso (f ∣_ U)] (h : V ≤ U) :
    IsIso (f ∣_ V) := by
  have himage : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    ext x
    change (∃ y : U, y.val ∈ V ∧ y.val = x) ↔ x ∈ V
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, h hx⟩, hx, rfl⟩
  have he := morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V) ≪≫
    morphismRestrictEq f himage
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff he).mp
    (inferInstance : IsIso ((f ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)))

namespace SchemePointBlowup

/-- An actual point blowup is an isomorphism on each original open
avoiding its centre. No integrality or rational-point assumption is used. -/
theorem IsAt.isIso_restrict {S T : Scheme.{u}} {f : S ⟶ T} {x : T}
    (h : IsAt f x) (U : T.Opens) (hx : x ∉ U) : IsIso (f ∣_ U) := by
  obtain ⟨c, e, he⟩ := h
  letI := c.instCommRing
  letI := c.instOpenImmersion
  letI := c.instMaximal
  let W := PointBlowupGluing.puncture c.j c.q c.isClosed
  have hUW : U ≤ W := by
    intro z hz
    change z ∉ ({c.j.base c.q} : Set T)
    intro hzC
    have hzx : z = x := (Set.mem_singleton_iff.mp hzC).trans c.base_eq
    exact hx (hzx ▸ hz)
  letI : IsIso (c.projection ∣_ W) := by
    change IsIso (PointBlowupGluing.projection c.j c.q c.isClosed ∣_ W)
    rw [← PointBlowupGluing.punctureIso_hom]
    infer_instance
  letI : IsIso (c.projection ∣_ U) := isIso_morphismRestrict_of_le c.projection hUW
  rw [← he, morphismRestrict_comp]
  infer_instance

/-- Every finite actual sequence avoiding the original open is an
isomorphism over that open, for the original composite morphism. -/
theorem SequenceAway.isIso_restrict {S T : Scheme.{u}} {f : S ⟶ T}
    (U : T.Opens) (h : SequenceAway T (U : Set T) S f) : IsIso (f ∣_ U) := by
  induction h with
  | of_isIso f hf =>
      letI := hf
      infer_instance
  | step b g x hb hx hg ih =>
      letI := ih
      letI : IsIso (b ∣_ g ⁻¹ᵁ U) := hb.isIso_restrict (g ⁻¹ᵁ U) hx
      rw [morphismRestrict_comp]
      infer_instance

end SchemePointBlowup
end KltDP.Geometry
