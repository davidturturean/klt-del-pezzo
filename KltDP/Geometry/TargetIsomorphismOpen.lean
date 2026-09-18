import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
The actual largest open in the target over which the original morphism
is an isomorphism. Target locality proves the restriction to this union
is an isomorphism; no open or isomorphism witness is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- The target points having an original isomorphism neighborhood. -/
def targetIsomorphismOpen {S T : Scheme.{u}} (f : S ⟶ T) : T.Opens :=
  ⟨{x | ∃ U : T.Opens, x ∈ U ∧ IsIso (f ∣_ U)}, by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨U, hxU, hU⟩
    exact ⟨U, fun y hy => ⟨U, hy, hU⟩, U.isOpen, hxU⟩⟩

@[simp] theorem mem_targetIsomorphismOpen {S T : Scheme.{u}}
    (f : S ⟶ T) (x : T) :
    x ∈ targetIsomorphismOpen f ↔
      ∃ U : T.Opens, x ∈ U ∧ IsIso (f ∣_ U) := Iff.rfl

/-- The original restriction to the union of its isomorphism opens is
itself an isomorphism, by the pinned target-locality theorem. -/
theorem isIso_targetIsomorphismOpen {S T : Scheme.{u}} (f : S ⟶ T) :
    IsIso (f ∣_ targetIsomorphismOpen f) := by
  let W := targetIsomorphismOpen f
  let I := {U : T.Opens // IsIso (f ∣_ U)}
  let V : I → W.toScheme.Opens := fun U => W.ι ⁻¹ᵁ U.val
  have hcover : iSup V = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨U, hxU, hU⟩ := x.property
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩
  apply IsLocalAtTarget.of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) V hcover
  intro U
  have hUW : U.val ≤ W := fun x hx => ⟨U.val, hx, U.property⟩
  have himage : W.ι ''ᵁ (W.ι ⁻¹ᵁ U.val) = U.val := by
    ext x
    change (∃ y : W, y.val ∈ U.val ∧ y.val = x) ↔ x ∈ U.val
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hUW hx⟩, hx, rfl⟩
  let e := morphismRestrictRestrict f W (W.ι ⁻¹ᵁ U.val) ≪≫
    morphismRestrictEq f himage
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e).mpr U.property

/-- The original target locus where no isomorphism neighborhood exists. -/
def targetNonisomorphismLocus {S T : Scheme.{u}} (f : S ⟶ T) : Set T :=
  (targetIsomorphismOpen f : Set T)ᶜ

theorem isClosed_targetNonisomorphismLocus {S T : Scheme.{u}} (f : S ⟶ T) :
    IsClosed (targetNonisomorphismLocus f) :=
  (targetIsomorphismOpen f).isOpen.isClosed_compl

end KltDP.Geometry
