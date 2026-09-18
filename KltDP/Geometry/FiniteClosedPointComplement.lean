import KltDP.Geometry.SchemePointBlowupSequenceRestriction

/-!
The actual complement of finitely many closed points, with no T1
assumption on the scheme. A point-blowup sequence above that finite set
preserves this original complement. These ordinary adapters supply the
domain used by the general point-blowup domination source statement.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- The complement open of the specified finite set of closed points. -/
def finiteClosedPointComplement (X : Scheme.{u})
    (T : Set X) (hfinite : T.Finite)
    (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X)) : X.Opens := by
  have hT : IsClosed T := by
    simpa only [Set.biUnion_of_singleton] using hfinite.isClosed_biUnion hclosed
  exact ⟨Tᶜ, hT.isOpen_compl⟩

@[simp] theorem mem_finiteClosedPointComplement
    (X : Scheme.{u}) (T : Set X) (hfinite : T.Finite)
    (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X)) (x : X) :
    x ∈ finiteClosedPointComplement X T hfinite hclosed ↔ x ∉ T := Iff.rfl

/-- The actual sequence composite is an isomorphism away from the
specified finite bad set. This is proved from the actual blowup steps. -/
theorem SchemePointBlowup.SequenceAway.isIso_finiteClosedPointComplement
    {X Z : Scheme.{u}} {b : Z ⟶ X} (T : Set X) (hfinite : T.Finite)
    (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hb : SchemePointBlowup.SequenceAway X Tᶜ Z b) :
    IsIso (b ∣_ finiteClosedPointComplement X T hfinite hclosed) :=
  hb.isIso_restrict (finiteClosedPointComplement X T hfinite hclosed)

end KltDP.Geometry
