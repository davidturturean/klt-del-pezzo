import KltDP.Geometry.InvertibleSheafFrameWithin

/-! An actual line on the actual field spectrum is globally trivial.
A local frame at its unique point already covers the whole source. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafOnField

variable (k : Type u) [Field k]

/-- The actual local rank-one structure produces a global unit isomorphism on Spec k. -/
theorem exists_unitIso (L : InvertibleSheaf (Spec (CommRingCat.of k))) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf) := by
  let x : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  obtain ⟨U, -, hxU, ⟨e⟩⟩ :=
    InvertibleSheafFrameWithin.exists_unit_frame_within L ⊤ x (by trivial)
  have hU : U = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = x := Subsingleton.elim _ _
    simpa only [hy] using hxU
  subst U
  exact ⟨KltDP.SheafOfModules.isoFromOverTerminal
    (Spec (CommRingCat.of k)).ringCatSheaf (⊤ : (Spec (CommRingCat.of k)).Opens)
    CategoryTheory.Limits.isTerminalTop (e ≪≫
      (_root_.SheafOfModules.unitOverIso
        (R := (Spec (CommRingCat.of k)).ringCatSheaf) ⊤).symm)⟩

#print axioms exists_unitIso

end KltDP.Geometry.InvertibleSheafOnField
