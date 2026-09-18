import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
The pinned isomorphism criterion for presheafed spaces lifts through the
forgetful functors to schemes. A proper bijective scheme map with its
original structure-sheaf map an isomorphism is therefore an isomorphism.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ProperIsoComponents

/-- The original structure-sheaf map remains an isomorphism after
restriction to any target open. -/
theorem restrict_c_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f.c] (U : Y.Opens) : IsIso (f ∣_ U).c := by
  letI : ∀ V, IsIso ((f ∣_ U).c.app V) := by
    intro V
    change IsIso ((f ∣_ U).app V.unop)
    rw [morphismRestrict_app]
    letI : IsIso (f.app (U.ι ''ᵁ V.unop)) := by
      change IsIso (f.c.app (Opposite.op (U.ι ''ᵁ V.unop)))
      infer_instance
    infer_instance
  exact NatIso.isIso_of_isIso_app (f ∣_ U).c

theorem isIso_of_base_c {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f.base] [IsIso f.c] : IsIso f := by
  letI : IsIso (SheafedSpace.forgetToPresheafedSpace.map
      (LocallyRingedSpace.forgetToSheafedSpace.map (Scheme.forgetToLocallyRingedSpace.map f))) := by
    change IsIso f.toPshHom
    exact PresheafedSpace.isIso_of_components f.toPshHom
  letI : IsIso (LocallyRingedSpace.forgetToSheafedSpace.map
      (Scheme.forgetToLocallyRingedSpace.map f)) :=
    isIso_of_reflects_iso _ SheafedSpace.forgetToPresheafedSpace
  letI : IsIso (Scheme.forgetToLocallyRingedSpace.map f) :=
    isIso_of_reflects_iso _ LocallyRingedSpace.forgetToSheafedSpace
  exact isIso_of_reflects_iso f Scheme.forgetToLocallyRingedSpace

theorem isIso_of_bijective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsIso f.c] (hf : Function.Bijective f.base) : IsIso f := by
  letI : IsIso f.base :=
    TopCat.isIso_of_bijective_of_isClosedMap f.base hf f.isClosedMap
  exact isIso_of_base_c f

end KltDP.Geometry.ProperIsoComponents
