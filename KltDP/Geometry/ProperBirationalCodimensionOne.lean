import KltDP.Geometry.BirationalValuativeInverse
import KltDP.Geometry.NormalStalkDVR
import Mathlib.AlgebraicGeometry.SpreadingOut

/-!
# Proper birational morphisms near original prime-curve generic points

Properness extends the original inverse function-field map to the actual
valuation stalk. Spreading that lift produces a dominant section around
the chosen point. The actual restricted morphism is then an isomorphism.
The surface specialization uses its proved original prime-curve DVR stalk.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ProperBirationalCodimensionOne

attribute [local instance] integralSchemeStalk_isDomain

/-- A proper birational morphism is an isomorphism on some target open
containing any original point whose stalk is a valuation ring. -/
theorem exists_isomorphism_open_at_valuation_stalk
    {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (π : S ⟶ X) [IsProper π] (hbir : IsBirationalScheme π)
    (x : X) [ValuationRing (X.presheaf.stalk x)] :
    ∃ U : X.Opens, x ∈ U ∧ IsIso (π ∣_ U) := by
  obtain ⟨φ, hφπ, hφdom⟩ := exists_dominant_stalk_lift π hbir x
  obtain ⟨U, hxU, g, hφ, hg⟩ :=
    spread_out_of_isGermInjective' (𝟙 X) π φ
      (by simpa only [Category.comp_id] using hφπ)
  letI : IsDominant φ := hφdom
  letI : IsDominant (U.fromSpecStalkOfMem x hxU ≫ g) := by
    rw [← hφ]
    infer_instance
  letI : IsDominant g := IsDominant.of_comp (U.fromSpecStalkOfMem x hxU) g
  exact ⟨U, hxU, DominantOpenSection.isIso_restrict_of_dominant_section π U g
    (by simpa only [Category.comp_id] using hg)⟩

/-- For an original prime curve on the normal projective surface, the
same proper birational morphism is an isomorphism near its generic point.
The source is any integral scheme and the base field is arbitrary. -/
theorem exists_isomorphism_open_at_primeCurve
    {k : Type u} [Field k] {S : Scheme.{u}} [IsIntegral S]
    (X : NormalProjectiveSurface k) (π : S ⟶ X.toScheme) [IsProper π]
    (hbir : IsBirationalScheme π) (C : X.PrimeCurve) :
    ∃ U : X.toScheme.Opens, C.genericPoint ∈ U ∧ IsIso (π ∣_ U) := by
  letI : IsDiscreteValuationRing (X.stalk C.genericPoint) :=
    C.genericPoint_isDiscreteValuationRing
  exact exists_isomorphism_open_at_valuation_stalk π hbir C.genericPoint

end KltDP.Geometry.ProperBirationalCodimensionOne
