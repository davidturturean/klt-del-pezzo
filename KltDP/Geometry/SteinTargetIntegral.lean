import KltDP.Geometry.NormalTargetStructureSheaf

/-!
Ordinary descent through the original canonical structure-sheaf map.
The target's integrality is derived, so the compiled normal-target theorem
can be used without a separate target-integrality assumption. These are
consumers of explicit original-map conditions, not Stein existence.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.SteinTargetIntegral

/-- An isomorphism of the original structure-sheaf comparison descends
reducedness, without any topological surjectivity assumption. -/
theorem reduced {X Y : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Y) [IsIso f.c] : IsReduced Y := by
  constructor
  intro U
  letI : IsIso (f.app U) := show IsIso (f.c.app (op U)) from inferInstance
  exact isReduced_of_injective (f.app U).hom
    (asIso (f.app U)).commRingCatIsoToRingEquiv.injective

/-- The original section-ring isomorphisms and actual surjectivity
make the target integral whenever the source is integral. -/
theorem integral {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Y) (hsurjective : Function.Surjective f.base) [IsIso f.c] :
    IsIntegral Y := by
  constructor
  · exact Nonempty.map f.base inferInstance
  · intro U hU
    obtain ⟨y⟩ := hU
    obtain ⟨x, hx⟩ := hsurjective y.1
    letI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, by
      change f.base x ∈ U
      rw [hx]
      exact y.2⟩⟩
    letI : IsIso (f.app U) := show IsIso (f.c.app (op U)) from inferInstance
    exact Function.Injective.isDomain (f.app U).hom
      (asIso (f.app U)).commRingCatIsoToRingEquiv.injective

/-- The actual Stein structure-sheaf and surjectivity clauses will
therefore give both integrality and normality of its original target. -/
theorem integral_and_normal {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Y) (hnormal : IsNormalScheme X)
    (hsurjective : Function.Surjective f.base) [IsIso f.c] :
    IsIntegral Y ∧ IsNormalScheme Y := by
  letI : IsIntegral Y := integral f hsurjective
  exact ⟨inferInstance, isNormalScheme_of_isIso_structureMap f hnormal hsurjective⟩

end KltDP.Geometry.SteinTargetIntegral
