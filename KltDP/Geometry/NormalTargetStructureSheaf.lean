import KltDP.Geometry.NormalOpenSections

/-!
Normality descends through the canonical structure-presheaf map when that
map is an isomorphism. The actual morphism and its actual map `f.c` are
retained. Properness or birationality alone does not supply this premise.

This is a source-only proof candidate; it does not prove Stein factorization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry

/-- A surjective morphism from an integral normal scheme has normal
integral target if its original structure-sheaf comparison is an isomorphism.
No affineness assumption is imposed on preimages of target affine opens. -/
theorem isNormalScheme_of_isIso_structureMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hnormal : IsNormalScheme X)
    (hsurjective : Function.Surjective f.base) [IsIso f.c] :
    IsNormalScheme Y := by
  intro y
  let U : Y.Opens := (Y.affineCover.map y).opensRange
  have hyU : y ∈ U := Y.affineCover.covers y
  have hU : IsAffineOpen U := isAffineOpen_opensRange (Y.affineCover.map y)
  letI : Nonempty U := ⟨⟨y, hyU⟩⟩
  obtain ⟨x, hx⟩ := hsurjective y
  letI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, by
    change f.base x ∈ U
    rw [hx]
    exact hyU⟩⟩
  letI : IsIntegrallyClosed Γ(X, f ⁻¹ᵁ U) :=
    isIntegrallyClosed_openSections_of_isNormal X hnormal (f ⁻¹ᵁ U)
  letI : IsIso (f.app U) := show IsIso (f.c.app (op U)) from inferInstance
  let e : Γ(Y, U) ≃+* Γ(X, f ⁻¹ᵁ U) :=
    (asIso (f.app U)).commRingCatIsoToRingEquiv
  letI : IsIntegrallyClosed Γ(Y, U) := isIntegrallyClosed_of_ringEquiv e.symm
  have hUnormal : IsNormalScheme U.toScheme :=
    isNormalScheme_of_isOpenImmersion hU.isoSpec.hom
      (spec_isNormalScheme_of_isIntegrallyClosed Γ(Y, U))
  exact normal_stalk_at_image_of_isOpenImmersion U.ι hUnormal ⟨y, hyU⟩

end KltDP.Geometry
