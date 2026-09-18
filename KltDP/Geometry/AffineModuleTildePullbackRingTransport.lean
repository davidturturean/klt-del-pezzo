import KltDP.Geometry.AffineModuleTildePullbackComp

/-!
# The original affine pullback comparison under equality of ring maps

This is the equality-transport step in the original quotient ambient square.
Both the scheme pullback and scalar extension retain their actual functors;
equality elimination checks their original comparison before a composite
quotient ring map is substituted.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.AffineModuleTilde

/-- The actual affine comparison commutes with the two original equality transports. -/
theorem pullbackIso_ringMap_eqToIso {A B : Type u} [CommRing A] [CommRing B]
    {φ ψ : A →+* B} (h : φ = ψ) (M : ModuleCat.{u} A) :
    (eqToIso (congrArg
      (fun ρ => (schemeModulePullback (Spec.map (CommRingCat.ofHom ρ))).obj M.tilde) h)).hom ≫
        (pullbackIso ψ M).hom =
      (pullbackIso φ M).hom ≫
        map (eqToIso (congrArg (fun ρ => (ModuleCat.extendScalars ρ).obj M) h)).hom := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, map_id, Category.id_comp, Category.comp_id]

end KltDP.Geometry.AffineModuleTilde
