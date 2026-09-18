import KltDP.Geometry.AffineFiniteType

/-! The actual ground-field structure map on the original principal chart. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffinePrincipalNeighborhoodStructure

/-- This is the original affine structure-map square followed by the
literal principal localization, with no independently chosen algebra. -/
theorem structure_map {k : Type u} [CommRing k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of k))
    {U : Y.Opens} (hU : IsAffineOpen U) (r : Γ(Y, U)) :
    letI := affineSectionsAlgebra g hU
    (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(Y, U) (Localization.Away r))) ≫ hU.fromSpec) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) := by
  letI := affineSectionsAlgebra g hU
  have hscalar : baseToAffineSectionsMap g hU ≫
      CommRingCat.ofHom (algebraMap Γ(Y, U) (Localization.Away r)) =
      CommRingCat.ofHom (algebraMap k (Localization.Away r)) := by
    change CommRingCat.ofHom ((algebraMap Γ(Y, U) (Localization.Away r)).comp
      (algebraMap k Γ(Y, U))) = _
    exact congrArg CommRingCat.ofHom
      (IsScalarTower.algebraMap_eq k Γ(Y, U) (Localization.Away r)).symm
  rw [Category.assoc, ← Spec_map_baseToAffineSectionsMap g hU,
    ← Spec.map_comp, hscalar]

end KltDP.Geometry.AffinePrincipalNeighborhoodStructure
