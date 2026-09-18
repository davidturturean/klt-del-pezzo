import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Original pushforward rings on distinguished affine subopens

The original ring on the inverse image of a distinguished subopen is
the localization of the original inverse-image section ring. Its algebra
map is the literal structure-presheaf restriction. The only geometric
input is that the original inverse-image open is quasi-compact and
quasi-separated, derived automatically over affine opens for a qcqs map.

The equality-of-opens adapter specializes the existing pinned
`IsAffineOpen.isLocalization_of_eq_basicOpen` proof to the pinned qcqs
localization theorem. No sheaf, ring map, or spectrum is replaced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.PushforwardBasicOpenLocalization

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The literal original restriction between the two inverse-image section rings. -/
def restriction (U : Y.Opens) (r : Γ(Y, U)) :
    Γ(X, f ⁻¹ᵁ U) ⟶ Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
  X.presheaf.map ((Opens.map f.base).map (homOfLE (Y.basicOpen_le r))).op

/-- The actual base and inverse-image restrictions form the original naturality square. -/
@[reassoc] theorem restriction_square (U : Y.Opens) (r : Γ(Y, U)) :
    Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op ≫ f.app (Y.basicOpen r) =
      f.app U ≫ restriction f U r :=
  f.naturality (homOfLE (Y.basicOpen_le r)).op

private theorem isLocalization_of_eq_basicOpen_of_qcqs
    {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X))
    (r : Γ(X, U)) (i : V ⟶ U) (e : V = X.basicOpen r) :
    @IsLocalization.Away _ _ r Γ(X, V) _ (X.presheaf.map i.op).hom.toAlgebra := by
  subst e
  convert isLocalization_basicOpen_of_qcqs hU hU' r using 3

/-- The pinned qcqs theorem retains the exact inverse-image ring and restriction algebra. -/
theorem isLocalization_preimage_basicOpen_of_qcqs (U : Y.Opens) (r : Γ(Y, U))
    (hqc : IsCompact (f ⁻¹ᵁ U : Set X))
    (hqs : IsQuasiSeparated (f ⁻¹ᵁ U : Set X)) :
    letI := (restriction f U r).hom.toAlgebra
    IsLocalization.Away (f.app U r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
  isLocalization_of_eq_basicOpen_of_qcqs hqc hqs (f.app U r)
    ((Opens.map f.base).map (homOfLE (Y.basicOpen_le r)))
    (Scheme.preimage_basicOpen f r)

/-- Every actual affine-site distinguished restriction of a qcqs map is this localization. -/
theorem isLocalization_preimage_basicOpen [QuasiCompact f] [QuasiSeparated f]
    (U : Y.affineOpens) (r : Γ(Y, U.1)) :
    letI := (restriction f U.1 r).hom.toAlgebra
    IsLocalization.Away (f.app U.1 r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
  have hqs : QuasiSeparatedSpace (f ⁻¹ᵁ U.1).toScheme :=
    HasAffineProperty.restrict (P := @QuasiSeparated)
      (inferInstance : QuasiSeparated f) U
  exact isLocalization_preimage_basicOpen_of_qcqs f U.1 r
    (QuasiCompact.isCompact_preimage (f := f) U.1 U.1.isOpen U.2.isCompact)
    ((isQuasiSeparated_iff_quasiSeparatedSpace
      (f ⁻¹ᵁ U.1 : Set X) (f ⁻¹ᵁ U.1).isOpen).mpr hqs)

end KltDP.Geometry.PushforwardBasicOpenLocalization
