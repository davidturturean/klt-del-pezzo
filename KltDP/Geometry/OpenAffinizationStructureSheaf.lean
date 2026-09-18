import KltDP.Geometry.AffinizationStructureSheaf
import KltDP.Geometry.PushforwardBasicOpenLocalization
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# Canonical structure-sheaf comparison for an original open affinization

The actual open affinization uses the original ring Γ(X,U). Its canonical
structure map is invertible for a qcqs open, including the inverse image
of every affine base open under a qcqs morphism. The top-section comparison
is transported by its actual isomorphism, preserving the original map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u

namespace KltDP.Geometry.OpenAffinizationStructureSheaf

/-- Postcomposing with an original scheme isomorphism preserves the
canonical pushforward-O isomorphism. -/
theorem comp_c_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIso f.c] [IsIso g] : IsIso (f ≫ g).c := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  change IsIso ((f ≫ g).app U.unop)
  rw [Scheme.comp_app]
  infer_instance

/-- The original map to the spectrum of Γ(X,U) has the actual sheaf isomorphism. -/
theorem open_toSpecΓ_c_isIso {X : Scheme.{u}} (U : X.Opens)
    [CompactSpace U.toScheme] [QuasiSeparatedSpace U.toScheme] :
    IsIso U.toSpecΓ.c := by
  letI : IsIso U.toScheme.toSpecΓ.c :=
    AffinizationStructureSheaf.toSpecΓ_c_isIso U.toScheme
  exact comp_c_isIso U.toScheme.toSpecΓ (Spec.map U.topIso.inv)

/-- The canonical comparison on every original affine-site inverse-image chart. -/
theorem preimage_toSpecΓ_c_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (U : Y.AffineZariskiSite) :
    IsIso (f ⁻¹ᵁ U.1).toSpecΓ.c := by
  letI : CompactSpace (f ⁻¹ᵁ U.1).toScheme := by
    exact isCompact_iff_compactSpace.mp
      (QuasiCompact.isCompact_preimage (f := f) U.1 U.1.isOpen U.2.isCompact)
  letI : QuasiSeparatedSpace (f ⁻¹ᵁ U.1).toScheme :=
    HasAffineProperty.restrict (P := @QuasiSeparated)
      (inferInstance : QuasiSeparated f) ⟨U.1, U.2⟩
  exact open_toSpecΓ_c_isIso (f ⁻¹ᵁ U.1)

end KltDP.Geometry.OpenAffinizationStructureSheaf
