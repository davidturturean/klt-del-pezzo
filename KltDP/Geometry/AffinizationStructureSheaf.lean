import KltDP.Compatibility.SheafIsoOnBasis
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
The original affinization map of a quasi-compact quasi-separated scheme
has an isomorphism as its canonical structure-presheaf comparison.
The pinned Qcqs lemma already proves the comparison on each distinguished
open of the original spectrum; the accepted sheaf basis criterion gives
all opens. This is an ordinary affine-piece producer, not Stein
factorization or geometric connectedness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffinizationStructureSheaf

/-- The canonical structure map of an original scheme morphism, regarded
as a morphism of the original ring sheaves. -/
def structureMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf :=
  CategoryTheory.Sheaf.Hom.mk f.c

/-- The pinned localization comparison on distinguished opens determines
the canonical pushforward structure-sheaf isomorphism on every open. -/
theorem structureMap_toSpecΓ_isIso (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsIso (structureMap X.toSpecΓ) := by
  apply TopCat.Sheaf.isIso_of_isIso_basis
    (B := fun r : Γ(X, ⊤) => PrimeSpectrum.basicOpen r)
    PrimeSpectrum.isBasis_basic_opens
  intro r
  exact isIso_ΓSpec_adjunction_unit_app_basicOpen r

/-- The preceding theorem retains the original presheaf map `X.toSpecΓ.c`. -/
theorem toSpecΓ_c_isIso (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] : IsIso X.toSpecΓ.c := by
  letI := structureMap_toSpecΓ_isIso X
  exact (TopCat.Sheaf.forget CommRingCat _).map_isIso (structureMap X.toSpecΓ)

/-- In particular, the original comparison on any open of the spectrum is invertible. -/
theorem toSpecΓ_app_isIso (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (U : (Spec Γ(X, ⊤)).Opens) :
    IsIso (X.toSpecΓ.app U) := by
  letI := toSpecΓ_c_isIso X
  change IsIso (X.toSpecΓ.c.app (op U))
  infer_instance

end KltDP.Geometry.AffinizationStructureSheaf
