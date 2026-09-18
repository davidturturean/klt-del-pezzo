import KltDP.Geometry.BirationalNormalAffineSections
import KltDP.Geometry.AffinizationStructureSheaf

/-!
# The original pushforward-O map of a proper birational morphism

The original section isomorphisms on the basis of nonempty affine target
opens prove that the original structure-sheaf map is an isomorphism. The
source need only be integral; the target is integral and normal. No Stein
theorem or cohomological premise is used, and universal closedness suffices.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProperBirationalStructureSheaf

/-- The canonical map from the original target structure sheaf to the
original pushforward is an isomorphism. -/
theorem c_isIso
    {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (π : S ⟶ X) [UniversallyClosed π]
    (hbir : IsBirationalScheme π) (hnormal : IsNormalScheme X) : IsIso π.c := by
  let B := {U : X.AffineZariskiSite // Nonempty U.1}
  let V : B → X.Opens := fun U => U.val.1
  have hB : Opens.IsBasis (Set.range V) := by
    rw [Opens.isBasis_iff_nbhd]
    intro W x hx
    obtain ⟨T, hT, hxT, hTW⟩ :=
      Opens.isBasis_iff_nbhd.mp (isBasis_affine_open X) hx
    exact ⟨T, ⟨⟨⟨T, hT⟩, ⟨⟨x, hxT⟩⟩⟩, rfl⟩, hxT, hTW⟩
  letI : IsIso (AffinizationStructureSheaf.structureMap π) := by
    apply TopCat.Sheaf.isIso_of_isIso_basis hB
    intro U
    letI : Nonempty U.val.1 := U.property
    exact BirationalNormalAffineSections.app_isIso π hbir hnormal U.val
  exact (TopCat.Sheaf.forget CommRingCat _).map_isIso
    (AffinizationStructureSheaf.structureMap π)

/-- In particular every actual resolution map has its original
pushforward-O isomorphism, derived from its defining properties. -/
theorem resolution_c_isIso
    {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (hπ : IsResolution S X π) : IsIso π.c := by
  letI : IsProper π := hπ.isProper
  exact c_isIso π ((isBirational_iff_isBirationalScheme π).mp hπ.birational) X.normal

end KltDP.Geometry.ProperBirationalStructureSheaf

#print axioms KltDP.Geometry.ProperBirationalStructureSheaf.c_isIso
#print axioms KltDP.Geometry.ProperBirationalStructureSheaf.resolution_c_isIso
