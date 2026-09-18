import KltDP.Geometry.NegativeCanonicalSurfaceInvariants
import KltDP.Geometry.RegularResolutionStructureCohomology
import KltDP.Geometry.RegularResolutionNoetherSum
import KltDP.Geometry.SurfacePointBlowupSequenceBirational

/-!
# The same blowdown inherits the derived negative-canonical invariants

The original source's actual nef line and negative canonical pairing
produce its invariants. The same point-blowup sequence transports the
Noether sum and structure-sheaf cohomology to its actual target.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open ModuleCohomology SmoothCanonicalExteriorComparison

/-- Native invariants on the unchanged target of the original blowdown sequence. -/
theorem IsPointBlowupSequence.target_invariants_of_negative_nef
    {k : Type u} [Field k] [IsAlgClosed k]
    {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
    (hb : IsPointBlowupSequence S T b)
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ x : T.Point, RegularPoint T.toScheme x)
    (KS : CartierDivisor S.toScheme) (KT : CartierDivisor T.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅ relativeDifferentialExterior S.structureMorphism 2)
    (eKT : cartierDivisorModule T.toScheme KT ≅ relativeDifferentialExterior T.structureMorphism 2)
    (H : InvertibleSheaf S.toScheme) (hH : Positivity.IsNef S.structureMorphism H)
    (hnegative : S.picardPairing hS (cartierPicardClass S.toScheme KS) H.toPic < 0) :
    T.intersectionPairing hT KT KT + (T.picardRank : ℤ) =
        10 - 8 * (cohomologyDimension T.structureMorphism
          (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) 1 : ℤ) ∧
      eulerCharacteristic T.structureMorphism
          (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) =
        1 - (cohomologyDimension T.structureMorphism
          (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) 1 : ℤ) := by
  have hsource := S.noether_euler_relations_of_negative_nef hS KS eKS H hH hnegative
  let hres : IsResolution S T b :=
    ⟨hb.over_base, hS, (isBirational_iff_isBirationalScheme b).mpr hb.isBirationalScheme⟩
  have hsum := hres.canonical_square_add_picardRank_eq hT KS KT eKS eKT
  have hOne := hres.structureSheaf_cohomologyDimension_eq_of_regular_target hT 1
  have hEuler := hres.structureSheaf_eulerCharacteristic_eq_of_regular_target hT
  constructor
  · calc
      T.intersectionPairing hT KT KT + (T.picardRank : ℤ) =
          S.intersectionPairing hS KS KS + (S.picardRank : ℤ) := hsum.symm
      _ = 10 - 8 * (cohomologyDimension S.structureMorphism
          (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 : ℤ) := hsource.1
      _ = 10 - 8 * (cohomologyDimension T.structureMorphism
          (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) 1 : ℤ) := by rw [hOne]
  · calc
      eulerCharacteristic T.structureMorphism
          (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) =
        eulerCharacteristic S.structureMorphism
          (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) := hEuler.symm
      _ = 1 - (cohomologyDimension S.structureMorphism
          (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 : ℤ) := hsource.2
      _ = 1 - (cohomologyDimension T.structureMorphism
          (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) 1 : ℤ) := by rw [hOne]

end KltDP.Geometry

#print axioms KltDP.Geometry.IsPointBlowupSequence.target_invariants_of_negative_nef
