import KltDP.Geometry.AffineModuleTildeAdjunction
import KltDP.Geometry.SchemeExteriorPower

/-!
# The original affine tilde-to-exterior map

The original canonical sections of an affine module give an alternating map
into the actual exterior sheaf's global sections. The accepted original tilde
functor and counit lift its exterior linear map to a sheaf morphism. On every
open this morphism preserves wedges of the original canonical sections.

No frame, comparison isomorphism, or quasicoherence premise is supplied.
Invertibility of this actual map is a separate result.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTildeExteriorMap

open AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (n : ℕ)

/-- Restrict the scalars of the original sheaf wedge along the actual affine
section map. The section carriers and the alternating function are unchanged. -/
def sectionWedge (U : Opens (PrimeSpectrum R)) :
    (sectionModule M.tilde U) [⋀^Fin n]→ₗ[R]
      (sectionModule (SchemeExteriorPower.sheaf M.tilde n) U) where
  toFun := SchemeExteriorPower.wedge M.tilde n U
  map_update_add' v i x y :=
    (SchemeExteriorPower.wedge M.tilde n U).map_update_add v i x y
  map_update_smul' v i r x :=
    (SchemeExteriorPower.wedge M.tilde n U).map_update_smul v i
      (StructureSheaf.toOpen R U r) x
  map_eq_zero_of_eq' v _ _ h hij :=
    (SchemeExteriorPower.wedge M.tilde n U).map_eq_zero_of_eq v h hij

/-- The universal exterior map formed from the original canonical sections. -/
def toSectionMap (U : Opens (PrimeSpectrum R)) :
    M.exteriorPower n ⟶ sectionModule (SchemeExteriorPower.sheaf M.tilde n) U :=
  ModuleCat.exteriorPower.desc
    (M := M) (N := sectionModule (SchemeExteriorPower.sheaf M.tilde n) U)
    ((sectionWedge M n U).compLinearMap (ModuleCat.Tilde.toOpen M U).hom)

/-- The universal map retains the original ordered wedge of every family. -/
theorem toSectionMap_wedge (U : Opens (PrimeSpectrum R)) (v : Fin n → M) :
    toSectionMap M n U (exteriorPower.ιMulti R n v) =
      SchemeExteriorPower.wedge M.tilde n U
        (fun i => ModuleCat.Tilde.toOpen M U (v i)) :=
  ModuleCat.exteriorPower.desc_mk
    (M := M) (N := sectionModule (SchemeExteriorPower.sheaf M.tilde n) U)
    ((sectionWedge M n U).compLinearMap (ModuleCat.Tilde.toOpen M U).hom) v

/-- The actual original tilde counit lifts the global exterior map. -/
def map : (M.exteriorPower n).tilde ⟶ SchemeExteriorPower.sheaf M.tilde n :=
  AffineModuleTilde.map (toSectionMap M n ⊤) ≫
    AffineModuleTilde.counit (SchemeExteriorPower.sheaf M.tilde n)

/-- Every native wedge, on every original open, is sent to the wedge of its
original canonical sections. This records the actual map's normalization. -/
theorem map_toOpen_wedge (U : Opens (PrimeSpectrum R)) (v : Fin n → M) :
    (map M n).val.app (op U)
        (ModuleCat.Tilde.toOpen (M.exteriorPower n) U (exteriorPower.ιMulti R n v)) =
      SchemeExteriorPower.wedge M.tilde n U
        (fun i => ModuleCat.Tilde.toOpen M U (v i)) := by
  let E := SchemeExteriorPower.sheaf M.tilde n
  change (AffineModuleTilde.counit E).val.app (op U)
      ((AffineModuleTilde.map (toSectionMap M n ⊤)).val.app (op U)
        (ModuleCat.Tilde.toOpen (M.exteriorPower n) U
          (exteriorPower.ιMulti R n v))) = _
  refine (congrArg ((AffineModuleTilde.counit E).val.app (op U))
    (AffineModuleTilde.map_app_toOpen (toSectionMap M n ⊤) U
      (exteriorPower.ιMulti R n v))).trans ?_
  refine (AffineModuleTilde.counit_toOpen E U
    (toSectionMap M n ⊤ (exteriorPower.ιMulti R n v))).trans ?_
  refine (congrArg (E.val.map (homOfLE (show U ≤ ⊤ from le_top)).op)
    (toSectionMap_wedge M n ⊤ v)).trans ?_
  refine (SchemeExteriorPower.wedge_restrict M.tilde n
    (show U ≤ ⊤ from le_top) (fun i => ModuleCat.Tilde.toOpen M ⊤ (v i))).trans ?_
  apply congrArg (SchemeExteriorPower.wedge M.tilde n U)
  funext i
  exact ConcreteCategory.congr_hom
    (ModuleCat.Tilde.toOpen_res M ⊤ U (homOfLE le_top)) (v i)

end KltDP.Geometry.AffineModuleTildeExteriorMap
