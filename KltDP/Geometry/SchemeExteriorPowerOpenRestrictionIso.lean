import KltDP.Geometry.SchemeExteriorPowerOpenRestrictionMap
import KltDP.Compatibility.ExteriorPowerRestrictScalarsRingEquiv

/-!
# The original exterior map for an open immersion is invertible

The actual section-ring isomorphisms make the original presheaf comparison
bijective. Open restriction preserves local bijectivity of the original
sheafification unit. The accepted local-bijectivity factorization argument
then proves that the already normalized original sheaf map is invertible.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeExteriorPowerOpenRestriction

open SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem underlying_isIso_of_factor {Y : Scheme.{u}}
    {P Q : Y.Opensᵒᵖ ⥤ AddCommGrp.{u}}
    {S T : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrp.{u}}
    (η : P ⟶ S.val) (a : P ⟶ Q) (b : Q ⟶ T.val) (c : S ⟶ T)
    (hfac : η ≫ c.val = a ≫ b)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) η]
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y) a]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) a]
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y) b]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) b] : IsIso c := by
  have hi : CategoryTheory.Sheaf.IsLocallyInjective c :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      (Opens.grothendieckTopology Y) (a ≫ b) hfac
  have hs : CategoryTheory.Sheaf.IsLocallySurjective c :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac
      (Opens.grothendieckTopology Y) hfac
  exact (CategoryTheory.Sheaf.isLocallyBijective_iff_isIso c).mp ⟨hi, hs⟩

private theorem moduleUnit_locallySurjective {Y : Scheme.{u}} (P : Y.PresheafOfModules) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.val).map
        ((_root_.PresheafOfModules.sheafificationAdjunction
          (𝟙 Y.ringCatSheaf.val)).unit.app P)) := by
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) P.presheaf)
  infer_instance

private theorem moduleMap_locallyInjective {Y : Scheme.{u}} {P Q : Y.PresheafOfModules}
    (a : P ⟶ Q) (h : ∀ U, Function.Injective (a.app U)) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.val).map a) :=
  Presheaf.isLocallyInjective_of_injective (Opens.grothendieckTopology Y) _ h

private theorem moduleMap_locallySurjective {Y : Scheme.{u}} {P Q : Y.PresheafOfModules}
    (a : P ⟶ Q) (h : ∀ U, Function.Surjective (a.app U)) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.val).map a) :=
  Presheaf.isLocallySurjective_of_surjective (Opens.grothendieckTopology Y) _ h

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules) (n : ℕ)

/-- The original scalar comparison is bijective because its actual ring map is invertible. -/
theorem presheafComparison_bijective (U : Y.Opens) :
    Function.Bijective ((presheafComparison j M n).app (op U)) := by
  letI : IsIso (presheafComparisonApp j M n U) :=
    KltDP.Compatibility.ExteriorPowerRestrictScalarsRingEquiv.fromRestrictScalars_isIso
      (j.appIso U).symm.commRingCatIsoToRingEquiv (M.val.obj (op (j ''ᵁ U))) n
  exact (ConcreteCategory.isIso_iff_bijective (presheafComparisonApp j M n U)).mp inferInstance

private theorem underlying_factor :
    (_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.val).map
        (SchemeExteriorPower.toSheaf ((restriction j).obj M) n) ≫
        ((_root_.SheafOfModules.toSheaf Y.ringCatSheaf).map (map j M n)).val =
      (_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.val).map
          (presheafComparison j M n) ≫
        (_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.val).map
          (restrictedUnit j M n) := by
  let F := _root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.val
  change F.map (SchemeExteriorPower.toSheaf ((restriction j).obj M) n) ≫
      F.map (map j M n).val =
    F.map (presheafComparison j M n) ≫ F.map (restrictedUnit j M n)
  rw [← F.map_comp, ← F.map_comp, toSheaf_comp_map]

private theorem comparison_locallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.val).map
        (presheafComparison j M n)) :=
  moduleMap_locallyInjective (presheafComparison j M n)
    (fun U => (presheafComparison_bijective j M n U.unop).injective)

private theorem comparison_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.val).map
        (presheafComparison j M n)) :=
  moduleMap_locallySurjective (presheafComparison j M n)
    (fun U => (presheafComparison_bijective j M n U.unop).surjective)

private theorem restrictedUnit_locallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.val).map
        (restrictedUnit j M n)) := by
  change Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
    (CategoryTheory.whiskerLeft j.opensFunctor.op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (SchemeExteriorPower.presheaf M n).presheaf))
  exact restriction_isLocallyInjective j _

private theorem restrictedUnit_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.val).map
        (restrictedUnit j M n)) := by
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
    (CategoryTheory.whiskerLeft j.opensFunctor.op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (SchemeExteriorPower.presheaf M n).presheaf))
  exact restriction_isLocallySurjective j _

private theorem underlyingMap_isIso :
    IsIso ((_root_.SheafOfModules.toSheaf Y.ringCatSheaf).map (map j M n)) := by
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.val).map
        (SchemeExteriorPower.toSheaf ((restriction j).obj M) n)) :=
    moduleUnit_locallySurjective (SchemeExteriorPower.presheaf ((restriction j).obj M) n)
  letI := comparison_locallyInjective j M n
  letI := comparison_locallySurjective j M n
  letI := restrictedUnit_locallyInjective j M n
  letI := restrictedUnit_locallySurjective j M n
  exact underlying_isIso_of_factor _ _ _ _ (underlying_factor j M n)

/-- Invertibility of the actual previously constructed sheaf map. -/
theorem map_isIso : IsIso (map j M n) := by
  letI := underlyingMap_isIso j M n
  exact isIso_of_reflects_iso (map j M n) (_root_.SheafOfModules.toSheaf Y.ringCatSheaf)

/-- The actual open restriction of the exterior is its actual restricted exterior. -/
def restrictionIso :
    (restriction j).obj (SchemeExteriorPower.sheaf M n) ≅
      SchemeExteriorPower.sheaf ((restriction j).obj M) n := by
  letI := map_isIso j M n
  exact (asIso (map j M n)).symm

theorem restrictionIso_inv : (restrictionIso j M n).inv = map j M n := rfl

theorem restrictionIso_inv_wedge (U : Y.Opens)
    (v : Fin n → ((restriction j).obj M).val.obj (op U)) :
    (restrictionIso j M n).inv.val.app (op U)
        (SchemeExteriorPower.wedge ((restriction j).obj M) n U v) =
      SchemeExteriorPower.wedge M n (j ''ᵁ U) v :=
  map_wedge j M n U v

/-- The inverse comparison also preserves each original wedge, not an arbitrary frame. -/
theorem restrictionIso_hom_wedge (U : Y.Opens)
    (v : Fin n → ((restriction j).obj M).val.obj (op U)) :
    (restrictionIso j M n).hom.val.app (op U)
        (SchemeExteriorPower.wedge M n (j ''ᵁ U) v) =
      SchemeExteriorPower.wedge ((restriction j).obj M) n U v := by
  letI := map_isIso j M n
  refine (congrArg ((restrictionIso j M n).hom.val.app (op U))
    (map_wedge j M n U v).symm).trans ?_
  exact ((_root_.SheafOfModules.evaluation Y.ringCatSheaf (op U)).mapIso
    (asIso (map j M n))).toLinearEquiv.symm_apply_apply _

end KltDP.Geometry.SchemeExteriorPowerOpenRestriction
