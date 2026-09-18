import KltDP.Geometry.LinearSystemRationalMap
import KltDP.Geometry.LinearSystemMapPullback
import KltDP.Geometry.LinearSystemSectionIsoMorphism
import KltDP.Geometry.PullbackSectionCoherence

/-!
# The original rational linear system on an original subopen of its domain

Inclusion in the actual non-base open supplies the pulled section cover.
The original pullback composition and equality isomorphisms identify the
double restriction with the direct restriction, preserving every original
section. The existing morphism naturality then identifies the actual maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemRationalMap

open InvertibleSectionNonvanishingOpen LinearSystemNaturality

variable {X : Scheme.{u}} (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections)
  (U : X.Opens) (hU : U ≤ nonBaseOpen L s)

include hU in
/-- The original sections generate after direct pullback to any subopen of their non-base open. -/
theorem subopenSections_cover :
    (⨆ i, nonvanishingOpen U.toScheme (pullbackInvertibleSheaf U.ι L)
      (pullbackSections U.ι L s i)) = ⊤ := by
  calc
    _ = ⨆ i, U.ι ⁻¹ᵁ nonvanishingOpen X L (s i) :=
      iSup_congr (fun i => InvertibleSectionNonvanishingPullback.nonvanishingOpen_pullback
        U.ι L (s i))
    _ = U.ι ⁻¹ᵁ nonBaseOpen L s :=
      (U.ι.preimage_iSup (fun i => nonvanishingOpen X L (s i))).symm
    _ = ⊤ := by
      apply top_unique
      intro x hx
      exact hU x.property

/-- The actual direct restriction is the original composed pullback, with its original transport. -/
def subopenPullbackIso :
    (pullbackInvertibleSheaf (X.homOfLE hU) (restrictedLine L s)).obj ≅
      (pullbackInvertibleSheaf U.ι L).obj :=
  (schemeModulePullbackCompIso (X.homOfLE hU) (nonBaseOpen L s).ι).app L.obj ≪≫
    eqToIso (congrArg (fun v : U.toScheme ⟶ X => (schemeModulePullback v).obj L.obj)
      (X.homOfLE_ι hU))

/-- This original comparison sends the literal double pullback of each section to its direct pullback. -/
theorem subopenPullbackIso_sectionsMap (i : Fin (n + 1)) :
    _root_.SheafOfModules.sectionsMap (subopenPullbackIso L s U hU).hom
      (pullbackSections (X.homOfLE hU) (restrictedLine L s) (restrictedSections L s) i) =
        pullbackSections U.ι L s i := by
  change _root_.SheafOfModules.sectionsMap
    (((schemeModulePullbackCompIso (X.homOfLE hU) (nonBaseOpen L s).ι).app L.obj).hom ≫
      (eqToIso (congrArg (fun v : U.toScheme ⟶ X => (schemeModulePullback v).obj L.obj)
        (X.homOfLE_ι hU))).hom) _ = _
  rw [_root_.SheafOfModules.sectionsMap_comp]
  exact (congrArg
    (_root_.SheafOfModules.sectionsMap
      (eqToIso (congrArg (fun v : U.toScheme ⟶ X => (schemeModulePullback v).obj L.obj)
        (X.homOfLE_ι hU))).hom)
    (PullbackSectionCoherence.compIso_sectionsMap (X.homOfLE hU)
      (nonBaseOpen L s).ι L.obj (s i))).trans
        (PullbackSectionCoherence.eqToIso_sectionsMap (X.homOfLE_ι hU) L.obj (s i))

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

/-- On the original subopen, the rational-system map is the actual map of the directly pulled sections. -/
theorem morphism_subopen :
    X.homOfLE hU ≫ morphism L s f =
      LinearSystemMorphism.morphism (pullbackInvertibleSheaf U.ι L)
        (pullbackSections U.ι L s) (U.ι ≫ f) (subopenSections_cover L s U hU) := by
  let v := X.homOfLE hU
  let V := nonBaseOpen L s
  let LP := restrictedLine L s
  let t := restrictedSections L s
  let ht := restrictedSections_cover L s
  let hT := pullbackSections_cover v LP t ht
  calc
    _ = LinearSystemMorphism.morphism (pullbackInvertibleSheaf v LP)
        (pullbackSections v LP t) (v ≫ (V.ι ≫ f)) hT :=
      (morphism_pullback v LP t (V.ι ≫ f) ht).symm
    _ = _ := morphism_eq_of_iso_sections
      (pullbackInvertibleSheaf v LP) (pullbackInvertibleSheaf U.ι L)
      (subopenPullbackIso L s U hU) (pullbackSections v LP t)
      (pullbackSections U.ι L s) (v ≫ (V.ι ≫ f)) (U.ι ≫ f)
      hT (subopenSections_cover L s U hU) (subopenPullbackIso_sectionsMap L s U hU)
      (by rw [← Category.assoc, Scheme.homOfLE_ι])

end KltDP.Geometry.LinearSystemRationalMap
