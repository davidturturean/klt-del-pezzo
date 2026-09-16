import KltDP.Geometry.SchemeModuleUnitCoherence
import KltDP.Geometry.SchemeKernelEquationRestriction

/-!
# Restriction of actual conormal equation maps

The open base-change comparison is the same composite of actual pullback
and restriction comparisons used to define `schemeConormalRestrictionIso`.
Its unit compatibility is proved from their adjunction normalizations.
Consequently the conormal equation map restricts to the equation map of
the restricted morphism, with the original section-ring restriction.

No regularity, invertibility, affine presentation, or transition identity
is assumed. These statements apply before an equation map is proved to
be a local frame.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

open SchemeModuleRestriction

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- The canonical comparison between restriction of an actual pullback
and pullback of the actual restricted module. -/
def schemeModuleOpenBaseChangeIso :
    schemeModulePullback f ⋙ restriction (f ⁻¹ᵁ U).ι ≅
      restriction U.ι ⋙ schemeModulePullback (f ∣_ U) :=
  isoWhiskerLeft (schemeModulePullback f) (restrictionIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
    schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f ≪≫
    eqToIso (congrArg schemeModulePullback (morphismRestrict_ι f U).symm) ≪≫
    (schemeModulePullbackCompIso (f ∣_ U) U.ι).symm ≪≫
    isoWhiskerRight (restrictionIsoPullback U.ι).symm
      (schemeModulePullback (f ∣_ U))

/-- The actual open base-change comparison preserves the original
structure-module unit maps on both routes around the square. -/
theorem schemeModuleOpenBaseChangeIso_unit :
    (schemeModuleOpenBaseChangeIso f U).hom.app
        (_root_.SheafOfModules.unit Y.ringCatSheaf) ≫
      (schemeModulePullback (f ∣_ U)).map (restrictionUnitIso U.ι).hom ≫
        (schemeModulePullbackUnitIso (f ∣_ U)).hom =
    (restriction (f ⁻¹ᵁ U).ι).map (schemeModulePullbackUnitIso f).hom ≫
      (restrictionUnitIso (f ⁻¹ᵁ U).ι).hom := by
  let P := schemeModulePullback (f ∣_ U)
  let A := (restrictionIsoPullback U.ι).app
    (_root_.SheafOfModules.unit Y.ringCatSheaf)
  let B := (schemeModulePullbackCompIso (f ∣_ U) U.ι).app
    (_root_.SheafOfModules.unit Y.ringCatSheaf)
  have hA : P.map A.inv ≫ P.map (restrictionUnitIso U.ι).hom =
      P.map (schemeModulePullbackUnitIso U.ι).hom := by
    rw [← Functor.map_comp]
    congr 1
    exact A.inv_comp_eq.mpr (restrictionIsoPullback_unit U.ι).symm
  have hB : B.inv ≫ (P.map (schemeModulePullbackUnitIso U.ι).hom ≫
      (schemeModulePullbackUnitIso (f ∣_ U)).hom) =
      (schemeModulePullbackUnitIso ((f ∣_ U) ≫ U.ι)).hom :=
    B.inv_comp_eq.mpr (schemeModulePullbackCompIso_unit (f ∣_ U) U.ι).symm
  have htail : B.inv ≫ (P.map A.inv ≫
      (P.map (restrictionUnitIso U.ι).hom ≫
        (schemeModulePullbackUnitIso (f ∣_ U)).hom)) =
      (schemeModulePullbackUnitIso ((f ∣_ U) ≫ U.ι)).hom := by
    rw [← Category.assoc (P.map A.inv), hA, hB]
  change ((restrictionIsoPullback (f ⁻¹ᵁ U).ι).hom.app
      ((schemeModulePullback f).obj (_root_.SheafOfModules.unit Y.ringCatSheaf)) ≫
      (schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f).hom.app
        (_root_.SheafOfModules.unit Y.ringCatSheaf) ≫
      (eqToIso (congrArg schemeModulePullback
        (morphismRestrict_ι f U).symm)).hom.app
          (_root_.SheafOfModules.unit Y.ringCatSheaf) ≫ B.inv ≫ P.map A.inv) ≫
      P.map (restrictionUnitIso U.ι).hom ≫
        (schemeModulePullbackUnitIso (f ∣_ U)).hom = _
  simp only [Category.assoc]
  rw [htail, schemeModulePullbackUnit_eqToIso (morphismRestrict_ι f U).symm,
    schemeModulePullbackCompIso_unit]
  rw [← Category.assoc,
    ← (restrictionIsoPullback (f ⁻¹ᵁ U).ι).hom.naturality
      (schemeModulePullbackUnitIso f).hom]
  rw [Category.assoc, restrictionIsoPullback_unit]

/-- The same unit coherence with the source pullback-unit map inverted,
as required by the actual definition of a conormal equation map. -/
theorem schemeModuleOpenBaseChangeIso_unit_inv :
    (restriction (f ⁻¹ᵁ U).ι).map (schemeModulePullbackUnitIso f).inv ≫
      (schemeModuleOpenBaseChangeIso f U).hom.app
        (_root_.SheafOfModules.unit Y.ringCatSheaf) ≫
      (schemeModulePullback (f ∣_ U)).map (restrictionUnitIso U.ι).hom =
    (restrictionUnitIso (f ⁻¹ᵁ U).ι).hom ≫
      (schemeModulePullbackUnitIso (f ∣_ U)).inv := by
  have h := congrArg (fun g =>
    (restriction (f ⁻¹ᵁ U).ι).map (schemeModulePullbackUnitIso f).inv ≫
      g ≫ (schemeModulePullbackUnitIso (f ∣_ U)).inv)
    (schemeModuleOpenBaseChangeIso_unit f U)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.map_inv_hom_id_assoc] using h

-- Prove reassociation on abstract isomorphisms so that the kernel need not
-- check a simplifier proof expanding all concrete pullback constructions.
private theorem iso_hom_last_factor {D : Type*} [Category D]
    {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : D}
    (a : M₀ ≅ M₁) (b : M₁ ≅ M₂) (c : M₂ ≅ M₃)
    (d : M₃ ≅ M₄) (e : M₄ ≅ M₅) (k : M₅ ≅ M₆) :
    (a ≪≫ b ≪≫ c ≪≫ d ≪≫ e ≪≫ k).hom =
      (a ≪≫ b ≪≫ c ≪≫ d ≪≫ e).hom ≫ k.hom := by
  simp only [Iso.trans_hom, Category.assoc]

/-- The previously defined conormal restriction comparison is exactly
the actual open base-change map followed by the actual kernel comparison. -/
theorem schemeConormalRestrictionIso_hom_factor :
    (schemeConormalRestrictionIso f U).hom =
      (schemeModuleOpenBaseChangeIso f U).hom.app (schemeKernelIdeal f) ≫
        (schemeModulePullback (f ∣_ U)).map
          (schemeKernelRestrictionIso f U).hom := by
  let a := (restrictionIsoPullback (f ⁻¹ᵁ U).ι).app
    ((schemeModulePullback f).obj (schemeKernelIdeal f))
  let b := (schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f).app (schemeKernelIdeal f)
  let c := (eqToIso (congrArg schemeModulePullback
    (morphismRestrict_ι f U).symm)).app (schemeKernelIdeal f)
  let d := ((schemeModulePullbackCompIso (f ∣_ U) U.ι).app
    (schemeKernelIdeal f)).symm
  let e := (schemeModulePullback (f ∣_ U)).mapIso
    ((restrictionIsoPullback U.ι).app (schemeKernelIdeal f)).symm
  let k := (schemeModulePullback (f ∣_ U)).mapIso (schemeKernelRestrictionIso f U)
  change (a ≪≫ b ≪≫ c ≪≫ d ≪≫ e ≪≫ k).hom =
    (a ≪≫ b ≪≫ c ≪≫ d ≪≫ e).hom ≫ k.hom
  exact iso_hom_last_factor a b c d e k

/-- Restricting the actual global conormal equation map gives the
actual equation map of the restricted morphism, with its canonical unit
normalization and original restricted equation. -/
theorem schemeConormalRestrictionIso_generator (d : Γ(Y, ⊤))
    (hd : f.appTop d = 0) :
    (restriction (f ⁻¹ᵁ U).ι).map (schemeConormalGenerator f d hd) ≫
        (schemeConormalRestrictionIso f U).hom =
      (restrictionUnitIso (f ⁻¹ᵁ U).ι).hom ≫
        schemeConormalGenerator (f ∣_ U) (U.ι.appTop d)
          (restrictedEquation_eq_zero U f d hd) := by
  have hn := (schemeModuleOpenBaseChangeIso f U).hom.naturality
    (schemeKernelGenerator f d hd)
  change (restriction (f ⁻¹ᵁ U).ι).map
      ((schemeModulePullback f).map (schemeKernelGenerator f d hd)) ≫
      (schemeModuleOpenBaseChangeIso f U).hom.app (schemeKernelIdeal f) =
    (schemeModuleOpenBaseChangeIso f U).hom.app
        (_root_.SheafOfModules.unit Y.ringCatSheaf) ≫
      (schemeModulePullback (f ∣_ U)).map
        ((restriction U.ι).map (schemeKernelGenerator f d hd)) at hn
  simp only [schemeConormalGenerator, Functor.map_comp,
    schemeConormalRestrictionIso_hom_factor, Category.assoc]
  rw [← Category.assoc
    ((restriction (f ⁻¹ᵁ U).ι).map
      ((schemeModulePullback f).map (schemeKernelGenerator f d hd))), hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp, schemeKernelRestrictionIso_generator, Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun g => g ≫ (schemeModulePullback (f ∣_ U)).map
      (schemeKernelGenerator (f ∣_ U) (U.ι.appTop d)
        (restrictedEquation_eq_zero U f d hd)))
    (schemeModuleOpenBaseChangeIso_unit_inv f U)

end KltDP.Geometry
