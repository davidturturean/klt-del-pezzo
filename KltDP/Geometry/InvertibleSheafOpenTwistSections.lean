import KltDP.Geometry.SchemeModuleOpenPullbackSections
import KltDP.Geometry.InvertibleSheafTwistPullback

/-!
# Original twisted sections on actual open charts

The actual tensor-power pullback comparison and the original open-section
equivalence return a chart's twisted section to the original ambient tensor
sheaf. Their restriction maps commute. The chart multiplication by the
original pulled power section is carried to the original ambient twist map.

These formulas retain both original coefficient modules and line sheaves.
They provide the section transport for the finite affine lifts; no agreement
on overlaps or global glued section is assumed or asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafOpenTwistSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance openTwistSectionsMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open InvertibleSheafSectionPowers InvertibleSheafTwistFrame
open InvertibleSheafTwistPullback SchemeModuleOpenPullbackSections

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
  (M : X.Modules) (L : InvertibleSheaf X)

/-- Actual chart twisted sections correspond to original ambient twisted
sections over the original image open. -/
def twistSectionsEquiv (n : ℕ) (V : Y.Opens) (W : X.Opens) (h : f ''ᵁ V = W) :
    ((schemeModulePullback f).obj M ⊗ (power (pullbackInvertibleSheaf f L) n).obj).val.obj
        (op V) ≃+ (M ⊗ (power L n).obj).val.obj (op W) :=
  (((_root_.SheafOfModules.evaluation Y.ringCatSheaf (op V)).mapIso
      (twistPullbackIso f M L n).symm).toLinearEquiv.toAddEquiv).trans
    (sectionsEquiv f (M ⊗ (power L n).obj) V W h)

/-- The section equivalence uses the original inverse tensor-power comparison. -/
theorem twistSectionsEquiv_apply (n : ℕ) (V : Y.Opens) (W : X.Opens)
    (h : f ''ᵁ V = W)
    (t : ((schemeModulePullback f).obj M ⊗
      (power (pullbackInvertibleSheaf f L) n).obj).val.obj (op V)) :
    twistSectionsEquiv f M L n V W h t =
      sectionsEquiv f (M ⊗ (power L n).obj) V W h
        ((twistPullbackIso f M L n).inv.val.app (op V) t) := rfl

/-- The actual twist section equivalences retain the original restriction maps. -/
theorem twistSectionsEquiv_naturality (n : ℕ) {V V' : Y.Opens} {W W' : X.Opens}
    (h : f ''ᵁ V = W) (h' : f ''ᵁ V' = W') (i : V' ≤ V) (j : W' ≤ W)
    (t : ((schemeModulePullback f).obj M ⊗
      (power (pullbackInvertibleSheaf f L) n).obj).val.obj (op V)) :
    twistSectionsEquiv f M L n V' W' h'
        (((schemeModulePullback f).obj M ⊗
          (power (pullbackInvertibleSheaf f L) n).obj).val.map (homOfLE i).op t) =
      (M ⊗ (power L n).obj).val.map (homOfLE j).op
        (twistSectionsEquiv f M L n V W h t) := by
  rw [twistSectionsEquiv_apply, twistSectionsEquiv_apply]
  exact (congrArg (sectionsEquiv f (M ⊗ (power L n).obj) V' W' h')
    (PresheafOfModules.naturality_apply (twistPullbackIso f M L n).inv.val
      (homOfLE i).op t)).trans
    (sectionsEquiv_naturality f (M ⊗ (power L n).obj) h h' i j _)

private theorem rightTwistMap_pullback_comp_inv (s : L.obj.sections) (n : ℕ) :
    rightTwistMap ((schemeModulePullback f).obj M) (pullbackInvertibleSheaf f L)
        (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) n ≫
      (twistPullbackIso f M L n).inv =
    (schemeModulePullback f).map (rightTwistMap M L s n) := by
  rw [← rightTwistMap_pullback f M L s n, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Multiplication by the original power section commutes with the
actual section equivalence for every section on every chart open. -/
theorem twistSectionsEquiv_rightTwistMap
    (s : L.obj.sections) (n : ℕ) (V : Y.Opens) (W : X.Opens)
    (h : f ''ᵁ V = W) (t : ((schemeModulePullback f).obj M).val.obj (op V)) :
    twistSectionsEquiv f M L n V W h
        ((rightTwistMap ((schemeModulePullback f).obj M) (pullbackInvertibleSheaf f L)
          (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) n).val.app (op V) t) =
      (rightTwistMap M L s n).val.app (op W) (sectionsEquiv f M V W h t) := by
  have hg := congrArg
    (fun a : (schemeModulePullback f).obj M ⟶
        (schemeModulePullback f).obj (M ⊗ (power L n).obj) => a.val.app (op V) t)
    (rightTwistMap_pullback_comp_inv f M L s n)
  change (twistPullbackIso f M L n).inv.val.app (op V)
      ((rightTwistMap ((schemeModulePullback f).obj M) (pullbackInvertibleSheaf f L)
        (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) n).val.app (op V) t) =
    ((schemeModulePullback f).map (rightTwistMap M L s n)).val.app (op V) t at hg
  rw [twistSectionsEquiv_apply, hg]
  exact sectionsEquiv_map f M (rightTwistMap M L s n) V W h t

/-- The original pulled section multiplied in the chart returns to the
original ambient twist map on the original restricted coefficient section. -/
theorem twistSectionsEquiv_rightTwistMap_pulledSection
    (s : L.obj.sections) (n : ℕ) (U W : X.Opens)
    (h : f ''ᵁ (f ⁻¹ᵁ U) = W) (j : W ≤ U) (t : M.val.obj (op U)) :
    twistSectionsEquiv f M L n (f ⁻¹ᵁ U) W h
        ((rightTwistMap ((schemeModulePullback f).obj M) (pullbackInvertibleSheaf f L)
          (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) n).val.app
            (op (f ⁻¹ᵁ U)) (pullbackSection f M U t)) =
      (rightTwistMap M L s n).val.app (op W) (M.val.map (homOfLE j).op t) := by
  rw [twistSectionsEquiv_rightTwistMap f M L s n (f ⁻¹ᵁ U) W h,
    sectionsEquiv_pulledSection f M U W h j t]

end KltDP.Geometry.InvertibleSheafOpenTwistSections
