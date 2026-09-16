import KltDP.Geometry.AffineOpenModuleDenominators
import KltDP.Geometry.PrimeCurvePullbackFrameCore

/-!
# Original sections through the actual open pullback

Compose the already proved restriction/pullback isomorphism with the
original image-open section comparison. This gives the actual additive
equivalence between pullback sections and original sections, retaining
restriction maps, module morphisms and the literal adjunction-unit section.

No affineness, quasicoherence or extension hypothesis is required. This is
the section comparison used to return affine twisted lifts to the original
ambient module sheaf before gluing.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeModuleOpenPullbackSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules)

/-- Actual pullback sections are the original sections over the actual image open. -/
def sectionsEquiv (V : Y.Opens) (W : X.Opens) (h : f ''ᵁ V = W) :
    ((schemeModulePullback f).obj M).val.obj (op V) ≃+ M.val.obj (op W) :=
  (((_root_.SheafOfModules.evaluation Y.ringCatSheaf (op V)).mapIso
      ((restrictionIsoPullback f).app M).symm).toLinearEquiv.toAddEquiv).trans
    (sectionsOfImageEq f M V W h)

/-- The equivalence uses precisely the original inverse pullback comparison. -/
theorem sectionsEquiv_apply (V : Y.Opens) (W : X.Opens) (h : f ''ᵁ V = W)
    (s : ((schemeModulePullback f).obj M).val.obj (op V)) :
    sectionsEquiv f M V W h s =
      sectionsOfImageEq f M V W h
        (((restrictionIsoPullback f).inv.app M).val.app (op V) s) := rfl

/-- The actual section equivalences commute with the original restriction maps. -/
theorem sectionsEquiv_naturality {V V' : Y.Opens} {W W' : X.Opens}
    (h : f ''ᵁ V = W) (h' : f ''ᵁ V' = W') (i : V' ≤ V) (j : W' ≤ W)
    (s : ((schemeModulePullback f).obj M).val.obj (op V)) :
    sectionsEquiv f M V' W' h'
        (((schemeModulePullback f).obj M).val.map (homOfLE i).op s) =
      M.val.map (homOfLE j).op (sectionsEquiv f M V W h s) := by
  subst W
  subst W'
  change ((restrictionIsoPullback f).inv.app M).val.app (op V')
      (((schemeModulePullback f).obj M).val.map (homOfLE i).op s) =
    M.val.map (homOfLE j).op (((restrictionIsoPullback f).inv.app M).val.app (op V) s)
  exact PresheafOfModules.naturality_apply ((restrictionIsoPullback f).inv.app M).val
    (homOfLE i).op s

/-- Applying an original module morphism agrees through the actual equivalence. -/
theorem sectionsEquiv_map {N : X.Modules} (g : M ⟶ N)
    (V : Y.Opens) (W : X.Opens) (h : f ''ᵁ V = W)
    (s : ((schemeModulePullback f).obj M).val.obj (op V)) :
    sectionsEquiv f N V W h (((schemeModulePullback f).map g).val.app (op V) s) =
      g.val.app (op W) (sectionsEquiv f M V W h s) := by
  subst W
  change ((restrictionIsoPullback f).inv.app N).val.app (op V)
      (((schemeModulePullback f).map g).val.app (op V) s) =
    g.val.app (op (f ''ᵁ V)) (((restrictionIsoPullback f).inv.app M).val.app (op V) s)
  exact congrArg (fun a : (schemeModulePullback f).obj M ⟶ (restriction f).obj N =>
    a.val.app (op V) s) ((restrictionIsoPullback f).inv.naturality g)

/-- A literal pulled section returns to its original restriction over the image. -/
theorem sectionsEquiv_pulledSection (U W : X.Opens)
    (h : f ''ᵁ (f ⁻¹ᵁ U) = W) (j : W ≤ U) (s : M.val.obj (op U)) :
    sectionsEquiv f M (f ⁻¹ᵁ U) W h (pullbackSection f M U s) =
      M.val.map (homOfLE j).op s := by
  subst W
  change ((restrictionIsoPullback f).inv.app M).val.app (op (f ⁻¹ᵁ U))
      (pullbackSection f M U s) = M.val.map (homOfLE j).op s
  exact restrictionIsoPullback_inv_app_pullbackSection f M U (homOfLE j) s

variable (U : X.Opens)

private theorem image_preimage_of_le {V : X.Opens} (hVU : V ≤ U) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inter,
    Scheme.Opens.opensRange_ι, inf_eq_right.mpr hVU]

/-- On a subopen of an original open chart, actual pullback and original
sections are additively equivalent. -/
def openSectionsEquiv {V : X.Opens} (hVU : V ≤ U) :
    ((schemeModulePullback U.ι).obj M).val.obj (op (U.ι ⁻¹ᵁ V)) ≃+
      M.val.obj (op V) :=
  sectionsEquiv U.ι M (U.ι ⁻¹ᵁ V) V (image_preimage_of_le U hVU)

/-- The actual open-chart equivalence inverts the literal section pullback. -/
theorem openSectionsEquiv_pulledSection {V : X.Opens} (hVU : V ≤ U)
    (s : M.val.obj (op V)) :
    openSectionsEquiv M U hVU (pullbackSection U.ι M V s) = s := by
  have h := sectionsEquiv_pulledSection U.ι M V V (image_preimage_of_le U hVU) le_rfl s
  calc
    _ = M.val.map (homOfLE (show V ≤ V from le_rfl)).op s := h
    _ = s := by
      change M.val.presheaf.map (𝟙 (op V)) s = s
      rw [CategoryTheory.Functor.map_id]
      rfl

end KltDP.Geometry.SchemeModuleOpenPullbackSections
