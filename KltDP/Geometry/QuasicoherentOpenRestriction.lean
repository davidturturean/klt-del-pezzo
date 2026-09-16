/-
Original project adapters using the existing presentation and restriction
functors. Released under Apache 2.0; the upstream comparison and license
are recorded in docs/reuse_sources/quasicoherent_open_restriction/.
-/
import KltDP.Geometry.AffineQuasicoherentPresentationCover
import KltDP.Compatibility.SheafPresentationQuasicoherent

/-!
# Quasicoherence under actual open restriction

Pull back an original presentation cover along the open immersion.
The restricted presentations are compared through the equality of the
original composite scheme maps. The actual open-to-Over equivalence
then supplies presentations on the original Over sites of the source.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- A presentation on an actual open subscheme gives a presentation of
the original Over restriction, through its actual section comparison. -/
def overPresentationOfOpen {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (P : ((SchemeModuleRestriction.restriction U.ι).obj M).Presentation) :
    (M.over U).Presentation :=
  _root_.SheafOfModules.Presentation.ofIsIso (openToOverRestrictionIso U M).hom
    (P.map (openToOverFunctor U) (openToOverUnitIso U))

/-- A covering by actual open presentations gives the original
quasicoherent data, with the same cover and the same local modules. -/
def quasicoherentDataOfOpenPresentations {X : Scheme.{u}} (M : X.Modules)
    {I : Type u} (U : I → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (P : ∀ i, ((SchemeModuleRestriction.restriction (U i).ι).obj M).Presentation) :
    M.QuasicoherentData where
  I := I
  X := U
  coversTop := by
    intro W x hx
    obtain ⟨i, hi⟩ := hU x
    exact ⟨W ⊓ U i, homOfLE inf_le_left,
      ⟨i, ⟨homOfLE inf_le_right⟩⟩, ⟨hx, hi⟩⟩
  presentation i := overPresentationOfOpen M (U i) (P i)

namespace SchemeModuleRestriction

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- Restricting first to an ambient open and then along the restricted
morphism agrees with restriction along f followed by its actual preimage.
The comparison uses the equality of the original composite scheme maps. -/
def restrictionMorphismRestrictIso (U : X.Opens) :
    restriction U.ι ⋙ restriction (f ∣_ U) ≅
      restriction f ⋙ restriction (f ⁻¹ᵁ U).ι :=
  isoWhiskerRight (restrictionIsoPullback U.ι) (restriction (f ∣_ U)) ≪≫
    isoWhiskerLeft (schemeModulePullback U.ι) (restrictionIsoPullback (f ∣_ U)) ≪≫
    schemeModulePullbackCompIso (f ∣_ U) U.ι ≪≫
    eqToIso (congrArg schemeModulePullback (AlgebraicGeometry.morphismRestrict_ι f U)) ≪≫
    (schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f).symm ≪≫
    (isoWhiskerLeft (schemeModulePullback f)
      (restrictionIsoPullback (f ⁻¹ᵁ U).ι)).symm ≪≫
    (isoWhiskerRight (restrictionIsoPullback f)
      (restriction (f ⁻¹ᵁ U).ι)).symm

/-- The original open-immersion restriction preserves quasicoherence.
No affineness or quasi-compactness of the source is required. -/
instance isQuasicoherent_restriction (M : X.Modules) [M.IsQuasicoherent] :
    ((restriction f).obj M).IsQuasicoherent := by
  obtain ⟨I, U, _, hU, ⟨P⟩⟩ := exists_affine_open_presentations M
  let N := (restriction f).obj M
  let V : I → Y.Opens := fun i => f ⁻¹ᵁ U i
  have hV : ∀ y : Y, ∃ i, y ∈ V i := by
    intro y
    exact hU (f.base y)
  have P' (i : I) : ((restriction (V i).ι).obj N).Presentation := by
    let e := (restrictionMorphismRestrictIso f (U i)).app M
    exact _root_.SheafOfModules.Presentation.ofIsIso e.hom
      (presentationOpenRestriction (f ∣_ U i)
        ((restriction (U i).ι).obj M) (P i))
  change _root_.SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) N
  exact { nonempty_quasicoherentData :=
    ⟨quasicoherentDataOfOpenPresentations (X := Y) N V hV P'⟩ }

end SchemeModuleRestriction

end KltDP.Geometry
