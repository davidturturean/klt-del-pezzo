import KltDP.Geometry.CommonOpenCanonicalLocalFrame
import KltDP.Geometry.NormalModelLocalFrameRescale
import KltDP.Geometry.CanonicalPrincipalShiftOpenCoordinate
import KltDP.Geometry.CanonicalCoordinateOpenComposition
import KltDP.Geometry.CanonicalReferenceScalarTransport
import KltDP.Geometry.CommonTargetCanonicalNormalization
import KltDP.Geometry.CanonicalOpenCoordinateCongruence
import KltDP.Geometry.OpenImmersionNonemptyOverlap

/-!
# Normalizing the actual detected local frame through a target open

The original target lift supplies its own canonical divisor and normalized
coordinate. Equality of its extended Weil divisor with the target reference
produces the actual scalar, including its zero order on the original model.
An actual nonempty overlap and a principal correction then construct a frame
normalized to that reference, with the original source-frame order unchanged.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelFrameNormalization

open OpenImmersionRational DominantCartierPullback CartierRationalCoordinate
open NormalModelCanonical

attribute [local instance] integralSchemeStalk_isDomain
attribute [local irreducible] canonicalOpenPullbackIso

local instance frameOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (f : A ⟶ B) [IsOpenImmersion f] : GenericPointPreserving f :=
  ⟨genericPoint_eq_of_isOpenImmersion f⟩

local instance frameIntegralOpen {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

/-- A genuine target lift and equality of the original Weil extensions
construct a normalized frame without a scalar or order-comparison premise. -/
theorem exists_normalized_frame_of_target_lift
    {k : Type u} [Field k] [IsAlgClosed k] (S X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {V W : Scheme.{u}} [IsIntegral V] [IsIntegral W]
    (π : S.toScheme ⟶ X.toScheme) [GenericPointPreserving π]
    (v : V ⟶ X.toScheme) (iS : W ⟶ S.toScheme) (iV : W ⟶ V)
    [IsOpenImmersion iS] [IsOpenImmersion iV]
    (hcomm : iS ≫ π = iV ≫ v)
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (w : W) (x : V) (hwV : iV.base w = x)
    [IsDiscreteValuationRing (V.presheaf.stalk x)]
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (B U : X.toScheme.Opens) [Nonempty B.toScheme] [Nonempty U.toScheme]
    (b : B.toScheme ⟶ S.toScheme) [IsOpenImmersion b] (hb : b ≫ π = B.ι)
    (hB : ∀ C : X.PrimeCurve, C.genericPoint ∈ B)
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    (hext : OpenCartierWeil.restrictedWeilHom B (pullbackHom b KS) =
      OpenCartierWeil.restrictedWeilHom U KU) :
    ∃ F : LocalFrame (v ≫ X.structureMorphism) x,
      IsNormalized X U KU eKU v x F ∧
      F.order = (CommonOpenCanonicalLocalFrame.localFrame
        S X π v iS iV hcomm hπ w x hwV KS eKS).order := by
  let sW := iV ≫ (v ≫ X.structureMorphism)
  let sB := B.ι ≫ X.structureMorphism
  let sU := U.ι ≫ X.structureMorphism
  have hSW : iS ≫ S.structureMorphism = sW :=
    CanonicalExteriorCommonOpen.structure_eq X.structureMorphism π v
      S.structureMorphism (v ≫ X.structureMorphism) hπ rfl iS iV hcomm
  have hbbase : b ≫ S.structureMorphism = sB := by
    rw [← hπ, ← Category.assoc, hb]
  let DB := pullbackHom b KS
  let eB := canonicalOpenPullbackIso b S.structureMorphism sB hbbase KS eKS
  let T := B ⊓ U
  letI : Nonempty T.toScheme := CommonTargetCanonical.inf_nonempty X B U hB hU
  let h₁ : T.toScheme ⟶ B.toScheme := X.toScheme.homOfLE (show T ≤ B from inf_le_left)
  let h₂ : T.toScheme ⟶ U.toScheme := X.toScheme.homOfLE (show T ≤ U from inf_le_right)
  let sT := T.ι ≫ X.structureMorphism
  let E₁ := pullbackHom h₁ DB
  let E₂ := pullbackHom h₂ KU
  let e₁ := CommonTargetCanonical.canonicalRestrictionIso X B T inf_le_left DB eB
  let e₂ := CommonTargetCanonical.canonicalRestrictionIso X U T inf_le_right KU eKU
  obtain ⟨q, _, hcoordinate, horder⟩ :=
    CommonTargetCanonical.exists_coordinate_scalar_order_zero_on_models
      X B U hB hU DB KU eB eKU hext
  change coordinate T.toScheme E₂ _ e₂ =
    coordinate T.toScheme E₁ _ e₁ ≫ (rationalFunctionMulIso T.toScheme q).hom at hcoordinate
  let bT := h₁ ≫ b
  have hbT : bT ≫ π = T.ι := by
    dsimp only [bT, h₁]
    rw [Category.assoc, hb, Scheme.homOfLE_ι]
  obtain ⟨Z, hne, j, hj, hZ⟩ := exists_nonempty_open_overlap iS bT
  letI : Nonempty Z.toScheme := hne
  letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
  letI : IsOpenImmersion j := hj
  let sZ := Z.ι ≫ sW
  have hZtarget : Z.ι ≫ (iS ≫ π) = j ≫ T.ι := by
    rw [← Category.assoc, hZ, Category.assoc, hbT]
  have hjbase : j ≫ sT = sZ := by
    have hbaseMap : j ≫ T.ι = Z.ι ≫ (iV ≫ v) :=
      hZtarget.symm.trans (congrArg (fun a => Z.ι ≫ a) hcomm)
    simpa only [sT, sZ, sW, Category.assoc] using
      congrArg (fun a => a ≫ X.structureMorphism) hbaseMap
  have hh₁ : h₁ ≫ sB = sT :=
    CommonTargetCanonical.restriction_structure X B T inf_le_left
  have hh₂ : h₂ ≫ sU = sT :=
    CommonTargetCanonical.restriction_structure X U T inf_le_right
  have hjh₁ : (j ≫ h₁) ≫ sB = sZ := by rw [Category.assoc, hh₁, hjbase]
  have hmap : (j ≫ h₁) ≫ b = Z.ι ≫ iS :=
    (Category.assoc j h₁ b).trans hZ.symm
  have hmapbase : ((j ≫ h₁) ≫ b) ≫ S.structureMorphism = sZ := by
    rw [Category.assoc, hbbase, hjh₁]
  have hZS : (Z.ι ≫ iS) ≫ S.structureMorphism = sZ := by rw [Category.assoc, hSW]
  let F₀ := CommonOpenCanonicalLocalFrame.localFrame S X π v iS iV hcomm hπ w x hwV KS eKS
  let cZ := coordinate Z.toScheme (pullbackHom Z.ι F₀.divisor)
    (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sZ 2)
    (canonicalOpenPullbackIso Z.ι sW sZ rfl F₀.divisor F₀.canonicalIso)
  have hsource : coordinate Z.toScheme (pullbackHom j E₁)
      (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sZ 2)
      (canonicalOpenPullbackIso j sT sZ hjbase E₁ e₁) = cZ := by
    have ha := coordinate_canonicalOpenPullbackIso_comp j h₁ sB sT sZ hh₁ hjbase DB eB
    have hb' := coordinate_canonicalOpenPullbackIso_comp (j ≫ h₁) b
      S.structureMorphism sB sZ hbbase hjh₁ KS eKS
    have hc := coordinate_canonicalOpenPullbackIso_congr ((j ≫ h₁) ≫ b) (Z.ι ≫ iS)
      hmap S.structureMorphism sZ hmapbase hZS KS eKS
    have hd := coordinate_canonicalOpenPullbackIso_comp Z.ι iS
      S.structureMorphism sW sZ hSW rfl KS eKS
    exact ha.trans (hb'.trans (hc.trans hd.symm))
  let qW := Units.map (functionFieldMap (iS ≫ π)).hom.toMonoidHom
    (OpenCartierWeil.transportUnit T q)
  let F := F₀.rescale qW
  let jU := j ≫ h₂
  have htriangle : jU ≫ U.ι = (Z.ι ≫ iV) ≫ v := by
    change (j ≫ X.toScheme.homOfLE (show T ≤ U from inf_le_right)) ≫ U.ι = _
    rw [Category.assoc, Scheme.homOfLE_ι, ← hZtarget, hcomm, ← Category.assoc]
  have hjUbase : jU ≫ sU = sZ := by rw [Category.assoc, hh₂, hjbase]
  have hscaled : coordinate T.toScheme (rescaleDivisor T.toScheme E₁ q) _
      (rescaleIso T.toScheme E₁ _ e₁ q) = coordinate T.toScheme E₂ _ e₂ :=
    (coordinate_rescaleIso T.toScheme E₁ _ e₁ q).trans hcoordinate.symm
  have hpulled := canonicalOpenPullback_coordinate_congr sT sZ j hjbase
    (rescaleDivisor T.toScheme E₁ q) E₂ (rescaleIso T.toScheme E₁ _ e₁ q) e₂ hscaled
  have hrescale := coordinate_rescaleIso_openPullback j sT sZ hjbase E₁ e₁ q
  have hfinal := coordinate_canonicalOpenPullbackIso_comp j h₂ sU sT sZ hh₂ hjbase KU eKU
  have htarget : coordinate Z.toScheme (pullbackHom jU KU)
      (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sZ 2)
      (canonicalOpenPullbackIso jU sU sZ hjUbase KU eKU) =
      cZ ≫ (rationalFunctionMulIso Z.toScheme
        (Units.map (functionFieldIso j).hom.hom.toMonoidHom q)).hom :=
    hfinal.symm.trans (hpulled.symm.trans (hrescale.trans
      (congrArg (fun c => c ≫ (rationalFunctionMulIso Z.toScheme
        (Units.map (functionFieldIso j).hom.hom.toMonoidHom q)).hom) hsource)))
  have hscalar := CanonicalReferenceScalar.map_transportUnit_of_triangle
    X T (iS ≫ π) Z.ι j hZtarget q
  refine ⟨F, ?_, ?_⟩
  · refine ⟨Z, hne, jU, inferInstance, htriangle, ?_⟩
    have hnew := coordinate_rescaleIso_openPullback Z.ι sW sZ rfl
      F₀.divisor F₀.canonicalIso qW
    exact hnew.trans ((congrArg (fun r => cZ ≫ (rationalFunctionMulIso Z.toScheme r).hom)
      hscalar).trans htarget.symm)
  · letI : IsDiscreteValuationRing (W.presheaf.stalk w) :=
      stalk_isDiscreteValuationRing_of_isOpenImmersion iV w x hwV
    have hzero : stalkDivisorOrder W w qW = 0 := horder W (iS ≫ π) w
    have hF := F₀.rescale_order qW
    change F.order = F₀.order - stalkDivisorOrder W w qW at hF
    simpa only [hzero, sub_zero] using hF

end KltDP.Geometry.NormalModelFrameNormalization

#check @KltDP.Geometry.NormalModelFrameNormalization.exists_normalized_frame_of_target_lift
#print axioms KltDP.Geometry.NormalModelFrameNormalization.exists_normalized_frame_of_target_lift
