import KltDP.Compatibility.OpensOverEquivalence
import KltDP.Geometry.ModuleOpenRestriction
import KltDP.Geometry.InvertibleSheaf

/-!
# Actual scheme-open charts and the over-site local-basis predicate

An actual module sheaf on an open subscheme gives a module sheaf on the
over site through the actual equivalence of opens. Its scalar map is the
original open immersion's structure map. This identifies the structure
module with the over-site unit and identifies an actual open restriction
with the original module's over-site restriction.

Consequently, actual scheme-open unit trivializations on a covering give
the existing literal singleton local-basis predicate. No invertibility
assumption or abstract identification of these two restrictions is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u v

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (U : X.Opens)

/-- The open-subspace equivalence is continuous also when its target
is written using the actual open subscheme's carrier. -/
local instance openToOverContinuous : Functor.IsContinuous.{v} U.overEquivalence.functor
    ((Opens.grothendieckTopology X).over U)
    (Opens.grothendieckTopology U.toScheme) := by
  let J := (Opens.grothendieckTopology X).over U
  let K := Opens.grothendieckTopology U.toScheme
  let F := U.overEquivalence.functor
  letI : F.IsDenseSubsite J K := Opens.overEquivalence_isDenseSubsite U
  letI := Functor.IsDenseSubsite.isCoverDense J K F
  letI := Functor.IsDenseSubsite.isLocallyFull J K F
  letI := Functor.IsDenseSubsite.isLocallyFaithful J K F
  exact Functor.IsCoverDense.isContinuous J K F
    (Functor.IsDenseSubsite.coverPreserving J K F)

/-- The actual structure map of the open immersion, read on its over
site. The functor sends an ambient subopen to its actual preimage. -/
def openToOverRingSheafHom : X.ringCatSheaf.over U ⟶
    (U.overEquivalence.functor.sheafPushforwardContinuous RingCat.{u}
      ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology U.toScheme)).obj U.toScheme.ringCatSheaf where
  val := whiskerLeft (Over.forget U).op
    (whiskerRight U.ι.c (forget₂ CommRingCat RingCat))

/-- Actual module sheaves on the open subscheme, read on the over site
with scalars supplied by the original structure map. -/
def openToOverFunctor : U.toScheme.Modules ⥤
    _root_.SheafOfModules.{u} (X.ringCatSheaf.over U) :=
  _root_.SheafOfModules.pushforward (F := U.overEquivalence.functor)
    (openToOverRingSheafHom U)

local instance (V : Over U) : IsIso (U.ι.app V.left) :=
  Scheme.Hom.isIso_app U.ι V.left (by simpa using V.hom.le)

/-- The actual ring map on every subopen of U is a ring isomorphism. -/
def openToOverUnitLinearEquiv (V : Over U) :
    (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj (op V) ≃ₗ[Γ(X, V.left)]
      ((openToOverFunctor U).obj
        (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf)).val.obj (op V) :=
  { (asIso (U.ι.app V.left)).commRingCatIsoToRingEquiv.toAddEquiv with
    map_smul' := fun r s => (U.ι.app V.left).hom.map_mul r s }

/-- The actual structure module on the open subscheme is the over-site
unit, through the original section-ring maps. -/
def openToOverUnitIso :
    _root_.SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      (openToOverFunctor U).obj (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf) :=
  (_root_.SheafOfModules.fullyFaithfulForget.{u} (X.ringCatSheaf.over U)).preimageIso
    (PresheafOfModules.isoMk
      (M₁ := (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)).val)
      (M₂ := ((openToOverFunctor U).obj
        (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf)).val)
      (fun V => (openToOverUnitLinearEquiv U V.unop).toModuleIso)
      (fun {V W} i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact ConcreteCategory.congr_hom (U.ι.c.naturality i.unop.left.op) s))

/-- An ambient subopen of U is exactly the image of its preimage in U. -/
theorem openImage_preimage (V : Over U) :
    U.ι ''ᵁ U.ι ⁻¹ᵁ V.left = V.left := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inter, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr (show V.left ≤ U from V.hom.le)

/-- The equality of actual opens, assembled before applying any module
presheaf or restriction-of-scalars functor. -/
def overToOpenIndexIso :
    (Over.forget U).op ≅ U.overEquivalence.functor.op ⋙ U.ι.opensFunctor.op :=
  NatIso.ofComponents
    (fun V => (eqToIso (openImage_preimage U V.unop)).op)
    (fun {V W} i => by
      apply Subsingleton.elim)

/-- The actual additive section comparison is the image of the original
open-index isomorphism under the original additive module presheaf. -/
def overToOpenRestrictionAdditiveIso (M : X.Modules) :
    (M.over U).val.presheaf ≅
      ((openToOverFunctor U).obj
        ((SchemeModuleRestriction.restriction U.ι).obj M)).val.presheaf :=
  isoWhiskerRight (overToOpenIndexIso U) M.val.presheaf

/-- The same actual section comparison is linear for the original
over-site scalar action. The inverse appIso in open restriction cancels
the actual open structure map. -/
def overToOpenRestrictionLinearEquiv (M : X.Modules) (V : Over U) :
    (M.over U).val.obj (op V) ≃ₗ[Γ(X, V.left)]
      ((openToOverFunctor U).obj
        ((SchemeModuleRestriction.restriction U.ι).obj M)).val.obj (op V) :=
  { ((overToOpenRestrictionAdditiveIso U M).app (op V)).addCommGroupIsoToAddEquiv with
    map_smul' := fun r m => by
      change M.val.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ V.left)
          (Set.image_preimage_subset _ _)).op (r • m) =
        (U.ι.appIso (U.ι ⁻¹ᵁ V.left)).inv (U.ι.app V.left r) •
          M.val.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ V.left)
            (Set.image_preimage_subset _ _)).op m
      rw [Scheme.Opens.ι_appIso]
      exact M.val.map_smul _ r m }

/-- Actual open restriction, read on the over site, is canonically
isomorphic to the original module's over-site restriction. -/
def openToOverRestrictionIso (M : X.Modules) :
    (openToOverFunctor U).obj ((SchemeModuleRestriction.restriction U.ι).obj M) ≅
      M.over U :=
  ((_root_.SheafOfModules.fullyFaithfulForget.{u} (X.ringCatSheaf.over U)).preimageIso
    (X := M.over U)
    (Y := (openToOverFunctor U).obj ((SchemeModuleRestriction.restriction U.ι).obj M))
    (PresheafOfModules.isoMk
      (M₁ := (M.over U).val)
      (M₂ := ((openToOverFunctor U).obj
        ((SchemeModuleRestriction.restriction U.ι).obj M)).val)
      (fun V => (overToOpenRestrictionLinearEquiv U M V.unop).toModuleIso)
      (fun {V W} i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        exact ConcreteCategory.congr_hom
          ((overToOpenRestrictionAdditiveIso U M).hom.naturality i) m))).symm

/-- An actual unit trivialization on the open subscheme gives a unit
trivialization in the existing over-site local-basis language. -/
def openChartToOverUnitIso (M : X.Modules)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      (SchemeModuleRestriction.restriction U.ι).obj M) :
    _root_.SheafOfModules.unit (X.ringCatSheaf.over U) ≅ M.over U :=
  openToOverUnitIso U ≪≫ (openToOverFunctor U).mapIso e ≪≫
    openToOverRestrictionIso U M

variable {U}

/-- An actual covering by open-subscheme unit trivializations gives an
actual atlas of singleton free presentations on the over sites. -/
def localTrivializationsOfOpenCharts (M : X.Modules) {ι : Type u}
    (V : ι → X.Opens) (hV : ∀ x : X, ∃ i, x ∈ V i)
    (e : ∀ i, _root_.SheafOfModules.unit (V i).toScheme.ringCatSheaf ≅
      (SchemeModuleRestriction.restriction (V i).ι).obj M) :
    KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M where
  I := ι
  X := V
  coversTop := by
    intro W x hx
    obtain ⟨i, hi⟩ := hV x
    exact ⟨W ⊓ V i, homOfLE inf_le_left,
      ⟨i, ⟨homOfLE inf_le_right⟩⟩, ⟨hx, hi⟩⟩
  iso i := _root_.SheafOfModules.freeUniqueIsoUnit
      (R := X.ringCatSheaf.over (V i)) PUnit ≪≫
    openChartToOverUnitIso (V i) M (e i)

/-- A sheaf which is actually isomorphic to the structure module near
every point is locally free of rank one in the original literal sense. -/
theorem isInvertible_of_openCharts (M : X.Modules)
    (hM : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅
        (SchemeModuleRestriction.restriction U.ι).obj M)) :
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M := by
  choose V hV e using hM
  exact (localTrivializationsOfOpenCharts M V (fun x => ⟨x, hV x⟩)
    (fun x => Classical.choice (e x))).isInvertible

end KltDP.Geometry
