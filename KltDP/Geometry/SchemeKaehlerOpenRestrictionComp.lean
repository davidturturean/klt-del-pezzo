import KltDP.Geometry.SchemeKaehlerOpenRestriction
import KltDP.Geometry.ModuleRestrictionPullback
import KltDP.Geometry.SchemeModulePullbackCoherence

/-!
# Composition of the actual differential restriction isomorphisms

The restriction composition comparison is the original four-isomorphism
recipe through `restrictionIsoPullback` and `schemeModulePullbackCompIso`,
already used in `ProjectiveLineChartTriviality`. Its normalization follows
from the original restriction adjunctions and the proved pullback
composition normalization.

The adjoint of the actual differential restriction isomorphism sends
`d s` to `d (j.app U s)`. Thus the original scheme section-map composition
law proves composition of the actual differential restriction maps. The
canonical equality isomorphism retains the association of the original
structure morphisms. No replacement scalar map or coherence datum is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeKaehlerOpenRestriction

open SchemeKaehlerSheaf SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem homEquiv_leftAdjointUniq_comp
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G)
    (M : C) (N : D) (h : F'.obj M ⟶ N) :
    a.homEquiv M N ((Adjunction.leftAdjointUniq a b).hom.app M ≫ h) =
      b.homEquiv M N h := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_unit]

variable {X Y Z : Scheme.{u}}

/-- The existing restriction composition recipe through the original
restriction/pullback and pullback-composition isomorphisms. -/
def restrictionCompIso (j : Y ⟶ X) (l : Z ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion l] :
    restriction j ⋙ restriction l ≅ restriction (l ≫ j) :=
  isoWhiskerRight (restrictionIsoPullback j) (restriction l) ≪≫
    isoWhiskerLeft (schemeModulePullback j) (restrictionIsoPullback l) ≪≫
      schemeModulePullbackCompIso l j ≪≫ (restrictionIsoPullback (l ≫ j)).symm

set_option maxHeartbeats 1000000 in
/-- The original comparison is normalized by the two original
restriction adjunctions, for every destination and final morphism. -/
theorem restrictionCompIso_homEquiv (j : Y ⟶ X) (l : Z ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion l] (M : X.Modules) (N : Z.Modules)
    (a : (restriction (l ≫ j)).obj M ⟶ N) :
    (restrictionAdjunction j).homEquiv M ((schemeModulePushforward l).obj N)
      ((restrictionAdjunction l).homEquiv ((restriction j).obj M) N
        ((restrictionCompIso j l).hom.app M ≫ a)) =
      (restrictionAdjunction (l ≫ j)).homEquiv M N a := by
  change (restrictionAdjunction j).homEquiv M ((schemeModulePushforward l).obj N)
      ((restrictionAdjunction l).homEquiv ((restriction j).obj M) N
        ((restriction l).map ((restrictionIsoPullback j).hom.app M) ≫
          (restrictionIsoPullback l).hom.app ((schemeModulePullback j).obj M) ≫
            (schemeModulePullbackCompIso l j).hom.app M ≫
              (restrictionIsoPullback (l ≫ j)).inv.app M ≫ a)) = _
  rw [Adjunction.homEquiv_naturality_left]
  change (restrictionAdjunction j).homEquiv M ((schemeModulePushforward l).obj N)
      ((Adjunction.leftAdjointUniq (restrictionAdjunction j)
        (schemeModulePullbackPushforwardAdjunction j)).hom.app M ≫
          (restrictionAdjunction l).homEquiv ((schemeModulePullback j).obj M) N
            ((Adjunction.leftAdjointUniq (restrictionAdjunction l)
              (schemeModulePullbackPushforwardAdjunction l)).hom.app
                ((schemeModulePullback j).obj M) ≫
              (schemeModulePullbackCompIso l j).hom.app M ≫
                (restrictionIsoPullback (l ≫ j)).inv.app M ≫ a)) = _
  rw [homEquiv_leftAdjointUniq_comp, homEquiv_leftAdjointUniq_comp]
  refine (schemeModulePullbackCompIso_homEquiv l j M N
    ((restrictionIsoPullback (l ≫ j)).inv.app M ≫ a)).trans ?_
  change (schemeModulePullbackPushforwardAdjunction (l ≫ j)).homEquiv M N
      ((Adjunction.leftAdjointUniq
        (schemeModulePullbackPushforwardAdjunction (l ≫ j))
        (restrictionAdjunction (l ≫ j))).hom.app M ≫ a) = _
  exact homEquiv_leftAdjointUniq_comp _ _ M N a

variable {k : Type u} [CommRing k]
variable (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X) [IsOpenImmersion j]

/-- The forward restriction isomorphism differentiates the original
forward section-ring map on every image open. -/
theorem restrictionIso_hom_d (U : Y.Opens) (s : Γ(X, j ''ᵁ U)) :
    (restrictionIso f j).hom.val.app (op U) ((baseRingDerivation f).d s) =
      (baseRingDerivation (j ≫ f)).d ((j.appIso U).hom s) := by
  have hring := ConcreteCategory.congr_hom (j.appIso U).hom_inv_id s
  change (j.appIso U).inv ((j.appIso U).hom s) = s at hring
  have h := comparison_d f j U ((j.appIso U).hom s)
  rw [hring] at h
  refine (congrArg ((restrictionIso f j).hom.val.app (op U)) h.symm).trans ?_
  change ((restrictionIso f j).inv ≫ (restrictionIso f j).hom).val.app (op U)
    ((baseRingDerivation (j ≫ f)).d ((j.appIso U).hom s)) = _
  rw [Iso.inv_hom_id]
  rfl

/-- The adjoint of the actual differential restriction isomorphism
under the original open-restriction adjunction. -/
def adjointComparison : baseRingSheaf f ⟶
    (schemeModulePushforward j).obj (baseRingSheaf (j ≫ f)) :=
  (restrictionAdjunction j).homEquiv _ _ (restrictionIso f j).hom

set_option maxHeartbeats 1000000 in
/-- Its original section formula uses precisely the original scheme
section map, on arbitrary ambient opens. -/
theorem adjointComparison_d (U : X.Opens) (s : Γ(X, U)) :
    (adjointComparison f j).val.app (op U) ((baseRingDerivation f).d s) =
      (baseRingDerivation (j ≫ f)).d (j.app U s) := by
  let i : j ''ᵁ (j ⁻¹ᵁ U) ⟶ U :=
    homOfLE (Set.image_preimage_subset j.base (U : Set X))
  have hmap := (baseRingDerivation f).d_map i.op s
  have hmap' := congrArg
    (fun t : (baseRingSheaf f).val.obj (op (j ''ᵁ (j ⁻¹ᵁ U))) =>
      (restrictionIso f j).hom.val.app (op (j ⁻¹ᵁ U)) t) hmap.symm
  rw [adjointComparison, Adjunction.homEquiv_unit]
  change (restrictionIso f j).hom.val.app (op (j ⁻¹ᵁ U))
      ((baseRingSheaf f).val.map i.op ((baseRingDerivation f).d s)) = _
  refine hmap'.trans ?_
  refine (restrictionIso_hom_d f j (j ⁻¹ᵁ U) (X.presheaf.map i.op s)).trans ?_
  have hring : X.presheaf.map i.op ≫ (j.appIso (j ⁻¹ᵁ U)).hom = j.app U := by
    have hbase : j.app U ≫ (j.appIso (j ⁻¹ᵁ U)).inv = X.presheaf.map i.op :=
      j.app_appIso_inv U
    have h := congrArg (fun g => g ≫ (j.appIso (j ⁻¹ᵁ U)).hom) hbase.symm
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
  exact congrArg (fun t => (baseRingDerivation (j ≫ f)).d t)
    (ConcreteCategory.congr_hom hring s)

/-- Equality of the original structure morphisms transports their
original derivative maps by the canonical equality isomorphism. -/
theorem baseRingSheaf_eqToIso_hom_d {f₁ f₂ : X ⟶ Spec (CommRingCat.of k)}
    (h : f₁ = f₂) (U : X.Opens) (s : Γ(X, U)) :
    (eqToIso (congrArg baseRingSheaf h)).hom.val.app (op U)
        ((baseRingDerivation f₁).d s) = (baseRingDerivation f₂).d s := by
  subst f₂
  rfl

variable (l : Z ⟶ Y) [IsOpenImmersion l]

/-- The adjoint derivative maps compose by the original scheme section
map law, retaining the canonical reassociation of structure morphisms. -/
theorem adjointComparison_comp :
    adjointComparison f (l ≫ j) ≫
      (schemeModulePushforward (l ≫ j)).map
        (eqToIso (congrArg baseRingSheaf (Category.assoc l j f))).hom =
    adjointComparison f j ≫
      (schemeModulePushforward j).map (adjointComparison (j ≫ f) l) := by
  apply SchemeKaehlerSheaf.hom_ext (scalarPresheafHom f)
  ext U s
  change (eqToIso (congrArg baseRingSheaf (Category.assoc l j f))).hom.val.app
      (op ((l ≫ j) ⁻¹ᵁ U.unop))
      ((adjointComparison f (l ≫ j)).val.app U ((baseRingDerivation f).d s)) =
    (adjointComparison (j ≫ f) l).val.app (op (j ⁻¹ᵁ U.unop))
      ((adjointComparison f j).val.app U ((baseRingDerivation f).d s))
  rw [adjointComparison_d, baseRingSheaf_eqToIso_hom_d (Category.assoc l j f),
    adjointComparison_d, adjointComparison_d]
  exact congrArg (fun t => (baseRingDerivation (l ≫ (j ≫ f))).d t)
    (ConcreteCategory.congr_hom (Scheme.comp_app l j U.unop) s)

/-- The actual differential restriction isomorphisms compose through
the original module restriction comparison. -/
theorem restrictionIso_comp :
    (restrictionCompIso j l).app (baseRingSheaf f) ≪≫
        restrictionIso f (l ≫ j) ≪≫
          eqToIso (congrArg baseRingSheaf (Category.assoc l j f)) =
      (restriction l).mapIso (restrictionIso f j) ≪≫ restrictionIso (j ≫ f) l := by
  apply Iso.ext
  apply ((restrictionAdjunction l).homEquiv _ _).injective
  apply ((restrictionAdjunction j).homEquiv _ _).injective
  change (restrictionAdjunction j).homEquiv _ _
      ((restrictionAdjunction l).homEquiv _ _
        ((restrictionCompIso j l).hom.app (baseRingSheaf f) ≫
          (restrictionIso f (l ≫ j)).hom ≫
            (eqToIso (congrArg baseRingSheaf (Category.assoc l j f))).hom)) =
    (restrictionAdjunction j).homEquiv _ _
      ((restrictionAdjunction l).homEquiv _ _
        ((restriction l).map (restrictionIso f j).hom ≫
          (restrictionIso (j ≫ f) l).hom))
  rw [restrictionCompIso_homEquiv, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  exact adjointComparison_comp f j l

/-- The original derivative-preserving comparison maps compose, with
the canonical source association and original restriction comparison. -/
theorem comparison_comp :
    comparison (j ≫ f) l ≫ (restriction l).map (comparison f j) ≫
        (restrictionCompIso j l).hom.app (baseRingSheaf f) =
      (eqToIso (congrArg baseRingSheaf (Category.assoc l j f))).inv ≫
        comparison f (l ≫ j) := by
  let C := (restrictionCompIso j l).app (baseRingSheaf f)
  have h := congrArg (fun e :
      (restriction l).obj ((restriction j).obj (baseRingSheaf f)) ≅
        baseRingSheaf (l ≫ (j ≫ f)) => e.inv) (restrictionIso_comp f j l)
  have h' : (eqToIso (congrArg baseRingSheaf (Category.assoc l j f))).inv ≫
      comparison f (l ≫ j) ≫ C.inv =
        comparison (j ≫ f) l ≫ (restriction l).map (comparison f j) := by
    simpa only [Iso.trans_inv, Functor.mapIso_inv, restrictionIso_inv,
      Category.assoc] using h
  have hc := congrArg (fun a => a ≫ C.hom) h'
  simpa only [Category.assoc, C.inv_hom_id, Category.comp_id] using hc.symm

end KltDP.Geometry.SchemeKaehlerOpenRestriction
