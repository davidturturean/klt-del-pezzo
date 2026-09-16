import KltDP.Geometry.SchemeKaehlerPullbackSections

/-!
# The original Kähler pullback map for an arbitrary scheme morphism

Differentiate the original scheme section map and use the universal property
of the original Kähler sheaf. The resulting adjunct gives the actual
differential pullback map without an open-immersion hypothesis. It preserves
each original differential under the original pullback unit, and agrees with
the existing pullback isomorphism whenever the morphism is an open immersion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeKaehlerPullbackMap

open SchemeKaehlerSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X)

/-- Original base-ring scalar sections commute with the original scheme map. -/
theorem scalar_app (U : X.Opens) (a : k) :
    j.app U ((scalarPresheafHom f).app (op U) a) =
      (scalarPresheafHom (j ≫ f)).app (op (j ⁻¹ᵁ U)) a := by
  change j.app U (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a))) =
    Y.presheaf.map (homOfLE (show j ⁻¹ᵁ U ≤ ⊤ from le_top)).op
      (j.appTop (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)))
  exact ConcreteCategory.congr_hom
    (j.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a))

/-- The original derivative of the original forward section map, as a
derivation into the original pushforward module. -/
def pushforwardDerivation :
    ((schemeModulePushforward j).obj (baseRingSheaf (j ≫ f))).val.Derivation'
      (scalarPresheafHom f) where
  d {U} := (baseRingDerivation (j ≫ f)).d.comp (j.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b := by
    change (baseRingDerivation (j ≫ f)).d (j.app U.unop (a * b)) =
      j.app U.unop a • (baseRingDerivation (j ≫ f)).d (j.app U.unop b) +
        j.app U.unop b • (baseRingDerivation (j ≫ f)).d (j.app U.unop a)
    rw [(j.app U.unop).hom.map_mul]
    exact (baseRingDerivation (j ≫ f)).d_mul _ _
  d_map {U V} i s := by
    have h := ConcreteCategory.congr_hom (j.naturality i) s
    change (baseRingDerivation (j ≫ f)).d (j.app V.unop (X.presheaf.map i s)) =
      (baseRingSheaf (j ≫ f)).val.map ((Opens.map j.base).map i.unop).op
        ((baseRingDerivation (j ≫ f)).d (j.app U.unop s))
    exact (congrArg (baseRingDerivation (j ≫ f)).d h).trans
      ((baseRingDerivation (j ≫ f)).d_map _ _)
  d_app {U} a := by
    change (baseRingDerivation (j ≫ f)).d
      (j.app U.unop ((scalarPresheafHom f).app U a)) = 0
    rw [scalar_app]
    exact _root_.PresheafOfModules.Derivation'.d_app (baseRingDerivation (j ≫ f)) a

/-- The universal original Kähler map into the original pushforward. -/
def adjointMap : baseRingSheaf f ⟶
    (schemeModulePushforward j).obj (baseRingSheaf (j ≫ f)) :=
  SchemeKaehlerSheaf.desc (scalarPresheafHom f) (pushforwardDerivation f j)

theorem adjointMap_d (U : X.Opens) (s : Γ(X, U)) :
    (adjointMap f j).val.app (op U) ((baseRingDerivation f).d s) =
      (baseRingDerivation (j ≫ f)).d (j.app U s) :=
  _root_.PresheafOfModules.Derivation.congr_d
    (derivation_postcomp_desc (scalarPresheafHom f) (pushforwardDerivation f j)) s

/-- The actual differential map along an arbitrary original scheme morphism. -/
def map : (schemeModulePullback j).obj (baseRingSheaf f) ⟶ baseRingSheaf (j ≫ f) :=
  ((schemeModulePullbackPushforwardAdjunction j).homEquiv _ _).symm (adjointMap f j)

theorem map_homEquiv :
    (schemeModulePullbackPushforwardAdjunction j).homEquiv _ _ (map f j) =
      adjointMap f j :=
  ((schemeModulePullbackPushforwardAdjunction j).homEquiv _ _).apply_symm_apply _

/-- The original pullback unit sends a differential to the differential of
the original section image under this exact map. -/
theorem map_unit_d (U : X.Opens) (s : Γ(X, U)) :
    (map f j).val.app (op (j ⁻¹ᵁ U))
        (((schemeModulePullbackPushforwardAdjunction j).unit.app
          (baseRingSheaf f)).val.app (op U) ((baseRingDerivation f).d s)) =
      (baseRingDerivation (j ≫ f)).d (j.app U s) := by
  have h := congrArg (fun a => a.val.app (op U) ((baseRingDerivation f).d s))
    (map_homEquiv f j)
  exact h.trans (adjointMap_d f j U s)

/-- On actual open immersions this map is the existing original pullback
isomorphism's forward map. -/
theorem map_eq_pullbackIso [IsOpenImmersion j] :
    map f j = (SchemeKaehlerOpenRestriction.pullbackIso f j).hom := by
  apply ((schemeModulePullbackPushforwardAdjunction j).homEquiv _ _).injective
  rw [map_homEquiv, SchemeKaehlerOpenRestriction.pullbackIso_homEquiv]
  apply SchemeKaehlerSheaf.hom_ext (scalarPresheafHom f)
  ext U s
  change (adjointMap f j).val.app U ((baseRingDerivation f).d s) =
    (SchemeKaehlerOpenRestriction.adjointComparison f j).val.app U
      ((baseRingDerivation f).d s)
  rw [adjointMap_d, SchemeKaehlerOpenRestriction.adjointComparison_d]

end KltDP.Geometry.SchemeKaehlerPullbackMap
