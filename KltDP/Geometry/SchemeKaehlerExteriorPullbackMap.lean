import KltDP.Geometry.SchemeKaehlerPullbackMap
import KltDP.Geometry.SchemeExteriorPowerPushforwardMap

/-!
# The original exterior differential pullback map

Apply the existing exterior functor to the original pushed-forward
Kähler differential, then the original pushforward exterior comparison.
The original scheme module adjunction gives the pullback map. Its unit
formula records the wedge of the derivatives of the original section images.
No smoothness, frame, or determinant-compatibility premise is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.SchemeKaehlerExteriorPullbackMap

open SchemeKaehlerSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X) (n : ℕ)

/-- The actual exterior of the actual pushed-forward differential map. -/
def adjointMap : SchemeExteriorPower.sheaf (baseRingSheaf f) n ⟶
    (schemeModulePushforward j).obj
      (SchemeExteriorPower.sheaf (baseRingSheaf (j ≫ f)) n) :=
  SchemeExteriorPower.map (SchemeKaehlerPullbackMap.adjointMap f j) n ≫
    SchemeExteriorPowerPushforwardMap.map j (baseRingSheaf (j ≫ f)) n

/-- It preserves the wedge of the actual differential images. -/
theorem adjointMap_wedge (U : X.Opens)
    (v : Fin n → (baseRingSheaf f).val.obj (op U)) :
    (adjointMap f j n).val.app (op U)
        (SchemeExteriorPower.wedge (baseRingSheaf f) n U v) =
      SchemeExteriorPower.wedge (baseRingSheaf (j ≫ f)) n (j ⁻¹ᵁ U)
        (fun i => (SchemeKaehlerPullbackMap.adjointMap f j).val.app (op U) (v i)) := by
  change (SchemeExteriorPowerPushforwardMap.map j (baseRingSheaf (j ≫ f)) n).val.app
      (op U) ((SchemeExteriorPower.map (SchemeKaehlerPullbackMap.adjointMap f j) n).val.app
        (op U) (SchemeExteriorPower.wedge (baseRingSheaf f) n U v)) = _
  rw [SchemeExteriorPower.map_wedge, SchemeExteriorPowerPushforwardMap.map_wedge]

/-- The actual pullback map on the original exterior differential sheaves. -/
def map :
    (schemeModulePullback j).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) n) ⟶
      SchemeExteriorPower.sheaf (baseRingSheaf (j ≫ f)) n :=
  ((schemeModulePullbackPushforwardAdjunction j).homEquiv _ _).symm (adjointMap f j n)

theorem map_homEquiv :
    (schemeModulePullbackPushforwardAdjunction j).homEquiv _ _ (map f j n) =
      adjointMap f j n :=
  ((schemeModulePullbackPushforwardAdjunction j).homEquiv _ _).apply_symm_apply _

/-- Original wedges of original differentials map to the wedge of the
original derivatives of their images, through the original pullback unit. -/
theorem map_unit_wedge_d (U : X.Opens) (s : Fin n → Γ(X, U)) :
    (map f j n).val.app (op (j ⁻¹ᵁ U))
        (((schemeModulePullbackPushforwardAdjunction j).unit.app
          (SchemeExteriorPower.sheaf (baseRingSheaf f) n)).val.app (op U)
            (SchemeExteriorPower.wedge (baseRingSheaf f) n U
              (fun i => (baseRingDerivation f).d (s i)))) =
      SchemeExteriorPower.wedge (baseRingSheaf (j ≫ f)) n (j ⁻¹ᵁ U)
        (fun i => (baseRingDerivation (j ≫ f)).d (j.app U (s i))) := by
  have h := congrArg (fun a => a.val.app (op U)
      (SchemeExteriorPower.wedge (baseRingSheaf f) n U
        (fun i => (baseRingDerivation f).d (s i)))) (map_homEquiv f j n)
  refine h.trans ((adjointMap_wedge f j n U
    (fun i => (baseRingDerivation f).d (s i))).trans ?_)
  apply congrArg (SchemeExteriorPower.wedge (baseRingSheaf (j ≫ f)) n (j ⁻¹ᵁ U))
  funext i
  exact SchemeKaehlerPullbackMap.adjointMap_d f j U (s i)

end KltDP.Geometry.SchemeKaehlerExteriorPullbackMap
