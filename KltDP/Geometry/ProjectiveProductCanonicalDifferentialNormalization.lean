import KltDP.Geometry.ProjectiveProductCanonicalDifferentials

/-!
# Section normalization of the original second projection differential

This retains the original normalization equation separately from the global
comparison map. The canonical-product chain uses the original maps directly;
it does not depend on this additional sectionwise normalization theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace KltDP.Geometry.ProjectiveProductCanonicalDifferentials

open SchemeKaehlerSheaf
open KltDP.Examples.FrobeniusProjectivePoints KltDP.Examples.FrobeniusGraphClosed

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k : Type u) [Field k]

private theorem transport_derivation {Y : Scheme.{u}}
    {f g : Y ⟶ Spec (CommRingCat.of k)} (h : f = g) (U : Y.Opens) (s : Γ(Y, U)) :
    (eqToHom (congrArg (fun t => baseRingSheaf t) h)).val.app (op U)
        ((baseRingDerivation f).d s) = (baseRingDerivation g).d s := by
  subst g
  rfl

private theorem module_comp_app {Y : Scheme.{u}} {A B C : Y.Modules}
    (a : A ⟶ B) (b : B ⟶ C) (U : Y.Opens) (s : A.val.obj (op U)) :
    (a ≫ b).val.app (op U) s = b.val.app (op U) (a.val.app (op U) s) := rfl

private theorem module_comp_app_of_eq {Y : Scheme.{u}} {A B C : Y.Modules}
    (a : A ⟶ B) (b : B ⟶ C) (U : Y.Opens)
    (s : A.val.obj (op U)) (t : B.val.obj (op U)) (v : C.val.obj (op U))
    (ha : a.val.app (op U) s = t) (hb : b.val.app (op U) t = v) :
    (a ≫ b).val.app (op U) s = v :=
  (module_comp_app a b U s).trans ((congrArg (b.val.app (op U)) ha).trans hb)

private theorem transported_map_unit_d {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X)
    (g : Y ⟶ Spec (CommRingCat.of k)) (h : j ≫ f = g)
    (U : X.Opens) (s : Γ(X, U)) :
    (SchemeKaehlerPullbackMap.map f j ≫
        eqToHom (congrArg (fun t => baseRingSheaf t) h)).val.app (op (j ⁻¹ᵁ U))
      (((schemeModulePullbackPushforwardAdjunction j).unit.app
        (baseRingSheaf f)).val.app (op U) ((baseRingDerivation f).d s)) =
      (baseRingDerivation g).d (j.app U s) :=
  module_comp_app_of_eq (SchemeKaehlerPullbackMap.map f j)
    (eqToHom (congrArg (fun t => baseRingSheaf t) h)) (j ⁻¹ᵁ U) _ _ _
    (SchemeKaehlerPullbackMap.map_unit_d f j U s)
    (transport_derivation k h (j ⁻¹ᵁ U) (j.app U s))

private theorem transported_map_unit_d_of_eq {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X)
    (g : Y ⟶ Spec (CommRingCat.of k)) (h : j ≫ f = g)
    (a : (schemeModulePullback j).obj (baseRingSheaf f) ⟶ baseRingSheaf g)
    (ha : a = SchemeKaehlerPullbackMap.map f j ≫
      eqToHom (congrArg (fun t => baseRingSheaf t) h))
    (U : X.Opens) (s : Γ(X, U)) :
    a.val.app (op (j ⁻¹ᵁ U))
      (((schemeModulePullbackPushforwardAdjunction j).unit.app
        (baseRingSheaf f)).val.app (op U) ((baseRingDerivation f).d s)) =
      (baseRingDerivation g).d (j.app U s) := by
  subst a
  exact transported_map_unit_d k f j g h U s

private def secondDifferential_unit_d_proof (U : (projectiveSpace k 1).Opens)
    (s : Γ(projectiveSpace k 1, U)) :=
  transported_map_unit_d k (projectiveSpaceToSpec k 1) secondProjection
    projectiveProductToSpec (secondProjection_structure k) U s

private abbrev statementOf {P : Prop} (_ : P) : Prop := P

/-- The second component has the same original normalization, after the actual base-map equality.
The transparent result type is precisely the original equation supplied by
`transported_map_unit_d`; its composite map is the defining original map of
`secondDifferential`, with the same proved fiber-product structure equality. -/
theorem secondDifferential_unit_d (U : (projectiveSpace k 1).Opens)
    (s : Γ(projectiveSpace k 1, U)) :
    statementOf (secondDifferential_unit_d_proof k U s) :=
  secondDifferential_unit_d_proof k U s

end KltDP.Geometry.ProjectiveProductCanonicalDifferentials
