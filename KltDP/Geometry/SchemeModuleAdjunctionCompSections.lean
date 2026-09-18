import KltDP.Geometry.SchemeModuleAdjunctionCompExplicit

/-!
# Section evaluation of the original composite adjunction comparison

The explicit original pushforward comparison is the identity on actual
sections. This calculation is made with an arbitrary original module,
before specialization to a concrete rational-function module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y Z : Scheme.{u}}

/-- Postcomposition by the original pushforward comparison leaves the
actual value on every original section unchanged. -/
theorem schemeModulePushforwardCompIso_postcompose_app
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (N : X.Modules)
    (b : M ⟶ (schemeModulePushforward g).obj ((schemeModulePushforward f).obj N))
    (U : Z.Opens) (s : M.val.obj (op U)) :
    (b ≫ (schemeModulePushforwardCompIso f g).hom.app N).val.app (op U) s =
      b.val.app (op U) s := by
  change ((schemeModulePushforwardCompIso f g).hom.app N).val.app (op U)
      (b.val.app (op U) s) = b.val.app (op U) s
  exact schemeModulePushforwardCompIso_hom_app f g N U (b.val.app (op U) s)

/-- The original iterated and composite adjoints agree on every original
section, with their sheaf comparison discharged only at section level. -/
theorem schemeModulePullbackCompIso_homEquiv_app
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (N : X.Modules)
    (a : (schemeModulePullback (f ≫ g)).obj M ⟶ N)
    (U : Z.Opens) (s : M.val.obj (op U)) :
    ((schemeModulePullbackPushforwardAdjunction g).homEquiv M
        ((schemeModulePushforward f).obj N)
      ((schemeModulePullbackPushforwardAdjunction f).homEquiv
        ((schemeModulePullback g).obj M) N
        ((schemeModulePullbackCompIso f g).hom.app M ≫ a))).val.app (op U) s =
      ((schemeModulePullbackPushforwardAdjunction (f ≫ g)).homEquiv M N a).val.app
        (op U) s := by
  let b := (schemeModulePullbackPushforwardAdjunction g).homEquiv M
    ((schemeModulePushforward f).obj N)
    ((schemeModulePullbackPushforwardAdjunction f).homEquiv
      ((schemeModulePullback g).obj M) N
      ((schemeModulePullbackCompIso f g).hom.app M ≫ a))
  have h := congrArg
    (fun q : M ⟶ (schemeModulePushforward (f ≫ g)).obj N =>
      q.val.app (op U) s)
    (schemeModulePullbackCompIso_homEquiv_pushforward f g M N a)
  exact (schemeModulePushforwardCompIso_postcompose_app f g M N b U s).symm.trans h

end KltDP.Geometry

#check @KltDP.Geometry.schemeModulePullbackCompIso_homEquiv_app
#print axioms KltDP.Geometry.schemeModulePullbackCompIso_homEquiv_app
