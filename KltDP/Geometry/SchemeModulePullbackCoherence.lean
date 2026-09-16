import KltDP.Geometry.SchemeModuleFunctorial
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Associativity of the original scheme module pullback comparisons

The comparisons in this file are exactly `schemeModulePullbackCompIso`.
Their associativity is derived from their normalization under the actual
pullback/pushforward adjunctions. Equality of scheme morphisms is handled
by the canonical equality isomorphisms, on both adjoints.

Reuse audit: Mathlib at the project pin
`c44e0c8ee63ca166450922a373c7409c5d26b00b` already supplies
`Adjunction.comp_homEquiv`, `Adjunction.ofNatIsoRight`, and
`Adjunction.homEquiv_leftAdjointUniq_hom_app`. The two private normalizer
proofs below reuse the bounded proofs in `SchemeModuleUnitCoherence`.
The official Apache 2.0 source at
`5aedf732b6987e8c26ab3c9ebc855314f82b045f`,
`AlgebraicGeometry/Modules/Sheaf.lean:265` and
`Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:193`, proves the
corresponding associativity through the newer
`Adjunction.leftAdjointCompIso_assoc`, which is absent from the pin.
Those newer modules are not imported or copied. This adapter instead
uses the original comparisons and the pinned adjunction uniqueness API.
No coherence equation is supplied as an assumption or as additional data.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem homEquiv_leftAdjointUniq_comp
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G)
    (M : C) (N : D) (h : F'.obj M ⟶ N) :
    a.homEquiv M N ((Adjunction.leftAdjointUniq a b).hom.app M ≫ h) =
      b.homEquiv M N h := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_unit]

private theorem homEquiv_ofNatIsoRight_apply
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (a : F ⊣ G) (e : G ≅ H)
    (M : C) (N : D) (h : F.obj M ⟶ N) :
    (a.ofNatIsoRight e).homEquiv M N h = a.homEquiv M N h ≫ e.hom.app N := by
  rw [Adjunction.ofNatIsoRight, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- Compose a mapped equality before instantiating concrete hom-set expressions. -/
private theorem apply_eq_trans {A B : Type*} (k : A → B)
    {x y : A} {z : B} (hxy : x = y) (hyz : k y = z) : k x = z :=
  (congrArg k hxy).trans hyz

/-- Cancel the same three hom-set equivalences on two normalized maps. -/
private theorem eq_of_three_equiv {A B C D : Type*}
    (e₁ : A ≃ B) (e₂ : B ≃ C) (e₃ : C ≃ D) {x y : A} {z : D}
    (hx : e₃ (e₂ (e₁ x)) = z) (hy : e₃ (e₂ (e₁ y)) = z) : x = y :=
  e₁.injective (e₂.injective (e₃.injective (hx.trans hy.symm)))

variable {X Y Z W : Scheme.{u}}

/-- The original composition comparison is adjoint to the same map under
the composite adjunction. The actual pushforward comparison is the identity. -/
theorem schemeModulePullbackCompIso_homEquiv (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (N : X.Modules)
    (a : (schemeModulePullback (f ≫ g)).obj M ⟶ N) :
    (schemeModulePullbackPushforwardAdjunction g).homEquiv M
        ((schemeModulePushforward f).obj N)
      ((schemeModulePullbackPushforwardAdjunction f).homEquiv
        ((schemeModulePullback g).obj M) N
        ((schemeModulePullbackCompIso f g).hom.app M ≫ a)) =
      (schemeModulePullbackPushforwardAdjunction (f ≫ g)).homEquiv M N a := by
  have H := homEquiv_leftAdjointUniq_comp
    (((schemeModulePullbackPushforwardAdjunction g).comp
      (schemeModulePullbackPushforwardAdjunction f)).ofNatIsoRight
        (schemeModulePushforwardCompIso f g))
    (schemeModulePullbackPushforwardAdjunction (f ≫ g)) M N a
  change (((schemeModulePullbackPushforwardAdjunction g).comp
      (schemeModulePullbackPushforwardAdjunction f)).ofNatIsoRight
        (schemeModulePushforwardCompIso f g)).homEquiv M N
      ((schemeModulePullbackCompIso f g).hom.app M ≫ a) = _ at H
  rw [homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at H
  have hcomp : (schemeModulePushforwardCompIso f g).hom.app N =
      𝟙 ((schemeModulePushforward g).obj ((schemeModulePushforward f).obj N)) := rfl
  simpa only [Equiv.trans_apply, hcomp, Category.comp_id] using H

/-- The preceding normalization applied to the comparison map itself. -/
theorem schemeModulePullbackCompIso_homEquiv_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) :
    (schemeModulePullbackPushforwardAdjunction g).homEquiv M
        ((schemeModulePushforward f).obj ((schemeModulePullback (f ≫ g)).obj M))
      ((schemeModulePullbackPushforwardAdjunction f).homEquiv
        ((schemeModulePullback g).obj M) ((schemeModulePullback (f ≫ g)).obj M)
        ((schemeModulePullbackCompIso f g).hom.app M)) =
      (schemeModulePullbackPushforwardAdjunction (f ≫ g)).homEquiv M
        ((schemeModulePullback (f ≫ g)).obj M) (𝟙 _) := by
  simpa only [Category.comp_id] using
    schemeModulePullbackCompIso_homEquiv f g M
      ((schemeModulePullback (f ≫ g)).obj M) (𝟙 _)

/-- Equality transport for the actual adjunction, including the necessary
transport of its pushforward target. -/
theorem schemeModulePullback_homEquiv_eqToIso {f g : X ⟶ Y} (e : f = g)
    (M : Y.Modules) (N : X.Modules) (a : (schemeModulePullback g).obj M ⟶ N) :
    (schemeModulePullbackPushforwardAdjunction f).homEquiv M N
        ((eqToIso (congrArg (fun k => (schemeModulePullback k).obj M) e)).hom ≫ a) ≫
      (eqToIso (congrArg schemeModulePushforward e)).hom.app N =
        (schemeModulePullbackPushforwardAdjunction g).homEquiv M N a := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Category.comp_id]

/-- The actual pushforward functors compose strictly. Hence the equality
transport for reassociation acts by the identity. This uses the same
definitional pushforward comparison as `schemeModulePushforwardCompIso`. -/
theorem schemeModulePushforward_assoc_eqToIso_hom
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (N : X.Modules) :
    (eqToIso (congrArg schemeModulePushforward (Category.assoc f g h))).hom.app N =
      𝟙 ((schemeModulePushforward ((f ≫ g) ≫ h)).obj N) := by
  rfl

set_option maxHeartbeats 800000 in
/-- The composite through `g ≫ h` normalizes under the three original
adjunctions, with an arbitrary destination and final map. -/
private theorem pullback_assoc_left_homEquiv
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : W.Modules) (N : X.Modules)
    (a : (schemeModulePullback (f ≫ (g ≫ h))).obj M ⟶ N) :
    (schemeModulePullbackPushforwardAdjunction h).homEquiv M
      ((schemeModulePushforward g).obj ((schemeModulePushforward f).obj N))
      ((schemeModulePullbackPushforwardAdjunction g).homEquiv
        ((schemeModulePullback h).obj M) ((schemeModulePushforward f).obj N)
        ((schemeModulePullbackPushforwardAdjunction f).homEquiv
          ((schemeModulePullback g).obj ((schemeModulePullback h).obj M)) N
          ((schemeModulePullback f).map ((schemeModulePullbackCompIso g h).hom.app M) ≫
            (schemeModulePullbackCompIso f (g ≫ h)).hom.app M ≫ a))) =
      (schemeModulePullbackPushforwardAdjunction (f ≫ (g ≫ h))).homEquiv M N a := by
  have Hnatural := Adjunction.homEquiv_naturality_left
    (schemeModulePullbackPushforwardAdjunction f)
    ((schemeModulePullbackCompIso g h).hom.app M)
    ((schemeModulePullbackCompIso f (g ≫ h)).hom.app M ≫ a)
  have Hgh := schemeModulePullbackCompIso_homEquiv g h M
    ((schemeModulePushforward f).obj N)
    ((schemeModulePullbackPushforwardAdjunction f).homEquiv
      ((schemeModulePullback (g ≫ h)).obj M) N
      ((schemeModulePullbackCompIso f (g ≫ h)).hom.app M ≫ a))
  have Hfgh := schemeModulePullbackCompIso_homEquiv f (g ≫ h) M N a
  have Hmiddle := Hgh.trans Hfgh
  have Hnormalized := apply_eq_trans
    (fun b => (schemeModulePullbackPushforwardAdjunction h).homEquiv M
      ((schemeModulePushforward g).obj ((schemeModulePushforward f).obj N))
      ((schemeModulePullbackPushforwardAdjunction g).homEquiv
        ((schemeModulePullback h).obj M) ((schemeModulePushforward f).obj N) b))
    Hnatural Hmiddle
  exact Hnormalized

set_option maxHeartbeats 800000 in
private theorem pullback_assoc_right_homEquiv
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : W.Modules) (N : X.Modules)
    (a : (schemeModulePullback ((f ≫ g) ≫ h)).obj M ⟶ N) :
    (schemeModulePullbackPushforwardAdjunction h).homEquiv M
      ((schemeModulePushforward g).obj ((schemeModulePushforward f).obj N))
      ((schemeModulePullbackPushforwardAdjunction g).homEquiv
        ((schemeModulePullback h).obj M) ((schemeModulePushforward f).obj N)
        ((schemeModulePullbackPushforwardAdjunction f).homEquiv
          ((schemeModulePullback g).obj ((schemeModulePullback h).obj M)) N
          ((schemeModulePullbackCompIso f g).hom.app ((schemeModulePullback h).obj M) ≫
            (schemeModulePullbackCompIso (f ≫ g) h).hom.app M ≫ a))) =
      (schemeModulePullbackPushforwardAdjunction ((f ≫ g) ≫ h)).homEquiv M N a := by
  have Hfg := schemeModulePullbackCompIso_homEquiv f g
    ((schemeModulePullback h).obj M) N
    ((schemeModulePullbackCompIso (f ≫ g) h).hom.app M ≫ a)
  have Hfgh := schemeModulePullbackCompIso_homEquiv (f ≫ g) h M N a
  have Hnormalized := apply_eq_trans
    ((schemeModulePullbackPushforwardAdjunction h).homEquiv M
      ((schemeModulePushforward g).obj ((schemeModulePushforward f).obj N))) Hfg Hfgh
  exact Hnormalized

/-- Normalize the existing reassociation transport before specializing its target. -/
private theorem pullback_assoc_transport_homEquiv
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : W.Modules) (N : X.Modules)
    (a : (schemeModulePullback (f ≫ (g ≫ h))).obj M ⟶ N) :
    (schemeModulePullbackPushforwardAdjunction ((f ≫ g) ≫ h)).homEquiv M N
      ((eqToIso (congrArg (fun k => (schemeModulePullback k).obj M)
        (Category.assoc f g h))).hom ≫ a) =
      (schemeModulePullbackPushforwardAdjunction (f ≫ (g ≫ h))).homEquiv M N a := by
  have H := schemeModulePullback_homEquiv_eqToIso
    (Category.assoc f g h) M N a
  simpa only [schemeModulePushforward_assoc_eqToIso_hom, Category.comp_id] using H

set_option maxHeartbeats 800000 in
/-- Both canonical ways of composing three actual pullbacks agree, with
the canonical equality transport to the right-associated scheme composite. -/
theorem schemeModulePullbackCompIso_assoc
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (schemeModulePullback f).map ((schemeModulePullbackCompIso g h).hom.app M) ≫
        (schemeModulePullbackCompIso f (g ≫ h)).hom.app M =
      (schemeModulePullbackCompIso f g).hom.app ((schemeModulePullback h).obj M) ≫
        (schemeModulePullbackCompIso (f ≫ g) h).hom.app M ≫
          (eqToIso (congrArg (fun k => (schemeModulePullback k).obj M)
            (Category.assoc f g h))).hom := by
  let N := (schemeModulePullback (f ≫ (g ≫ h))).obj M
  let t : (schemeModulePullback ((f ≫ g) ≫ h)).obj M ⟶ N :=
    (eqToIso (congrArg (fun k => (schemeModulePullback k).obj M)
      (Category.assoc f g h))).hom
  have Hleft := pullback_assoc_left_homEquiv f g h M N (𝟙 N)
  have Hright := pullback_assoc_right_homEquiv f g h M N t
  have Htransport := pullback_assoc_transport_homEquiv f g h M N (𝟙 N)
  simp only [Category.comp_id] at Hleft Htransport
  have HrightNormalized := Hright.trans Htransport
  have Hresult := eq_of_three_equiv
    ((schemeModulePullbackPushforwardAdjunction f).homEquiv
      ((schemeModulePullback g).obj ((schemeModulePullback h).obj M)) N)
    ((schemeModulePullbackPushforwardAdjunction g).homEquiv
      ((schemeModulePullback h).obj M) ((schemeModulePushforward f).obj N))
    ((schemeModulePullbackPushforwardAdjunction h).homEquiv M
      ((schemeModulePushforward g).obj ((schemeModulePushforward f).obj N)))
    Hleft HrightNormalized
  exact Hresult

/-- The original composition comparison is compatible with equality
transport in both original scheme morphisms. -/
theorem schemeModulePullbackCompIso_eqToIso
    {f f' : X ⟶ Y} {g g' : Y ⟶ Z} (ef : f = f') (eg : g = g') (M : Z.Modules) :
    (schemeModulePullback f).map
        ((eqToIso (congrArg schemeModulePullback eg)).hom.app M) ≫
      (eqToIso (congrArg schemeModulePullback ef)).hom.app
        ((schemeModulePullback g').obj M) ≫
      (schemeModulePullbackCompIso f' g').hom.app M =
    (schemeModulePullbackCompIso f g).hom.app M ≫
      (eqToIso (congrArg schemeModulePullback
        (congrArg₂ (fun (a : X ⟶ Y) (b : Y ⟶ Z) => a ≫ b) ef eg))).hom.app M := by
  subst f'
  subst g'
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Category.comp_id]
  rw [(schemeModulePullback f).map_id ((schemeModulePullback g).obj M), Category.id_comp]

end KltDP.Geometry
