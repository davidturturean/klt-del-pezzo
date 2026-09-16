import KltDP.Geometry.RationalTreePicardPullbackGluedFrames

/-!
# Pulled-back sections through the comparison isomorphisms

BRIEF16/17, generic transport lemmas towards the frame-coordinate identity `PulledFrameCoordinate`,
stated over a variable sheaf of modules and proved by adjunction calculus only (lane D's method for
`hpull`, `F03_RESTRICTION_ADAPTERS.md` Task 11: every step is a `congrArg`, a generic `rfl`
identity, or an accepted adjunction lemma):

* `homEquiv_val_app_pulledSection`, `homEquiv_symm_val_app_pulledSection`: the pullback-adjunction
  transpose of `φ : f^*N ⟶ P` evaluates on a section as `φ` on the pulled-back section, and
  conversely for the inverse transpose (`Adjunction.homEquiv_unit`, triangle identity).
* `pullback_map_val_app_pulledSection`: `f^*φ` sends pulled-back sections to pulled-back sections.
* `compIso_hom_val_app_pulledSection`, `compIso_inv_val_app_pulledSection`: the composition
  comparison `schemeModulePullbackCompIso` identifies the doubly pulled-back section with the
  section pulled back along the composite (accepted `schemeModulePullbackCompIso_homEquiv_hom`).
* `unitIso_hom_val_app_pulledSection`: the structure-module comparison sends the pulled-back
  section of `r` to `f.app W r`.
* `eqToIso_hom_val_app_pulledSection`: the equality comparison for `e : f = g` transports pulled-back
  sections along the induced equality of preimage opens (by `subst` and the presheaf identity law).
* Evaluation lemmas for the open-subscheme/over-site comparisons on the top object
  (`openToOverUnitIso_hom_app_one'`, `openToOverUnitIso_inv_app_one'`,
  `openToOverRestrictionIso_inv_app'`, `openToOverRestrictionIso_hom_app_unit'`,
  `openToOverFunctor_map_val_app'`), the restriction adjunction's unit
  (`restrictionAdjunction_unit_app_val_app'`) and the restriction/pullback comparison on pulled-back
  sections (`restrictionIsoPullback_hom_app_unit'`, `restrictionIsoPullback_inv_app_pulledSection_unit'`).

These lemmas are used in `RationalTreePicardPulledFrameCoordinate` to prove the frame-coordinate
identity and hence `PullbackGluedClass`; build records in `LEMMA22_PROGRESS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

open SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Transport

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The transpose of a morphism out of a pullback evaluates on a section as the morphism on the
pulled-back section. -/
theorem homEquiv_val_app_pulledSection (N : X.Modules) (P : Y.Modules)
    (φ : (schemeModulePullback f).obj N ⟶ P) (W : X.Opens) (x : N.val.obj (op W)) :
    ((schemeModulePullbackPushforwardAdjunction f).homEquiv N P φ).val.app (op W) x =
      φ.val.app (op (f ⁻¹ᵁ W)) (pulledSection f N W x) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The inverse transpose of a morphism into a pushforward evaluates a pulled-back section as the
morphism on the original section. -/
theorem homEquiv_symm_val_app_pulledSection (N : X.Modules) (P : Y.Modules)
    (ψ : N ⟶ (schemeModulePushforward f).obj P) (W : X.Opens) (x : N.val.obj (op W)) :
    (((schemeModulePullbackPushforwardAdjunction f).homEquiv N P).symm ψ).val.app (op (f ⁻¹ᵁ W))
        (pulledSection f N W x) =
      ψ.val.app (op W) x := by
  have h := homEquiv_val_app_pulledSection f N P
    (((schemeModulePullbackPushforwardAdjunction f).homEquiv N P).symm ψ) W x
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The pullback of a morphism sends pulled-back sections to pulled-back sections. -/
theorem pullback_map_val_app_pulledSection {N N' : X.Modules} (φ : N ⟶ N') (W : X.Opens)
    (x : N.val.obj (op W)) :
    ((schemeModulePullback f).map φ).val.app (op (f ⁻¹ᵁ W)) (pulledSection f N W x) =
      pulledSection f N' W (φ.val.app (op W) x) :=
  congrArg (fun m : N ⟶ (schemeModulePushforward f).obj ((schemeModulePullback f).obj N') =>
    m.val.app (op W) x) ((schemeModulePullbackPushforwardAdjunction f).unit_naturality φ)

variable {Z : Scheme.{u}} (j : Z ⟶ Y)

/-- The composition comparison sends the doubly pulled-back section to the section pulled back
along the composite. -/
theorem compIso_hom_val_app_pulledSection (M : X.Modules) (W : X.Opens) (s : M.val.obj (op W)) :
    ((schemeModulePullbackCompIso j f).hom.app M).val.app (op (j ⁻¹ᵁ (f ⁻¹ᵁ W)))
        (pulledSection j ((schemeModulePullback f).obj M) (f ⁻¹ᵁ W) (pulledSection f M W s)) =
      pulledSection (j ≫ f) M W s := by
  have h : ((schemeModulePullbackPushforwardAdjunction f).homEquiv M
      ((schemeModulePushforward j).obj ((schemeModulePullback (j ≫ f)).obj M))
      ((schemeModulePullbackPushforwardAdjunction j).homEquiv
        ((schemeModulePullback f).obj M) ((schemeModulePullback (j ≫ f)).obj M)
        ((schemeModulePullbackCompIso j f).hom.app M))).val.app (op W) s =
      ((schemeModulePullbackPushforwardAdjunction (j ≫ f)).homEquiv M
        ((schemeModulePullback (j ≫ f)).obj M) (𝟙 _)).val.app (op W) s :=
    congrArg (fun m : M ⟶ (schemeModulePushforward f).obj ((schemeModulePushforward j).obj
      ((schemeModulePullback (j ≫ f)).obj M)) => m.val.app (op W) s)
      (schemeModulePullbackCompIso_homEquiv_hom j f M)
  have h1 := homEquiv_val_app_pulledSection f M
    ((schemeModulePushforward j).obj ((schemeModulePullback (j ≫ f)).obj M))
    ((schemeModulePullbackPushforwardAdjunction j).homEquiv
      ((schemeModulePullback f).obj M) ((schemeModulePullback (j ≫ f)).obj M)
      ((schemeModulePullbackCompIso j f).hom.app M)) W s
  have h2 := homEquiv_val_app_pulledSection j ((schemeModulePullback f).obj M)
    ((schemeModulePullback (j ≫ f)).obj M) ((schemeModulePullbackCompIso j f).hom.app M)
    (f ⁻¹ᵁ W) (pulledSection f M W s)
  have h3 := homEquiv_val_app_pulledSection (j ≫ f) M ((schemeModulePullback (j ≫ f)).obj M)
    (𝟙 _) W s
  exact h2.symm.trans (h1.symm.trans (h.trans h3))

/-- The inverse composition comparison sends the section pulled back along the composite to the
doubly pulled-back section. -/
theorem compIso_inv_val_app_pulledSection (M : X.Modules) (W : X.Opens) (s : M.val.obj (op W)) :
    ((schemeModulePullbackCompIso j f).inv.app M).val.app (op (j ⁻¹ᵁ (f ⁻¹ᵁ W)))
        (pulledSection (j ≫ f) M W s) =
      pulledSection j ((schemeModulePullback f).obj M) (f ⁻¹ᵁ W) (pulledSection f M W s) := by
  rw [← compIso_hom_val_app_pulledSection f j M W s]
  exact congrArg (fun m : (schemeModulePullback j).obj ((schemeModulePullback f).obj M) ⟶
      (schemeModulePullback j).obj ((schemeModulePullback f).obj M) =>
    m.val.app (op (j ⁻¹ᵁ (f ⁻¹ᵁ W)))
      (pulledSection j ((schemeModulePullback f).obj M) (f ⁻¹ᵁ W) (pulledSection f M W s)))
    ((schemeModulePullbackCompIso j f).hom_inv_id_app M)

/-- The structure-module comparison sends the pulled-back section of `r` to `f.app W r`. -/
theorem unitIso_hom_val_app_pulledSection (W : X.Opens) (r : Γ(X, W)) :
    (schemeModulePullbackUnitIso f).hom.val.app (op (f ⁻¹ᵁ W))
        (pulledSection f (_root_.SheafOfModules.unit X.ringCatSheaf) W r) =
      f.app W r := by
  change (schemeModulePullbackUnitHom f).val.app (op (f ⁻¹ᵁ W))
    (pulledSection f (_root_.SheafOfModules.unit X.ringCatSheaf) W r) = f.app W r
  rw [← structureToPushforwardUnit_app f W r]
  exact homEquiv_symm_val_app_pulledSection f (_root_.SheafOfModules.unit X.ringCatSheaf)
    (_root_.SheafOfModules.unit Y.ringCatSheaf) (structureToPushforwardUnit f) W r

/-- The equality comparison for `e : f = g` sends the section pulled back along `f` to the section
pulled back along `g`, transported along the induced equality of preimage opens. -/
theorem eqToIso_hom_val_app_pulledSection {f g : Y ⟶ X} (e : f = g) (M : X.Modules) (W : X.Opens)
    (s : M.val.obj (op W)) :
    (eqToIso (congrArg (fun m : Y ⟶ X => (schemeModulePullback m).obj M) e)).hom.val.app
        (op (f ⁻¹ᵁ W)) (pulledSection f M W s) =
      ((schemeModulePullback g).obj M).val.map
        (eqToHom (congrArg (fun m : Y ⟶ X => m ⁻¹ᵁ W) e)).op (pulledSection g M W s) := by
  subst e
  exact (ConcreteCategory.congr_hom
    (((schemeModulePullback f).obj M).val.presheaf.map_id (op (f ⁻¹ᵁ W)))
    (pulledSection f M W s)).symm

/-- Restriction of the structure module preserves `1`. -/
theorem unit_val_map_one' (Y : Scheme.{u}) {W W' : Y.Opens} (r : W' ⟶ W) :
    (_root_.SheafOfModules.unit Y.ringCatSheaf).val.map r.op (1 : Γ(Y, W)) = (1 : Γ(Y, W')) :=
  (Y.ringCatSheaf.val.map r.op).hom.map_one

end Transport

section SectionRfl

variable {Y : Scheme.{u}}

/-- Generic: evaluating a composite of module-sheaf morphisms on a section. -/
theorem pulledHom_comp_val_app {A B E : Y.Modules} (a : A ⟶ B) (b : B ⟶ E)
    (V : Y.Opensᵒᵖ) (x : A.val.obj V) :
    (a ≫ b).val.app V x = b.val.app V (a.val.app V x) := rfl

/-- Generic: evaluating a composite of over-site module morphisms on a section. -/
theorem overHom_comp_val_app {U : Y.Opens}
    {A B E : _root_.SheafOfModules.{u} (Y.ringCatSheaf.over U)} (a : A ⟶ B) (b : B ⟶ E)
    (V : (Over U)ᵒᵖ) (x : A.val.obj V) :
    (a ≫ b).val.app V x = b.val.app V (a.val.app V x) := rfl

/-- Generic: evaluating the identity over-site module morphism on a section. -/
theorem overHom_id_val_app {U : Y.Opens}
    (A : _root_.SheafOfModules.{u} (Y.ringCatSheaf.over U)) (V : (Over U)ᵒᵖ)
    (x : A.val.obj V) : (_root_.SheafOfModules.Hom.val (𝟙 A)).app V x = x := rfl

/-- Generic: an over-site module isomorphism cancels on sections (`inv ∘ hom`). -/
theorem overIso_inv_app_hom_app {U : Y.Opens}
    {A B : _root_.SheafOfModules.{u} (Y.ringCatSheaf.over U)} (e : A ≅ B) (V : (Over U)ᵒᵖ)
    (x : A.val.obj V) : e.inv.val.app V (e.hom.val.app V x) = x := by
  have h : ((e.hom ≫ e.inv).val.app V) x = (_root_.SheafOfModules.Hom.val (𝟙 A)).app V x :=
    congrArg (fun q : A ⟶ A => (_root_.SheafOfModules.Hom.val q).app V x) e.hom_inv_id
  exact (overHom_comp_val_app e.hom e.inv V x).symm.trans (h.trans (overHom_id_val_app A V x))

/-- Generic: an over-site module isomorphism cancels on sections (`hom ∘ inv`). -/
theorem overIso_hom_app_inv_app {U : Y.Opens}
    {A B : _root_.SheafOfModules.{u} (Y.ringCatSheaf.over U)} (e : A ≅ B) (V : (Over U)ᵒᵖ)
    (x : B.val.obj V) : e.hom.val.app V (e.inv.val.app V x) = x := by
  have h : ((e.inv ≫ e.hom).val.app V) x = (_root_.SheafOfModules.Hom.val (𝟙 B)).app V x :=
    congrArg (fun q : B ⟶ B => (_root_.SheafOfModules.Hom.val q).app V x) e.inv_hom_id
  exact (overHom_comp_val_app e.inv e.hom V x).symm.trans (h.trans (overHom_id_val_app B V x))

end SectionRfl

section OpenOver

variable {X : Scheme.{u}}

/-- The top object of the over site of an open. -/
abbrev overTop (U : X.Opens) : (Over U)ᵒᵖ := op (Over.mk (homOfLE (le_rfl : U ≤ U)))

/-- The over-site unit comparison on the top object is the structure map of the open; it sends
`1` to `1`. -/
theorem openToOverUnitIso_hom_app_one' (U : X.Opens) :
    (openToOverUnitIso U).hom.val.app (overTop U) (1 : Γ(X, U)) =
      (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U)) :=
  (U.ι.app U).hom.map_one

/-- The inverse over-site unit comparison on the top object sends `1` to `1`. -/
theorem openToOverUnitIso_inv_app_one' (U : X.Opens) :
    (openToOverUnitIso U).inv.val.app (overTop U) (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U)) = (1 : Γ(X, U)) :=
  (congrArg (fun y => (openToOverUnitIso U).inv.val.app (overTop U) y)
    (openToOverUnitIso_hom_app_one' U)).symm.trans
    (overIso_inv_app_hom_app (openToOverUnitIso U) (overTop U) (1 : Γ(X, U)))

/-- The over-site restriction comparison on the top object is the module restriction along the
equality `U.ι(U.ι⁻¹U) = U`. -/
theorem openToOverRestrictionIso_inv_app' (U : X.Opens) (N : X.Modules)
    (s : (N.over U).val.obj (overTop U)) :
    (openToOverRestrictionIso U N).inv.val.app (overTop U) s =
      N.val.map (eqToHom (openImage_preimage U (Over.mk (homOfLE (le_rfl : U ≤ U))))).op s := rfl

/-- Evaluating a pushed-forward morphism on the over site. -/
theorem openToOverFunctor_map_val_app' (U : X.Opens) {A B : U.toScheme.Modules} (φ : A ⟶ B)
    (V : Over U) (x : ((openToOverFunctor U).obj A).val.obj (op V)) :
    ((openToOverFunctor U).map φ).val.app (op V) x =
      φ.val.app (op (U.overEquivalence.functor.obj V)) x := rfl

/-- The restriction-adjunction unit restricts along the (unique) inclusion `f(f⁻¹U) ≤ U`. -/
theorem restrictionAdjunction_unit_app_val_app' {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (N : X.Modules) (U : X.Opens) (g : f ''ᵁ f ⁻¹ᵁ U ⟶ U) (s : N.val.obj (op U)) :
    ((restrictionAdjunction f).unit.app N).val.app (op U) s = N.val.map g.op s :=
  (show ((restrictionAdjunction f).unit.app N).val.app (op U) s =
      N.val.map (f.isOpenEmbedding.isOpenMap.adjunction.counit.app U).op s from rfl).trans
    (congrArg (fun g' : f ''ᵁ f ⁻¹ᵁ U ⟶ U => N.val.map g'.op s) (Subsingleton.elim _ g))

/-- The over-site restriction comparison sends the restriction-adjunction unit of a section back
to the section. -/
theorem openToOverRestrictionIso_hom_app_unit' (U : X.Opens) (N : X.Modules)
    (s : N.val.obj (op U)) :
    (openToOverRestrictionIso U N).hom.val.app (overTop U)
        (((restrictionAdjunction U.ι).unit.app N).val.app (op U) s) = s :=
  (congrArg (fun y => (openToOverRestrictionIso U N).hom.val.app (overTop U) y)
    ((restrictionAdjunction_unit_app_val_app' U.ι N U
      (eqToHom (openImage_preimage U (Over.mk (homOfLE (le_rfl : U ≤ U))))) s).trans
      (openToOverRestrictionIso_inv_app' U N s).symm)).trans
    (overIso_hom_app_inv_app (openToOverRestrictionIso U N) (overTop U) s)

/-- The restriction/pullback comparison sends the restriction-adjunction unit of a section to its
pulled-back section. -/
theorem restrictionIsoPullback_hom_app_unit' {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (N : X.Modules) (U : X.Opens) (s : N.val.obj (op U)) :
    ((restrictionIsoPullback f).hom.app N).val.app (op (f ⁻¹ᵁ U))
        (((restrictionAdjunction f).unit.app N).val.app (op U) s) =
      pulledSection f N U s :=
  congrArg
    (fun q : N ⟶ (schemeModulePushforward f).obj ((schemeModulePullback f).obj N) =>
      q.val.app (op U) s)
    (Adjunction.unit_leftAdjointUniq_hom_app (restrictionAdjunction f)
      (schemeModulePullbackPushforwardAdjunction f) N)

/-- The inverse restriction/pullback comparison sends a pulled-back section to the
restriction-adjunction unit of the section. -/
theorem restrictionIsoPullback_inv_app_pulledSection_unit' {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (N : X.Modules) (U : X.Opens) (s : N.val.obj (op U)) :
    ((restrictionIsoPullback f).inv.app N).val.app (op (f ⁻¹ᵁ U)) (pulledSection f N U s) =
      ((restrictionAdjunction f).unit.app N).val.app (op U) s := by
  have h2 : ((restrictionIsoPullback f).inv.app N).val.app (op (f ⁻¹ᵁ U))
      (((restrictionIsoPullback f).hom.app N).val.app (op (f ⁻¹ᵁ U))
        (((restrictionAdjunction f).unit.app N).val.app (op U) s)) =
      ((restrictionAdjunction f).unit.app N).val.app (op U) s :=
    congrArg (fun q : (restriction f).obj N ⟶ (restriction f).obj N =>
      q.val.app (op (f ⁻¹ᵁ U)) (((restrictionAdjunction f).unit.app N).val.app (op U) s))
      ((restrictionIsoPullback f).hom_inv_id_app N)
  rw [restrictionIsoPullback_hom_app_unit'] at h2
  exact h2

end OpenOver

end KltDP.Geometry.RationalTreePicard
