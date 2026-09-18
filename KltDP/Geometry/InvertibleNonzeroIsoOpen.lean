import KltDP.Geometry.InvertibleNonzeroSections
import KltDP.Geometry.SchemeModuleOpenLocality

/-!
# A nonzero original line-bundle map is an isomorphism on a nonempty open

Take a common original rank-one frame where the actual morphism is nonzero.
Its original coefficient has a nonempty basic open. On every subopen of
that basic open, restriction makes the coefficient a unit, so the actual
component map is bijective. The accepted image-open restriction and pullback
comparison then makes the original scheme-module pullback an isomorphism.
No local coefficient, nonvanishing point, or chosen isomorphism is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleNonzeroIsoOpen

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitExtraction SchemeModuleRestriction

private theorem rankOne_coordinate {R P Q : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (eP : P ≃ₗ[R] R) (eQ : Q ≃ₗ[R] R) (g : P →ₗ[R] Q) (x : P) :
    eQ (g x) = eP x * eQ (g (eP.symm 1)) := by
  have hx : eP x • eP.symm 1 = x := by
    apply eP.injective
    rw [eP.map_smul, eP.apply_symm_apply, smul_eq_mul, mul_one]
  calc
    eQ (g x) = eQ (g (eP x • eP.symm 1)) := congrArg (fun y => eQ (g y)) hx.symm
    _ = _ := by rw [g.map_smul, eQ.map_smul, smul_eq_mul]

variable (X : Scheme.{u}) [IsIntegral X]

private theorem exists_nonzero_framed_component (L M : InvertibleSheaf X)
    (g : L.obj ⟶ M.obj) (hg : g ≠ 0) :
    ∃ (U : X.Opens) (_ : Nonempty U)
      (_ : L.obj.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
      (_ : M.obj.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)),
      g.val.app (op U) ≠ 0 := by
  classical
  by_contra! h
  apply hg
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change g.val.app W s = 0
  apply TopCat.Presheaf.IsSheaf.section_ext
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M.obj).cond
  intro x hx
  have hxL : x ∈ ⨆ i, L.localTrivializations.X i := by
    rw [invertibleSheafUnits_cover X L]
    trivial
  have hxM : x ∈ ⨆ i, M.localTrivializations.X i := by
    rw [invertibleSheafUnits_cover X M]
    trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxL
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hxM
  let V : X.Opens := W.unop ⊓ L.localTrivializations.X i ⊓ M.localTrivializations.X j
  have hxV : x ∈ V := ⟨⟨hx, hxi⟩, hxj⟩
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let eL := L.localTrivializations.unitIsoOver i
    (homOfLE (show V ≤ L.localTrivializations.X i from inf_le_left.trans inf_le_right))
  let eM := M.localTrivializations.unitIsoOver j
    (homOfLE (show V ≤ M.localTrivializations.X j from inf_le_right))
  let hVW : V ≤ W.unop := inf_le_left.trans inf_le_left
  refine ⟨V, hVW, hxV, ?_⟩
  change M.obj.val.map (homOfLE hVW).op (g.val.app W s) =
    M.obj.val.map (homOfLE hVW).op 0
  rw [map_zero, ← _root_.PresheafOfModules.naturality_apply,
    h V inferInstance eL eM]
  rfl

private def coefficient (L M : X.Modules) (g : L ⟶ M) (U : X.Opens)
    (eL : L.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (eM : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) : Γ(X, U) :=
  overTrivializationSectionEquiv X M U eM (𝟙 U)
    (g.val.app (op U) ((overTrivializationSectionEquiv X L U eL (𝟙 U)).symm 1))

private theorem coefficient_ne_zero (L M : X.Modules) (g : L ⟶ M) (U : X.Opens)
    (eL : L.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (eM : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (hg : g.val.app (op U) ≠ 0) : coefficient X L M g U eL eM ≠ 0 := by
  intro hc
  apply hg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply (overTrivializationSectionEquiv X M U eM (𝟙 U)).injective
  change overTrivializationSectionEquiv X M U eM (𝟙 U) (g.val.app (op U) s) =
    overTrivializationSectionEquiv X M U eM (𝟙 U) 0
  rw [map_zero, rankOne_coordinate]
  change _ * coefficient X L M g U eL eM = 0
  rw [hc, mul_zero]

private theorem coefficient_restrict (L M : X.Modules) (g : L ⟶ M) (U : X.Opens)
    (eL : L.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (eM : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    {V : X.Opens} (i : V ⟶ U) :
    overTrivializationSectionEquiv X M U eM i
      (g.val.app (op V) ((overTrivializationSectionEquiv X L U eL i).symm 1)) =
      X.presheaf.map i.op (coefficient X L M g U eL eM) := by
  have hgen : (overTrivializationSectionEquiv X L U eL i).symm 1 =
      L.val.map i.op ((overTrivializationSectionEquiv X L U eL (𝟙 U)).symm 1) := by
    apply (overTrivializationSectionEquiv X L U eL i).injective
    rw [LinearEquiv.apply_symm_apply]
    symm
    rw [overTrivializationSectionEquiv_naturality X L U eL (𝟙 U) i i (by simp),
      LinearEquiv.apply_symm_apply, map_one]
  rw [hgen, _root_.PresheafOfModules.naturality_apply]
  exact overTrivializationSectionEquiv_naturality X M U eM (𝟙 U) i i (by simp) _

private theorem component_bijective_of_unit_coefficient
    (L M : X.Modules) (g : L ⟶ M) (U : X.Opens)
    (eL : L.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (eM : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    {V : X.Opens} (i : V ⟶ U)
    (hc : IsUnit (X.presheaf.map i.op (coefficient X L M g U eL eM))) :
    Function.Bijective (g.val.app (op V)) := by
  let p := overTrivializationSectionEquiv X L U eL i
  let q := overTrivializationSectionEquiv X M U eM i
  have hcoord (s : L.val.obj (op V)) : q (g.val.app (op V) s) =
      p s * X.presheaf.map i.op (coefficient X L M g U eL eM) :=
    (rankOne_coordinate p q (g.val.app (op V)).hom s).trans
      (congrArg (fun c => p s * c) (coefficient_restrict X L M g U eL eM i))
  have hmul := IsUnit.isUnit_iff_mulRight_bijective.mp hc
  constructor
  · intro s t h
    apply p.injective
    apply hmul.1
    exact (hcoord s).symm.trans ((congrArg q h).trans (hcoord t))
  · intro t
    obtain ⟨r, hr⟩ := hmul.2 (q t)
    refine ⟨p.symm r, q.injective ?_⟩
    rw [hcoord, p.apply_symm_apply]
    exact hr

private theorem unit_on_subopen_basicOpen {U : X.Opens} (c : Γ(X, U))
    {V : X.Opens} (hV : V ≤ X.basicOpen c) :
    IsUnit (X.presheaf.map (homOfLE (hV.trans (X.basicOpen_le c))).op c) := by
  let a : X.basicOpen c ⟶ U := homOfLE (X.basicOpen_le c)
  let b : V ⟶ X.basicOpen c := homOfLE hV
  have hu := (X.toRingedSpace.isUnit_res_basicOpen c).map (X.presheaf.map b.op).hom
  have he : X.presheaf.map b.op (X.presheaf.map a.op c) =
      X.presheaf.map (homOfLE (hV.trans (X.basicOpen_le c))).op c := by
    calc
      _ = X.presheaf.map (a.op ≫ b.op) c :=
        (ConcreteCategory.congr_hom (X.presheaf.map_comp a.op b.op) c).symm
      _ = _ := congrArg (fun j => X.presheaf.map j c) (Subsingleton.elim _ _)
  exact he ▸ hu

private theorem pullback_isIso_of_subopen_bijective {L M : X.Modules}
    (g : L ⟶ M) (U : X.Opens)
    (h : ∀ (V : X.Opens), V ≤ U → Function.Bijective (g.val.app (op V))) :
    IsIso ((schemeModulePullback U.ι).map g) := by
  have hr : IsIso ((restriction U.ι).map g) := by
    apply KltDP.SheafOfModules.isIso_of_bijective_on_basis
      (B := fun V : U.toScheme.Opens => V)
    · apply Opens.isBasis_iff_nbhd.mpr
      intro V x hx
      exact ⟨V, ⟨V, rfl⟩, hx, le_rfl⟩
    · intro V
      change Function.Bijective (g.val.app (op (U.ι ''ᵁ V)))
      exact h _ (U.ι_image_le V)
  exact (NatIso.isIso_map_iff (restrictionIsoPullback U.ι) g).mp hr

/-- A nonzero original line-bundle map becomes an isomorphism on an actual nonempty open. -/
theorem exists_isIso_open (L M : InvertibleSheaf X) (g : L.obj ⟶ M.obj)
    (hg : g ≠ 0) :
    ∃ U : X.Opens, Nonempty U ∧ IsIso ((schemeModulePullback U.ι).map g) := by
  obtain ⟨U, hU, eL, eM, hne⟩ := exists_nonzero_framed_component X L M g hg
  let c : Γ(X, U) := coefficient X L.obj M.obj g U eL eM
  have hc : c ≠ 0 := coefficient_ne_zero X L.obj M.obj g U eL eM hne
  have hB : Nonempty (X.basicOpen c) := by
    by_contra hB
    exact hc ((basicOpen_eq_bot_iff c).mp
      ((Opens.not_nonempty_iff_eq_bot (X.basicOpen c)).mp
        (fun ⟨x, hx⟩ => hB ⟨⟨x, hx⟩⟩)))
  refine ⟨X.basicOpen c, hB, pullback_isIso_of_subopen_bijective X g (X.basicOpen c) ?_⟩
  intro V hV
  exact component_bijective_of_unit_coefficient X L.obj M.obj g U eL eM
    (homOfLE (hV.trans (X.basicOpen_le c))) (unit_on_subopen_basicOpen X c hV)

end KltDP.Geometry.InvertibleNonzeroIsoOpen
