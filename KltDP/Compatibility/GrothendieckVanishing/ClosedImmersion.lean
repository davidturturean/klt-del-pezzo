/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent

Ported from Vilin97/MazurTheorem commit
9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/Upstream/LeanPool/GrothendieckVanishing/ClosedImmersion.lean.
Exact upstream source and license: audit/library_reuse/grothendieck_vanishing/.
-/

import KltDP.Compatibility.GrothendieckVanishing.ClosedImmersionBasics
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Exactness of pushforward along a closed inclusion

The proof uses actual stalks, the canonical pullback-pushforward adjunction,
and its kernel. On the closed subset the stalk map of the unit is an
isomorphism; off the subset its target is zero. This proves the actual unit
is an epimorphism and constructs its short exact kernel sequence.
-/

open CategoryTheory TopologicalSpace Opposite Limits

universe u

noncomputable section

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- In the pinned concrete category, a zero object has only the zero element. -/
private theorem addCommGrp_subsingleton_of_isZero {G : AddCommGrp.{u}} (h : IsZero G) :
    Subsingleton G := by
  refine subsingleton_of_forall_eq (0 : G) fun x => ?_
  simpa using congrArg (fun f : G ⟶ G => f x) (h.eq_of_src (𝟙 G) 0)

/-- The pinned site theorem specialized to the actual opens-site sheaves. -/
private theorem locallySurjective_iff_epi_addCommGrp
    {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrp.{u} X} (f : F ⟶ G) :
    TopCat.Presheaf.IsLocallySurjective f.val ↔ Epi f :=
  CategoryTheory.Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrp.{u}) f

/-- Stalks of a pushforward along a closed inclusion vanish outside the closed set:
    if `x ∉ s`, every element of `stalk(i_*(G), x)` is zero. -/
theorem pushforward_closedIncl_stalk_eq_zero
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {G : TopCat.Presheaf AddCommGrp.{u} (TopCat.of s)} (hG : G.IsSheaf)
    {x : X} (hx : x ∉ s)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrp.{u} x).obj
      ((TopCat.Presheaf.pushforward AddCommGrp.{u} (TopCat.closedIncl hs)).obj G)) :
    a = 0 := by
  let Gsh : TopCat.Sheaf AddCommGrp.{u} (TopCat.of s) := ⟨G, hG⟩
  let F' := (TopCat.Presheaf.pushforward AddCommGrp.{u} (TopCat.closedIncl hs)).obj G
  obtain ⟨U, hxU, sU, rfl⟩ := F'.germ_exist x a
  let W : Opens X := U ⊓ ⟨sᶜ, hs.isOpen_compl⟩
  have hW_map : (Opens.map (TopCat.closedIncl hs)).obj W = ⊥ :=
    TopCat.closedIncl_map_eq_bot_of_le_compl (hs := hs) (U := W) inf_le_right
  haveI : Subsingleton (F'.obj (op W)) := addCommGrp_subsingleton_of_isZero (by
    change IsZero (G.obj (op ((Opens.map (TopCat.closedIncl hs)).obj W)))
    rw [hW_map]
    exact Gsh.isTerminalOfEmpty.isZero)
  rw [← TopCat.Presheaf.germ_res_apply F'
    (homOfLE (show W ≤ U from inf_le_left)) x ⟨hxU, hx⟩ sU]
  rw [Subsingleton.eq_zero (ConcreteCategory.hom (F'.map (homOfLE (show W ≤ U from
    inf_le_left)).op) sU)]
  exact map_zero _

/-- Pushforward along a closed immersion preserves epis: if `f : F ⟶ G` is epi in
    presheaves on the closed subspace, then `i_*(f)` is epi in sheaves on the ambient
    space whenever `f` is locally surjective.
    Proof: stalkwise surjectivity (identity on the closed set, zero outside). -/
theorem epi_pushforward_map_closedIncl_of_locallySurjective
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {F G : TopCat.Presheaf AddCommGrp.{u} (TopCat.of s)}
    (hF : F.IsSheaf) (hG : G.IsSheaf)
    (f : F ⟶ G)
    (hf_loc : TopCat.Presheaf.IsLocallySurjective f) :
    Epi ((TopCat.Sheaf.pushforward AddCommGrp.{u}
      (TopCat.closedIncl hs)).map (show
        (⟨F, hF⟩ : TopCat.Sheaf AddCommGrp.{u} (TopCat.of s)) ⟶
          (⟨G, hG⟩ : TopCat.Sheaf AddCommGrp.{u} (TopCat.of s)) from
            ⟨f⟩)) := by
  let fsh : (⟨F, hF⟩ : TopCat.Sheaf AddCommGrp.{u} (TopCat.of s)) ⟶
      (⟨G, hG⟩ : TopCat.Sheaf AddCommGrp.{u} (TopCat.of s)) := ⟨f⟩
  letI : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) :=
    balanced_of_strongEpiCategory
  change Epi ((TopCat.Sheaf.pushforward AddCommGrp.{u}
      (TopCat.closedIncl hs)).map fsh)
  rw [← locallySurjective_iff_epi_addCommGrp
    ((TopCat.Sheaf.pushforward AddCommGrp.{u}
      (TopCat.closedIncl hs)).map fsh)]
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x; by_cases hx : (x : X) ∈ s
  · let z : TopCat.of s := ⟨x, hx⟩
    haveI hEpiF : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrp.{u} z).map f) :=
      (AddCommGrp.epi_iff_surjective _).mpr
        (((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
            (T := f)).mp hf_loc) z)
    have hnat : (TopCat.Presheaf.stalkFunctor AddCommGrp.{u}
        ((TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrp.{u} (TopCat.closedIncl hs)).map f) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrp.{u} (TopCat.closedIncl hs) G z =
    TopCat.Presheaf.stalkPushforward AddCommGrp.{u} (TopCat.closedIncl hs) F z ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrp.{u} z).map f := by
      apply TopCat.Presheaf.stalk_hom_ext; intro U hU
      erw [← Category.assoc]
      rw [TopCat.Presheaf.stalkFunctor_map_germ U ((TopCat.closedIncl hs) z) hU
        ((TopCat.Presheaf.pushforward AddCommGrp.{u} (TopCat.closedIncl hs)).map f)]
      erw [Category.assoc]
      erw [TopCat.Presheaf.stalkPushforward_germ]
      erw [TopCat.Presheaf.stalkPushforward_germ_assoc]
      erw [TopCat.Presheaf.stalkFunctor_map_germ]
      rfl
    apply (AddCommGrp.epi_iff_surjective _).mp
    change Epi ((TopCat.Presheaf.stalkFunctor AddCommGrp.{u}
        ((TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrp.{u} (TopCat.closedIncl hs)).map f))
    haveI : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrp.{u}
        (TopCat.closedIncl hs) F z) :=
      TopCat.closedIncl_stalkPushforward_isIso (hs := hs)
    haveI : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrp.{u}
        (TopCat.closedIncl hs) G z) :=
      TopCat.closedIncl_stalkPushforward_isIso (hs := hs)
    have hcomp : Epi (TopCat.Presheaf.stalkPushforward AddCommGrp.{u}
        (TopCat.closedIncl hs) F z ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrp.{u} z).map f) :=
      @epi_comp _ _ _ _ _
        (TopCat.Presheaf.stalkPushforward AddCommGrp.{u} (TopCat.closedIncl hs) F z)
        (inferInstance : Epi (TopCat.Presheaf.stalkPushforward AddCommGrp.{u}
          (TopCat.closedIncl hs) F z))
        ((TopCat.Presheaf.stalkFunctor AddCommGrp.{u} z).map f)
        hEpiF
    have hcomp' : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrp.{u}
        ((TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrp.{u} (TopCat.closedIncl hs)).map f) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrp.{u} (TopCat.closedIncl hs) G z) := by
      rw [hnat]; exact hcomp
    letI := hcomp'
    have hcancel := epi_comp
      ((TopCat.Presheaf.stalkFunctor AddCommGrp.{u}
        ((TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrp.{u} (TopCat.closedIncl hs)).map f) ≫
        TopCat.Presheaf.stalkPushforward AddCommGrp.{u} (TopCat.closedIncl hs) G z)
      (inv (TopCat.Presheaf.stalkPushforward AddCommGrp.{u}
        (TopCat.closedIncl hs) G z))
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using hcancel
  · intro b
    rw [pushforward_closedIncl_stalk_eq_zero (hs := hs) (G := G) hG hx b]
    exact ⟨0, AddMonoidHom.map_zero _⟩

instance closedIncl_pushforward_preservesEpis
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    (TopCat.Sheaf.pushforward AddCommGrp.{u}
      (TopCat.closedIncl hs)).PreservesEpimorphisms where
  preserves {F G} f hf := by
    letI : Epi f := hf
    letI : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) :=
      balanced_of_strongEpiCategory
    have hf_loc : TopCat.Presheaf.IsLocallySurjective f.val :=
      (locallySurjective_iff_epi_addCommGrp f).mpr inferInstance
    change Epi ((TopCat.Sheaf.pushforward AddCommGrp.{u}
      (TopCat.closedIncl hs)).map (⟨f.val⟩))
    exact epi_pushforward_map_closedIncl_of_locallySurjective
      (hs := hs) (F := F.val) (G := G.val) F.cond G.cond f.val hf_loc

instance closedIncl_pushforward_preservesMonos
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    (TopCat.Sheaf.pushforward AddCommGrp.{u}
      (TopCat.closedIncl hs)).PreservesMonomorphisms := inferInstance

/-- Pushforward along a closed immersion preserves short exact sequences. -/
theorem closedIncl_pushforward_shortExact
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {S : ShortComplex (TopCat.Sheaf AddCommGrp.{u} (TopCat.of s))}
    (hSE : S.ShortExact) :
    (S.map (TopCat.Sheaf.pushforward AddCommGrp.{u}
        (TopCat.closedIncl hs))).ShortExact := by
  let F := TopCat.Sheaf.pushforward AddCommGrp.{u} (TopCat.closedIncl hs)
  haveI := hSE.mono_f
  haveI := hSE.epi_g
  haveI : Mono (F.map S.f) := inferInstance
  haveI : Epi (F.map S.g) := inferInstance
  exact ShortComplex.ShortExact.mk'
    (hSE.exact.map_of_mono_of_preservesKernel _ hSE.mono_f inferInstance) ‹_› ‹_›

namespace TopCat

-- Stalk pullback hom naturality
lemma stalkPullbackHom_naturality
    {C : Type*} [Category C] [HasColimits C]
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F G : Y.Presheaf C} (α : F ⟶ G) (x : ↑X) :
    (Presheaf.stalkFunctor C (ConcreteCategory.hom f x)).map α ≫
      Presheaf.stalkPullbackHom C f G x =
    Presheaf.stalkPullbackHom C f F x ≫
      (Presheaf.stalkFunctor C x).map
        ((Presheaf.pullback C f).map α) := by
  apply Presheaf.stalk_hom_ext; intro U hU
  have key : α.app (Opposite.op U) ≫
      ((Presheaf.pushforwardPullbackAdjunction C f).unit.app G).app (Opposite.op U) =
    ((Presheaf.pushforwardPullbackAdjunction C f).unit.app F).app (Opposite.op U) ≫
      ((Presheaf.pullback C f).map α).app
        (Opposite.op ((TopologicalSpace.Opens.map f).obj U)) := by
    have h := congr_arg (fun β ↦ NatTrans.app β (Opposite.op U))
      ((Presheaf.pushforwardPullbackAdjunction C f).unit.naturality α)
    dsimp at h ⊢
    exact h
  erw [← Category.assoc]
  rw [Presheaf.stalkFunctor_map_germ U ((ConcreteCategory.hom f) x) hU α]
  erw [Category.assoc]
  erw [Presheaf.germ_stalkPullbackHom]
  erw [Presheaf.germ_stalkPullbackHom_assoc]
  erw [← Category.assoc]
  rw [key]
  erw [Presheaf.stalkFunctor_map_germ]
  exact Category.assoc _ _ _

-- Unit stalk is iso for closed immersions.
-- Proof chain: triangle identity → pullback.map(η) iso → pullbackIso naturality
-- → toSheafify naturality → stalkPullbackHom_naturality → η stalk iso
theorem closedIncl_unit_stalk_isIso
    {C : Type*} [Category.{u} C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (forget C)]
    [PreservesFilteredColimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    (F : TopCat.Sheaf C X) (x : TopCat.of s) :
    IsIso ((Presheaf.stalkFunctor C ((closedIncl hs) x)).map
      ((Sheaf.pullbackPushforwardAdjunction C (closedIncl hs)).unit.app
        F).val) := by
  -- Use the triangle identity + counit iso
  let i := closedIncl hs
  let adj := Sheaf.pullbackPushforwardAdjunction C i
  let pb := Sheaf.pullback C i
  let η := adj.unit.app F
  haveI hCounit : IsIso (adj.counit.app (pb.obj F)) :=
    closedIncl_counit_isIso (C := C) (hs := hs) (pb.obj F)
  haveI hId : IsIso (𝟙 (pb.obj F)) := IsIso.id _
  haveI hEta : IsIso (pb.map η) :=
    @IsIso.of_isIso_fac_right (TopCat.Sheaf C (TopCat.of s)) _ _ _ _
      (pb.map η) (adj.counit.app (pb.obj F)) (𝟙 (pb.obj F))
      hCounit hId (adj.left_triangle_components F)
  -- Step 2: val stalk of pb.map(η) is iso
  haveI hEtaHom : IsIso (pb.map η).val :=
    @Functor.map_isIso _ _ _ _ _ _ (sheafToPresheaf _ _) (pb.map η) hEta
  let Tz := Presheaf.stalkFunctor C x
  let K := Opens.grothendieckTopology (TopCat.of s)
  let pull := Presheaf.pullback C i
  -- Step 3: pullbackIso naturality
  let pi := Sheaf.pullbackIso C i
  let piF := pi.hom.app F
  let piT := pi.hom.app ((pb ⋙ Sheaf.pushforward C i).obj F)
  haveI hPiF : IsIso piF := by
    dsimp only [piF]
    infer_instance
  haveI hPiT : IsIso piT := by
    dsimp only [piT]
    infer_instance
  haveI hPiFHom : IsIso piF.val :=
    @Functor.map_isIso _ _ _ _ _ _ (sheafToPresheaf _ _) piF hPiF
  haveI hPiTHom : IsIso piT.val :=
    @Functor.map_isIso _ _ _ _ _ _ (sheafToPresheaf _ _) piT hPiT
  have hnat : (pb.map η).val ≫ piT.val = piF.val ≫ sheafifyMap K (pull.map η.val) :=
    congr_arg CategoryTheory.Sheaf.Hom.val (pi.hom.naturality η)
  have hnat_stalk : Tz.map (pb.map η).val ≫ Tz.map piT.val =
      Tz.map piF.val ≫ Tz.map (sheafifyMap K (pull.map η.val)) := by
    rw [← Tz.map_comp, ← Tz.map_comp]
    exact congr_arg Tz.map hnat
  -- Step 4: presheafToSheaf.map(pull.map(η.val)) stalk is iso
  haveI hStalkEtaHom : IsIso (Tz.map (pb.map η).val) :=
    @Functor.map_isIso _ _ _ _ _ _ Tz _ hEtaHom
  haveI hStalkPiFHom : IsIso (Tz.map piF.val) :=
    @Functor.map_isIso _ _ _ _ _ _ Tz _ hPiFHom
  haveI hStalkPiTHom : IsIso (Tz.map piT.val) :=
    @Functor.map_isIso _ _ _ _ _ _ Tz _ hPiTHom
  haveI hSheafifyComp : IsIso (Tz.map piF.val ≫ Tz.map (sheafifyMap K (pull.map η.val))) := by
    rw [← hnat_stalk]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hStalkEtaHom hStalkPiTHom
  haveI hSheafifyMap : IsIso (Tz.map (sheafifyMap K (pull.map η.val))) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ (Tz.map piF.val)
      (Tz.map (sheafifyMap K (pull.map η.val))) hStalkPiFHom hSheafifyComp
  -- Step 5: toSheafify naturality → pull.map(η.val) stalk is iso
  let P₁ := pull.obj F.val
  let P₂ := pull.obj ((pb ⋙ Sheaf.pushforward C i).obj F).val
  have hts : Tz.map (pull.map η.val) ≫ Tz.map (CategoryTheory.toSheafify K P₂) =
      Tz.map (CategoryTheory.toSheafify K P₁) ≫ Tz.map (sheafifyMap K (pull.map η.val)) := by
    rw [← Tz.map_comp, ← Tz.map_comp]
    exact congr_arg Tz.map (CategoryTheory.toSheafify_naturality K (pull.map η.val))
  have hToSheafifyIso (P : (TopCat.of s).Presheaf C) :
      IsIso (Tz.map (toSheafify K P)) :=
    stalkFunctor_map_iso_toSheafify P x
  haveI hToSheafifyP₁ : IsIso (Tz.map (toSheafify K P₁)) :=
    hToSheafifyIso P₁
  haveI hToSheafifyP₂ : IsIso (Tz.map (toSheafify K P₂)) :=
    hToSheafifyIso P₂
  haveI hPullComp :
      IsIso (Tz.map (pull.map η.val) ≫ Tz.map (CategoryTheory.toSheafify K P₂)) := by
    rw [hts]
    infer_instance
  haveI hPullMap : IsIso (Tz.map (pull.map η.val)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ (Tz.map (pull.map η.val))
      (Tz.map (CategoryTheory.toSheafify K P₂)) (hToSheafifyIso P₂) hPullComp
  -- Step 6: stalkPull_nat → η.val stalk is iso
  haveI hStalkPullbackF : IsIso (Presheaf.stalkPullbackHom C i F.val x) :=
    (Presheaf.stalkPullbackIso C i F.val x).isIso_hom
  haveI hStalkPullbackTarget : IsIso (Presheaf.stalkPullbackHom C i
      ((pb ⋙ Sheaf.pushforward C i).obj F).val x) :=
    (Presheaf.stalkPullbackIso C i _ x).isIso_hom
  haveI hStalkPullbackComp :
      IsIso (Presheaf.stalkPullbackHom C i F.val x ≫ Tz.map (pull.map η.val)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ hStalkPullbackF hPullMap
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _
    hStalkPullbackTarget hStalkPullbackComp
    (stalkPullbackHom_naturality i η.val x)

end TopCat

-- The adjunction unit `F → i_*(i^*F)` is epi for closed immersions.
theorem epi_unit_of_closedImmersion
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrp.{u} X) :
    Epi ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrp.{u}
      (TopCat.closedIncl hZ)).unit.app F) := by
  let closedIncl := TopCat.closedIncl hZ
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrp.{u} closedIncl
  letI : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) :=
    balanced_of_strongEpiCategory
  rw [← locallySurjective_iff_epi_addCommGrp (adj.unit.app F),
    TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x
  by_cases hxZ : (x : X) ∈ Z
  · haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrp.{u}
        ((TopCat.closedIncl hZ) ⟨x, hxZ⟩)).map (adj.unit.app F).val) := by
      simpa using
        (TopCat.closedIncl_unit_stalk_isIso (C := AddCommGrp.{u})
          (hs := hZ) F ⟨x, hxZ⟩)
    exact (ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrp.{u} ((TopCat.closedIncl hZ) ⟨x, hxZ⟩)).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrp.{u}
          (TopCat.closedIncl hZ)).unit.app F).val)).2
  · exact fun b ↦ ⟨0, by
      rw [pushforward_closedIncl_stalk_eq_zero
        (hs := hZ)
        (G := ((TopCat.Sheaf.pullback AddCommGrp.{u} closedIncl).obj F).val)
        (((TopCat.Sheaf.pullback AddCommGrp.{u} closedIncl).obj F).cond)
        hxZ b]
      exact map_zero _⟩

/-- The short exact sequence `0 → ker(η) → F → i_*(i^*F) → 0` from a closed immersion,
    where `η` is the pullback-pushforward adjunction unit and `i : Z ↪ X` is the
    inclusion of a closed subset. -/
noncomputable def closedImmersionSES
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrp.{u} X) :
    ShortComplex (TopCat.Sheaf AddCommGrp.{u} X) :=
  let closedIncl := TopCat.closedIncl hZ
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrp.{u} closedIncl).unit.app F
  ShortComplex.mk (kernel.ι η) η (kernel.condition η)

theorem closedImmersionSES_shortExact
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrp.{u} X) :
    (closedImmersionSES (Z := Z) (hZ := hZ) F).ShortExact := by
  unfold closedImmersionSES
  haveI := epi_unit_of_closedImmersion (Z := Z) (hZ := hZ) F
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance
