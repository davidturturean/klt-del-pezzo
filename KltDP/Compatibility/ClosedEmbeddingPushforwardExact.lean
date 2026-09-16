import KltDP.Compatibility.GrothendieckVanishing.ClosedImmersion
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Pushforward of abelian sheaves along a closed embedding is exact and preserves injectives

For any continuous map `f : X ⟶ Y` the sheaf pullback `f⁻¹` preserves finite limits (pinned:
`Opens.map f` is representably flat), hence monomorphisms, so its right adjoint `f_*` preserves
injective sheaves (`pushforward_preservesInjectiveObjects`).

For a closed embedding `f`, `f_*` also preserves epimorphisms: this is the accepted Grothendieck-
vanishing argument for `TopCat.closedIncl` (`epi_pushforward_map_closedIncl_of_locallySurjective`)
repeated for an arbitrary closed embedding — stalks of `f_*G` at `y ∉ f(X)` vanish because `y` has
a neighbourhood disjoint from the closed set `f(X)`, and at `y = f z` the pushforward stalk map is an
isomorphism (`stalkPushforward_iso_of_isInducing`). Together with preservation of kernels (right
adjoint) this gives `Functor.PreservesHomology` (`pushforward_preservesHomology`), the exactness
input for the right-derived comparison of `ExactFunctorRightDerived.lean`.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite Limits

universe u

namespace KltDP.ClosedEmbeddingPushforward

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : TopCat.{u}}

/-- Pushforward of abelian sheaves along any continuous map is additive. -/
instance pushforward_additive (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward AddCommGrp.{u} f).Additive where
  map_add := by
    intro F G a b
    rfl

/-- The sheaf pullback preserves finite limits (pinned: `Opens.map f` is representably flat). -/
instance pullback_preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrp.{u} f) :=
  CategoryTheory.Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullback
    (Opens.map f) AddCommGrp.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The sheaf pullback preserves monomorphisms. -/
instance pullback_preservesMonomorphisms (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback AddCommGrp.{u} f).PreservesMonomorphisms :=
  inferInstance

/-- Pushforward preserves injective sheaves: its left adjoint preserves monomorphisms. -/
instance pushforward_preservesInjectiveObjects (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward AddCommGrp.{u} f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrp.{u} f)

/-- Pushforward preserves all limits (right adjoint). -/
theorem pushforward_preservesLimits (f : X ⟶ Y) :
    PreservesLimitsOfSize.{u, u} (TopCat.Sheaf.pushforward AddCommGrp.{u} f) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrp.{u} f).rightAdjoint_preservesLimits

section ClosedEmbedding

variable (f : X ⟶ Y)

/-- In the pinned concrete category, a zero object has only the zero element. -/
theorem addCommGrp_subsingleton_of_isZero {G : AddCommGrp.{u}} (h : IsZero G) :
    Subsingleton G := by
  refine subsingleton_of_forall_eq (0 : G) fun x => ?_
  simpa using congrArg (fun g : G ⟶ G => g x) (h.eq_of_src (𝟙 G) 0)

/-- The pinned site theorem specialized to the actual opens-site sheaves. -/
theorem locallySurjective_iff_epi_addCommGrp
    {F G : TopCat.Sheaf AddCommGrp.{u} Y} (φ : F ⟶ G) :
    TopCat.Presheaf.IsLocallySurjective φ.val ↔ Epi φ :=
  CategoryTheory.Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrp.{u}) φ

/-- An open set disjoint from the image pulls back to the empty open. -/
theorem map_eq_bot_of_disjoint_range {U : Opens Y}
    (hU : Disjoint (U : Set Y) (Set.range (f : X → Y))) :
    (Opens.map f).obj U = ⊥ := by
  apply Opens.ext
  change (f : X → Y) ⁻¹' (U : Set Y) = ((⊥ : Opens X) : Set X)
  simpa using Set.preimage_eq_empty hU

/-- Stalks of a pushforward along a closed embedding vanish outside the image. -/
theorem pushforward_stalk_eq_zero (hf : Topology.IsClosedEmbedding f)
    {G : TopCat.Presheaf AddCommGrp.{u} X} (hG : G.IsSheaf)
    {y : Y} (hy : y ∉ Set.range (f : X → Y))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrp.{u} y).obj
      ((TopCat.Presheaf.pushforward AddCommGrp.{u} f).obj G)) :
    a = 0 := by
  let Gsh : TopCat.Sheaf AddCommGrp.{u} X := ⟨G, hG⟩
  let F' := (TopCat.Presheaf.pushforward AddCommGrp.{u} f).obj G
  obtain ⟨U, hyU, sU, rfl⟩ := F'.germ_exist y a
  let W : Opens Y := U ⊓ ⟨(Set.range (f : X → Y))ᶜ, hf.isClosed_range.isOpen_compl⟩
  have hW_map : (Opens.map f).obj W = ⊥ :=
    map_eq_bot_of_disjoint_range f
      (Set.disjoint_left.mpr fun z hzW hzR => hzW.2 hzR)
  haveI : Subsingleton (F'.obj (op W)) := addCommGrp_subsingleton_of_isZero (by
    change IsZero (G.obj (op ((Opens.map f).obj W)))
    rw [hW_map]
    exact Gsh.isTerminalOfEmpty.isZero)
  rw [← TopCat.Presheaf.germ_res_apply F'
    (homOfLE (show W ≤ U from inf_le_left)) y ⟨hyU, hy⟩ sU]
  rw [Subsingleton.eq_zero (ConcreteCategory.hom (F'.map (homOfLE (show W ≤ U from
    inf_le_left)).op) sU)]
  exact map_zero _

/-- Pushforward along a closed embedding preserves epis: stalkwise surjectivity (the original
map on the image, zero outside). -/
theorem epi_pushforward_map_of_locallySurjective (hf : Topology.IsClosedEmbedding f)
    {F G : TopCat.Presheaf AddCommGrp.{u} X}
    (hF : F.IsSheaf) (hG : G.IsSheaf)
    (φ : F ⟶ G)
    (hφ_loc : TopCat.Presheaf.IsLocallySurjective φ) :
    Epi ((TopCat.Sheaf.pushforward AddCommGrp.{u} f).map (show
        (⟨F, hF⟩ : TopCat.Sheaf AddCommGrp.{u} X) ⟶
          (⟨G, hG⟩ : TopCat.Sheaf AddCommGrp.{u} X) from
            ⟨φ⟩)) := by
  let fsh : (⟨F, hF⟩ : TopCat.Sheaf AddCommGrp.{u} X) ⟶
      (⟨G, hG⟩ : TopCat.Sheaf AddCommGrp.{u} X) := ⟨φ⟩
  letI : Balanced (Sheaf (Opens.grothendieckTopology Y) AddCommGrp.{u}) :=
    balanced_of_strongEpiCategory
  change Epi ((TopCat.Sheaf.pushforward AddCommGrp.{u} f).map fsh)
  rw [← locallySurjective_iff_epi_addCommGrp
    ((TopCat.Sheaf.pushforward AddCommGrp.{u} f).map fsh)]
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro y; by_cases hy : y ∈ Set.range (f : X → Y)
  · obtain ⟨z, rfl⟩ := hy
    haveI hEpiF : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrp.{u} z).map φ) :=
      (AddCommGrp.epi_iff_surjective _).mpr
        (((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
            (T := φ)).mp hφ_loc) z)
    have hnat : (TopCat.Presheaf.stalkFunctor AddCommGrp.{u} (f z)).map
        ((TopCat.Presheaf.pushforward AddCommGrp.{u} f).map φ) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrp.{u} f G z =
    TopCat.Presheaf.stalkPushforward AddCommGrp.{u} f F z ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrp.{u} z).map φ := by
      apply TopCat.Presheaf.stalk_hom_ext; intro U hU
      erw [← Category.assoc]
      rw [TopCat.Presheaf.stalkFunctor_map_germ U (f z) hU
        ((TopCat.Presheaf.pushforward AddCommGrp.{u} f).map φ)]
      erw [Category.assoc]
      erw [TopCat.Presheaf.stalkPushforward_germ]
      erw [TopCat.Presheaf.stalkPushforward_germ_assoc]
      erw [TopCat.Presheaf.stalkFunctor_map_germ]
      rfl
    apply (AddCommGrp.epi_iff_surjective _).mp
    change Epi ((TopCat.Presheaf.stalkFunctor AddCommGrp.{u} (f z)).map
        ((TopCat.Presheaf.pushforward AddCommGrp.{u} f).map φ))
    haveI : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrp.{u} f F z) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrp.{u} hf.isInducing F z
    haveI : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrp.{u} f G z) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrp.{u} hf.isInducing G z
    have hcomp : Epi (TopCat.Presheaf.stalkPushforward AddCommGrp.{u} f F z ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrp.{u} z).map φ) :=
      @epi_comp _ _ _ _ _
        (TopCat.Presheaf.stalkPushforward AddCommGrp.{u} f F z)
        (inferInstance : Epi (TopCat.Presheaf.stalkPushforward AddCommGrp.{u} f F z))
        ((TopCat.Presheaf.stalkFunctor AddCommGrp.{u} z).map φ)
        hEpiF
    have hcomp' : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrp.{u} (f z)).map
        ((TopCat.Presheaf.pushforward AddCommGrp.{u} f).map φ) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrp.{u} f G z) := by
      rw [hnat]; exact hcomp
    letI := hcomp'
    have hcancel := epi_comp
      ((TopCat.Presheaf.stalkFunctor AddCommGrp.{u} (f z)).map
        ((TopCat.Presheaf.pushforward AddCommGrp.{u} f).map φ) ≫
        TopCat.Presheaf.stalkPushforward AddCommGrp.{u} f G z)
      (inv (TopCat.Presheaf.stalkPushforward AddCommGrp.{u} f G z))
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using hcancel
  · intro b
    rw [pushforward_stalk_eq_zero f hf (G := G) hG hy b]
    exact ⟨0, AddMonoidHom.map_zero _⟩

/-- Pushforward along a closed embedding preserves epimorphisms of abelian sheaves. -/
theorem pushforward_preservesEpimorphisms (hf : Topology.IsClosedEmbedding f) :
    (TopCat.Sheaf.pushforward AddCommGrp.{u} f).PreservesEpimorphisms where
  preserves {F G} φ hφ := by
    letI : Epi φ := hφ
    letI : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) :=
      balanced_of_strongEpiCategory
    have hφ_loc : TopCat.Presheaf.IsLocallySurjective φ.val :=
      (locallySurjective_iff_epi_addCommGrp φ).mpr inferInstance
    change Epi ((TopCat.Sheaf.pushforward AddCommGrp.{u} f).map (⟨φ.val⟩))
    exact epi_pushforward_map_of_locallySurjective f hf
      (F := F.val) (G := G.val) F.cond G.cond φ.val hφ_loc

/-- **Pushforward along a closed embedding is exact** (preserves homology). -/
theorem pushforward_preservesHomology (hf : Topology.IsClosedEmbedding f) :
    (TopCat.Sheaf.pushforward AddCommGrp.{u} f).PreservesHomology := by
  haveI := pushforward_preservesEpimorphisms f hf
  haveI := pushforward_preservesLimits f
  haveI : PreservesFiniteLimits (TopCat.Sheaf.pushforward AddCommGrp.{u} f) :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

end ClosedEmbedding

end KltDP.ClosedEmbeddingPushforward
