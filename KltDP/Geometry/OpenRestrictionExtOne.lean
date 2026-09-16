import KltDP.Geometry.ProjectiveLineGenusZero
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# The open-`Ext` comparison in degree one; `g(P¹) = 0` from the affine-vanishing literal alone

For an open immersion `f : Y ⟶ X` of schemes, restriction of abelian sheaves `res f` is precomposition with the
image functor `f.opensFunctor` (the underlying abelian sheaf of the accepted module restriction
`SchemeModuleRestriction.restriction f`).

* `opensFunctor_isCocontinuous`: the image functor of an open immersion is cocontinuous, so `res f` is a left
  adjoint (pinned `sheafAdjunctionCocontinuous`) and preserves finite colimits; it is a right adjoint (pinned
  `sheafPullbackConstruction`) and preserves finite limits; hence it preserves short exact sequences.
* `sections_surjective_of_subsingleton_H_one`: for a short exact `0 → A → B → C → 0` of abelian sheaves on `Y` with
  `H¹(Y, A) = 0`, `B(Y) → C(Y)` is surjective (covariant `Ext` sequence, accepted `H.equiv₀` and its naturality).
* `homFreeSheafEquiv_comp`: `Hom(ℤ[U], F) ≃ F(U)` is natural in `F`.
* **`subsingleton_ext_one_of_restriction`**: `H¹(Y, G|_Y) = 0 → Ext¹_X(ℤ[f(Y)], G) = 0`, by the injective
  presentation `0 → G → I → I/G → 0` on `X`: its restriction is short exact, so `I(f(Y)) → (I/G)(f(Y))` is
  surjective, and `Ext¹(ℤ[f(Y)], I) = 0` makes every class in `Ext¹(ℤ[f(Y)], G)` a connecting image of a class
  that lifts to `I`, hence zero. `subsingleton_ext_one_of_module_restriction` is the same for scheme modules.
* **`genus_projectiveLine_eq_zero_of_affineVanishing (hV) : g(P¹) = 0`**, using only the literal
  `AffineVanishingLiteral` (Stacks 01XB, not admitted).

This is the degree-one vanishing transfer, not the isomorphism `Ext^p_X(ℤ[U], F) ≅ H^p(U, F|_U)` of
`ProjectiveLineGenusZero.OpenExtComparison`, which stays open for general `p`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian Opposite TopologicalSpace AlgebraicGeometry
open KltDP.Geometry.ProjectiveLineComparison KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.ProjectiveLineSections KltDP.Geometry.ProjectiveLineHOneVanishing
open KltDP.Literature.Stacks

universe u

namespace KltDP.Geometry.OpenRestrictionExtOne

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section FreeSheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- `Hom(ℤ[U], F) ≃ F(U)` is natural in the sheaf `F`. -/
theorem homFreeSheafEquiv_comp (U : C) {F G : Sheaf J AddCommGrp.{u}}
    (φ : freeSheaf (J := J) U ⟶ F) (g : F ⟶ G) :
    homFreeSheafEquiv U G (φ ≫ g) = g.val.app (op U) (homFreeSheafEquiv U F φ) := by
  rw [homFreeSheafEquiv_apply, homFreeSheafEquiv_apply, Adjunction.homEquiv_naturality_right]
  rfl

end FreeSheaf

section SectionsSurjective

variable {Y : Scheme.{u}}

/-- For a short exact sequence `0 → A → B → C → 0` of abelian sheaves with `H¹(A) = 0`, global sections of
`B → C` are surjective. -/
theorem sections_surjective_of_subsingleton_H_one
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrp.{u})}
    (hS : S.ShortExact) (h : Subsingleton (Sheaf.H S.X₁ 1)) :
    Function.Surjective (S.g.val.app (op ⊤)) := by
  intro s
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hS
    ((Sheaf.H.equiv₀ S.X₃ Limits.isTerminalTop).symm s) (zero_add 1) (@Subsingleton.elim _ h _ _)
  refine ⟨Sheaf.H.equiv₀ S.X₂ Limits.isTerminalTop z, ?_⟩
  rw [Sheaf.H.equiv₀_naturality Limits.isTerminalTop S.g z, Sheaf.H.map_apply, hz,
    AddEquiv.apply_symm_apply]

end SectionsSurjective

section Restriction

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- The image functor of an open immersion is continuous (as in the accepted `ModuleOpenRestriction`). -/
local instance opensFunctor_isContinuous : f.opensFunctor.IsContinuous
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
  f.isOpenEmbedding.functor_isContinuous

/-- The image functor of an open immersion is cocontinuous: a covering sieve of `f(U)` pulls back to a
covering sieve of `U`. -/
theorem opensFunctor_isCocontinuous : f.opensFunctor.IsCocontinuous
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) where
  cover_lift {U} {S} hS := by
    intro y hy
    obtain ⟨V, g, hg, hyV⟩ := hS (f.base y) (Set.mem_image_of_mem (⇑f.base) hy)
    have hle : f ''ᵁ (U ⊓ f ⁻¹ᵁ V) ≤ V := by
      rintro _ ⟨z, ⟨_, hz⟩, rfl⟩
      exact hz
    refine ⟨U ⊓ f ⁻¹ᵁ V, homOfLE inf_le_left, ?_, Opens.mem_inf.2 ⟨hy, hyV⟩⟩
    show S.arrows (f.opensFunctor.map (homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ V ≤ U)))
    rw [Subsingleton.elim (f.opensFunctor.map (homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ V ≤ U)))
      (homOfLE hle ≫ g)]
    exact S.downward_closed hg (homOfLE hle)

local instance opensFunctor_isCocontinuous' : f.opensFunctor.IsCocontinuous
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
  opensFunctor_isCocontinuous f

/-- Restriction of abelian sheaves along the open immersion `f`. -/
abbrev res : Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u} ⥤
    Sheaf (Opens.grothendieckTopology Y) AddCommGrp.{u} :=
  f.opensFunctor.sheafPushforwardContinuous AddCommGrp.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

local instance res_additive : (res f).Additive where
  map_add := by
    intro F G a b
    rfl

theorem res_preservesFiniteColimits : PreservesFiniteColimits (res f) := by
  have : PreservesColimitsOfSize.{0, 0} (res f) :=
    (f.opensFunctor.sheafAdjunctionCocontinuous AddCommGrp.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

theorem res_preservesFiniteLimits : PreservesFiniteLimits (res f) := by
  have : PreservesLimitsOfSize.{0, 0} (res f) :=
    (Adjunction.ofIsRightAdjoint (res f)).rightAdjoint_preservesLimits
  exact PreservesLimitsOfSize.preservesFiniteLimits _

/-- The injective presentation `0 → G → I(G) → I(G)/G → 0`. -/
abbrev injectiveSES (G : Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) :=
  ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G)) (cokernel.condition _)

theorem injectiveSES_shortExact (G : Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) :
    (injectiveSES G).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

/-- **Degree-one open comparison (vanishing form)**: `H¹(Y, G|_Y) = 0` implies `Ext¹_X(ℤ[f(Y)], G) = 0`. -/
theorem subsingleton_ext_one_of_restriction (G : Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u})
    (h : Subsingleton (Sheaf.H ((res f).obj G) 1)) :
    Subsingleton (Ext (freeSheaf (J := Opens.grothendieckTopology X) (f ''ᵁ ⊤)) G 1) := by
  have hS := injectiveSES_shortExact G
  haveI := res_preservesFiniteLimits f
  haveI := res_preservesFiniteColimits f
  have hS' : ((injectiveSES G).map (res f)).ShortExact := hS.map_of_exact (res f)
  have hsurj : Function.Surjective ((injectiveSES G).g.val.app (op (f ''ᵁ ⊤))) :=
    sections_surjective_of_subsingleton_H_one hS' h
  have hzero : ∀ e : Ext (freeSheaf (J := Opens.grothendieckTopology X) (f ''ᵁ ⊤)) G 1, e = 0 := by
    intro e
    haveI : Injective (injectiveSES G).X₂ := Injective.injective_under G
    obtain ⟨x₃, hx₃⟩ :=
      Ext.covariant_sequence_exact₁ _ hS e (Ext.eq_zero_of_injective _) (zero_add 1)
    obtain ⟨t, ht⟩ := hsurj (homFreeSheafEquiv (f ''ᵁ ⊤) (injectiveSES G).X₃ (Ext.homEquiv₀ x₃))
    have hx₂ : (Ext.mk₀ ((homFreeSheafEquiv (f ''ᵁ ⊤) (injectiveSES G).X₂).symm t)).comp
        (Ext.mk₀ (injectiveSES G).g) (add_zero 0) = x₃ := by
      rw [Ext.mk₀_comp_mk₀]
      refine Eq.trans ?_ (Ext.mk₀_homEquiv₀_apply x₃)
      congr 1
      apply (homFreeSheafEquiv (f ''ᵁ ⊤) (injectiveSES G).X₃).injective
      rw [homFreeSheafEquiv_comp, Equiv.apply_symm_apply]
      exact ht
    rw [← hx₃, ← hx₂, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

/-- The same for scheme modules, with the accepted module restriction and the accepted cohomology `H`. -/
theorem subsingleton_ext_one_of_module_restriction (M : X.Modules)
    (h : Subsingleton (H ((SchemeModuleRestriction.restriction f).obj M) 1)) :
    Subsingleton (Ext (freeSheaf (J := Opens.grothendieckTopology X) (f ''ᵁ ⊤))
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) 1) :=
  subsingleton_ext_one_of_restriction f _ h

end Restriction

/-- For an open `U` of a scheme: `H¹(U, M|_U) = 0` implies `Ext¹_X(ℤ[U], M) = 0`. -/
theorem subsingleton_ext_one_of_open {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (h : Subsingleton (H ((SchemeModuleRestriction.restriction U.ι).obj M) 1)) :
    Subsingleton (Ext (freeSheaf (J := Opens.grothendieckTopology X) U)
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) 1) := by
  have h' := subsingleton_ext_one_of_module_restriction U.ι M h
  rw [Scheme.Opens.ι_image_top] at h'
  exact h'

/-- `Ext¹(ℤ[U_i], O_{P¹}) = 0` on the two standard charts, from the affine-vanishing literal alone. -/
theorem chart_ext_one_subsingleton (hV : AffineVanishingLiteral.{u}) (k : Type u) [Field k] (i : Fin 2) :
    Subsingleton (Ext (freeSheaf (J := Opens.grothendieckTopology (projectiveSpace k 1)) (chartOpen k i))
      (structureAbelianSheaf k) 1) := by
  haveI := ProjectiveLineGenusZero.unit_isQuasicoherent (projectiveSpace k 1)
  exact subsingleton_ext_one_of_open (chartOpen k i)
    (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf)
    (ProjectiveLineGenusZero.affineVanishing_restriction hV
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) (chartOpen k i)
      (chartOpen_isAffineOpen k i) 1 one_pos)

/-- **`g(P¹) = 0` from the affine-vanishing literal (Stacks 01XB) alone.** -/
theorem genus_projectiveLine_eq_zero_of_affineVanishing (k : Type u) [Field k]
    (hV : AffineVanishingLiteral.{u}) :
    CurveCanonical.genus (projectiveSpaceToSpec k 1) = 0 :=
  genus_projectiveLine_eq_zero_of_affine k (chart_ext_one_subsingleton hV k 0)
    (chart_ext_one_subsingleton hV k 1)

end KltDP.Geometry.OpenRestrictionExtOne
