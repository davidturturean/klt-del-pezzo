import KltDP.Geometry.ProjectiveLineSections
import KltDP.Geometry.SmoothCurveCanonicalDegree
import KltDP.Geometry.TransitionUnitSections
import KltDP.Geometry.ModuleCohomologyExact
import Mathlib.Topology.Sheaves.MayerVietoris
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Towards `H¹(P¹, O) = 0`: the two-chart Mayer–Vietoris reduction in `Ext`

The accepted cohomology `H F n` of an abelian sheaf is the pinned `Ext^n(ℤ, F)` from the constant
sheaf (`AbelianSheafCohomology`, `ModuleCohomology.zariskiFunctor`). The pin provides, for the
Mayer–Vietoris square of two opens (`Opens.mayerVietorisSquare`), the short exact sequence of free
abelian sheaves `0 → ℤ[U ⊓ V] → ℤ[U] ⊞ ℤ[V] → ℤ[U ⊔ V] → 0` (`MayerVietorisSquare.shortComplex_shortExact`)
and the contravariant long exact sequence of `Ext` (`Ext.contravariant_sequence_exact₁'/₃'`).

**Generic reduction (`ext_one_precomp_injective_of_surjective`, `subsingleton_ext_one_of_surjective`):**
for a short exact sequence `S` and coefficients `Y`, if `Ext⁰(S.X₂, Y) → Ext⁰(S.X₁, Y)` is surjective,
the connecting map vanishes and `Ext¹(S.X₃, Y) → Ext¹(S.X₂, Y)` is injective; so
`Ext¹(S.X₂, Y) = 0` gives `Ext¹(S.X₃, Y) = 0`.

**`P¹` (`ext_one_subsingleton_of_cech`):** for the square of the two standard charts and the abelian
sheaf `O` underlying the structure sheaf, `Ext¹(ℤ[U₀ ⊔ U₁], O) = 0` follows from (H1) the surjectivity
of `Ext⁰(ℤ[U₀] ⊞ ℤ[U₁], O) → Ext⁰(ℤ[U₀ ⊓ U₁], O)` and (H2) `Ext¹(ℤ[U₀] ⊞ ℤ[U₁], O) = 0`, both in `Ext`
form. `ℤ[⊤]` is the constant sheaf `ℤ` (`freeTopSheafIsoConstant`), so this is `H¹(P¹, O) = 0` for
the accepted Ext-based cohomology (`hOne_subsingleton_of_cech`) and `genus P¹ = 0`
(`genus_projectiveLine_eq_zero_of_cech`).

**(H1) is proved (`cech_surjective_ext`):** `Hom(ℤ[U], F) ≃ F(U)` (`homFreeSheafEquiv`, natural in `U`
and additive) identifies the degree-zero Mayer–Vietoris map with the Čech difference
`(a, b) ↦ a|_{U₀ ⊓ U₁} − b|_{U₀ ⊓ U₁}` (`homFreeSheafEquiv_mv_desc`), which is surjective by the accepted
`ProjectiveLineSections.restrict_difference_surjective` (`cech_difference_surjective`). Hence
**`hOne_subsingleton_of_affine : Ext¹(ℤ[U₀] ⊞ ℤ[U₁], O) = 0 → H¹(P¹, O) = 0`** and
**`genus_projectiveLine_eq_zero_of_affine`**: `g(P¹) = 0` once `Ext¹(ℤ[U_i], O) = 0` for the two affine
charts (`subsingleton_ext_biprod`).

**Not proved here** (recorded in `F03_RESTRICTION_ADAPTERS.md`, Task 21): (H2), the affine vanishing
`Ext¹(ℤ[U_i], O_{P¹}) = 0` for `U_i ≅ Spec k[t]`; neither `H¹(Spec A, M̃) = 0` nor the identification
`Ext¹(ℤ[U], F) ≅ H¹(U, F|_U)` is in the accepted tree.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian Opposite TopologicalSpace AlgebraicGeometry
open KltDP.Geometry.ProjectiveLineComparison KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.ProjectiveLineSections

universe w' w v u

namespace KltDP.Geometry.ProjectiveLineHOneVanishing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Generic

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w'} C]
variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

include hS in
/-- In the contravariant long exact sequence of `Ext`, surjectivity of
`Ext⁰(S.X₂, Y) → Ext⁰(S.X₁, Y)` forces the connecting map `Ext⁰(S.X₁, Y) → Ext¹(S.X₃, Y)` to vanish,
so `Ext¹(S.X₃, Y) → Ext¹(S.X₂, Y)` is injective. -/
theorem ext_one_precomp_injective_of_surjective
    (hsurj : Function.Surjective ((Ext.mk₀ S.f).precomp Y (zero_add 0))) :
    Function.Injective ((Ext.mk₀ S.g).precomp Y (zero_add 1)) := by
  have h₁ := Ext.contravariant_sequence_exact₁' hS Y 0 1 rfl
  have h₃ := Ext.contravariant_sequence_exact₃' hS Y 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h₁ h₃
  have h₁' : ∀ y : Ext S.X₂ Y 0,
      hS.extClass.precomp Y rfl ((Ext.mk₀ S.f).precomp Y (zero_add 0) y) = 0 :=
    fun y => h₁.apply_apply_eq_zero y
  have h₃' : ∀ z : Ext S.X₃ Y 1, (Ext.mk₀ S.g).precomp Y (zero_add 1) z = 0 →
      ∃ x : Ext S.X₁ Y 0, hS.extClass.precomp Y rfl x = z :=
    fun z hz => (h₃ z).mp hz
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  obtain ⟨x, hx⟩ := h₃' z hz
  obtain ⟨y, hy⟩ := hsurj x
  rw [← hx, ← hy, h₁']

include hS in
/-- Surjectivity in degree zero and vanishing of `Ext¹(S.X₂, Y)` give `Ext¹(S.X₃, Y) = 0`. -/
theorem subsingleton_ext_one_of_surjective
    (hsurj : Function.Surjective ((Ext.mk₀ S.f).precomp Y (zero_add 0)))
    (hmid : Subsingleton (Ext S.X₂ Y 1)) : Subsingleton (Ext S.X₃ Y 1) :=
  ⟨fun _ _ => ext_one_precomp_injective_of_surjective hS Y hsurj (Subsingleton.elim _ _)⟩

end Generic

variable (k : Type u) [Field k]

/-- The Mayer–Vietoris square of the two standard charts of `P¹`. -/
abbrev mvSquare : (Opens.grothendieckTopology (projectiveSpace k 1)).MayerVietorisSquare :=
  Opens.mayerVietorisSquare (chartOpen k 0) (chartOpen k 1)

/-- The abelian sheaf underlying the structure sheaf of `P¹`. -/
abbrev structureAbelianSheaf :
    Sheaf (Opens.grothendieckTopology (projectiveSpace k 1)) AddCommGrp.{u} :=
  (SheafOfModules.toSheaf (projectiveSpace k 1).ringCatSheaf).obj
    (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf)

/-- **The Mayer–Vietoris reduction for `P¹`**: (H1) surjectivity of the degree-zero map
`Ext⁰(ℤ[U₀] ⊞ ℤ[U₁], O) → Ext⁰(ℤ[U₀ ⊓ U₁], O)` and (H2) `Ext¹(ℤ[U₀] ⊞ ℤ[U₁], O) = 0` give
`Ext¹(ℤ[U₀ ⊔ U₁], O) = 0`. -/
theorem ext_one_subsingleton_of_cech
    (hsurj : Function.Surjective
      ((Ext.mk₀ (mvSquare k).shortComplex.f).precomp (structureAbelianSheaf k) (zero_add 0)))
    (hmid : Subsingleton (Ext (mvSquare k).shortComplex.X₂ (structureAbelianSheaf k) 1)) :
    Subsingleton (Ext (mvSquare k).shortComplex.X₃ (structureAbelianSheaf k) 1) :=
  subsingleton_ext_one_of_surjective (mvSquare k).shortComplex_shortExact
    (structureAbelianSheaf k) hsurj hmid

/-- The top object of the square is the whole `P¹`. -/
theorem mvSquare_X₄ : (mvSquare k).X₄ = (⊤ : (projectiveSpace k 1).Opens) := chartOpen_sup k

section Transport

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w'} C]

/-- Vanishing of `Ext` in the first variable transports along isomorphisms. -/
theorem subsingleton_ext_of_iso {A A' Y : C} (e : A ≅ A') (n : ℕ)
    (h : Subsingleton (Ext A Y n)) : Subsingleton (Ext A' Y n) := by
  refine ⟨fun x y => ?_⟩
  have hx : (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add n)) (zero_add n) = x := by
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
  have hy : (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp y (zero_add n)) (zero_add n) = y := by
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
  exact hx.symm.trans ((congrArg (fun z : Ext A Y n => (Ext.mk₀ e.inv).comp z (zero_add n))
    (@Subsingleton.elim _ h ((Ext.mk₀ e.hom).comp x (zero_add n))
      ((Ext.mk₀ e.hom).comp y (zero_add n)))).trans hy)

end Transport

section ConstantSheaf

variable {X : Type u} [TopologicalSpace X]

/-- The free abelian group on the (unique) morphism `V ⟶ ⊤` is `ℤ`. -/
def freeTopComponent (V : (Opens X)ᵒᵖ) :
    AddCommGrp.free.obj ((yoneda.obj (⊤ : Opens X)).obj V) ≅ AddCommGrp.of (ULift.{u} ℤ) :=
  ((FreeAbelianGroup.punitEquiv (V.unop ⟶ (⊤ : Opens X))).trans
    AddEquiv.ulift.symm).toAddCommGrpIso

theorem freeTopComponent_hom_of (V : (Opens X)ᵒᵖ) (h : V.unop ⟶ (⊤ : Opens X)) :
    (freeTopComponent V).hom (FreeAbelianGroup.of h) = ULift.up 1 := by
  show AddEquiv.ulift.symm (FreeAbelianGroup.lift (fun _ => (1 : ℤ)) (FreeAbelianGroup.of h)) =
    ULift.up 1
  rw [FreeAbelianGroup.lift.of]
  rfl

/-- On a space, the free abelian presheaf on the top open is the constant presheaf `ℤ`. -/
def freeTopPresheafIsoConstant :
    yoneda.obj (⊤ : Opens X) ⋙ AddCommGrp.free ≅
      (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrp.of (ULift.{u} ℤ)) :=
  NatIso.ofComponents (fun V => freeTopComponent V) (fun {V W} g => by
    apply AddCommGrp.hom_ext
    apply FreeAbelianGroup.lift.ext
    intro h
    change (freeTopComponent W).hom
        (AddCommGrp.free.map ((yoneda.obj (⊤ : Opens X)).map g) (FreeAbelianGroup.of h)) =
      (freeTopComponent V).hom (FreeAbelianGroup.of h)
    rw [AddCommGrp.free_map_coe, FreeAbelianGroup.map_of, freeTopComponent_hom_of,
      freeTopComponent_hom_of])

/-- **`ℤ[⊤] ≅ ℤ`**: the free abelian sheaf on the top open is the constant sheaf. -/
def freeTopSheafIsoConstant :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrp.{u}).obj
        (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrp.free) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrp.{u}).obj (AddCommGrp.of (ULift.{u} ℤ)) :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrp.{u}).mapIso freeTopPresheafIsoConstant

end ConstantSheaf

/-- The top term of the Mayer–Vietoris sequence of the two charts is the constant sheaf `ℤ`. -/
def mvTopIsoConstant :
    (mvSquare k).shortComplex.X₃ ≅
      (constantSheaf (Opens.grothendieckTopology (projectiveSpace k 1)) AddCommGrp.{u}).obj
        (AddCommGrp.of (ULift.{u} ℤ)) :=
  (presheafToSheaf (Opens.grothendieckTopology (projectiveSpace k 1)) AddCommGrp.{u}).mapIso
    (isoWhiskerRight (yoneda.mapIso (eqToIso (mvSquare_X₄ k))) AddCommGrp.free) ≪≫
    freeTopSheafIsoConstant

/-- **`H¹(P¹, O) = 0` under (H1), (H2)**, for the accepted Ext-based cohomology. -/
theorem hOne_subsingleton_of_cech
    (hsurj : Function.Surjective
      ((Ext.mk₀ (mvSquare k).shortComplex.f).precomp (structureAbelianSheaf k) (zero_add 0)))
    (hmid : Subsingleton (Ext (mvSquare k).shortComplex.X₂ (structureAbelianSheaf k) 1)) :
    Subsingleton (CategoryTheory.Sheaf.H (structureAbelianSheaf k) 1) :=
  subsingleton_ext_of_iso (mvTopIsoConstant k) 1 (ext_one_subsingleton_of_cech k hsurj hmid)

/-- **`g(P¹) = 0` under (H1), (H2).** -/
theorem genus_projectiveLine_eq_zero_of_cech
    (hsurj : Function.Surjective
      ((Ext.mk₀ (mvSquare k).shortComplex.f).precomp (structureAbelianSheaf k) (zero_add 0)))
    (hmid : Subsingleton (Ext (mvSquare k).shortComplex.X₂ (structureAbelianSheaf k) 1)) :
    CurveCanonical.genus (projectiveSpaceToSpec k 1) = 0 := by
  haveI : Subsingleton
      (H (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) 1) :=
    hOne_subsingleton_of_cech k hsurj hmid
  exact cohomologyDimension_eq_zero_of_subsingleton (projectiveSpaceToSpec k 1)
    (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) 1

section DegreeZero

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- The free abelian sheaf on a representable presheaf. -/
abbrev freeSheaf (U : C) : Sheaf J AddCommGrp.{u} :=
  (presheafToSheaf J AddCommGrp.{u}).obj (yoneda.obj U ⋙ AddCommGrp.free)

/-- The morphism of free abelian sheaves induced by a morphism `V ⟶ U`. -/
abbrev freeSheafMap {U V : C} (g : V ⟶ U) : freeSheaf (J := J) V ⟶ freeSheaf (J := J) U :=
  (presheafToSheaf J AddCommGrp.{u}).map (whiskerRight (yoneda.map g) AddCommGrp.free)

/-- **`Hom(ℤ[U], F) ≃ F(U)`**: sheafification, the free–forget adjunction and Yoneda. -/
def homFreeSheafEquiv (U : C) (F : Sheaf J AddCommGrp.{u}) :
    (freeSheaf (J := J) U ⟶ F) ≃ F.val.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrp.{u}).homEquiv _ _).trans
    (((AddCommGrp.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) F.val).trans yonedaEquiv)

theorem homFreeSheafEquiv_apply (U : C) (F : Sheaf J AddCommGrp.{u}) (φ : freeSheaf (J := J) U ⟶ F) :
    homFreeSheafEquiv U F φ =
      ((sheafificationAdjunction J AddCommGrp.{u}).homEquiv _ _ φ).app (op U)
        (FreeAbelianGroup.of (𝟙 U)) := rfl

theorem homFreeSheafEquiv_naturality {U V : C} (g : V ⟶ U) (F : Sheaf J AddCommGrp.{u})
    (φ : freeSheaf (J := J) U ⟶ F) :
    homFreeSheafEquiv V F (freeSheafMap g ≫ φ) = F.val.map g.op (homFreeSheafEquiv U F φ) := by
  simp only [homFreeSheafEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  erw [Adjunction.homEquiv_naturality_left]
  set h := ((Adjunction.whiskerRight Cᵒᵖ AddCommGrp.adj).homEquiv (yoneda.obj U) F.val)
    (((sheafificationAdjunction J AddCommGrp.{u}).homEquiv (yoneda.obj U ⋙ AddCommGrp.free) F) φ)
  change h.app (op V) ((yoneda.map g).app (op V) (𝟙 V)) = (F.val.map g.op) (h.app (op U) (𝟙 U))
  have hn := congr_fun (h.naturality g.op) (𝟙 U)
  change h.app (op V) ((yoneda.obj U).map g.op (𝟙 U)) = (F.val.map g.op) (h.app (op U) (𝟙 U)) at hn
  rw [← hn]
  simp

theorem homFreeSheafEquiv_add (U : C) (F : Sheaf J AddCommGrp.{u}) (φ ψ : freeSheaf (J := J) U ⟶ F) :
    homFreeSheafEquiv U F (φ + ψ) = homFreeSheafEquiv U F φ + homFreeSheafEquiv U F ψ := by
  rw [homFreeSheafEquiv_apply, homFreeSheafEquiv_apply, homFreeSheafEquiv_apply,
    show (sheafificationAdjunction J AddCommGrp.{u}).homEquiv _ _ (φ + ψ) =
      (sheafificationAdjunction J AddCommGrp.{u}).homEquiv _ _ φ +
        (sheafificationAdjunction J AddCommGrp.{u}).homEquiv _ _ ψ from
      ((sheafificationAdjunction J AddCommGrp.{u}).homAddEquiv _ _).map_add φ ψ,
    NatTrans.app_add]
  rfl

/-- `Hom(ℤ[U], F) ≃+ F(U)`. -/
def homFreeSheafAddEquiv (U : C) (F : Sheaf J AddCommGrp.{u}) :
    (freeSheaf (J := J) U ⟶ F) ≃+ F.val.obj (op U) :=
  { homFreeSheafEquiv U F with map_add' := homFreeSheafEquiv_add U F }

theorem homFreeSheafAddEquiv_apply (U : C) (F : Sheaf J AddCommGrp.{u}) (φ : freeSheaf (J := J) U ⟶ F) :
    homFreeSheafAddEquiv U F φ = homFreeSheafEquiv U F φ := rfl

end DegreeZero

section ExtZero

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w'} C]

theorem homEquiv₀_mk₀_comp {X Y Z : C} (f : X ⟶ Y) (x : Ext Y Z 0) :
    Ext.homEquiv₀ ((Ext.mk₀ f).comp x (zero_add 0)) = f ≫ Ext.homEquiv₀ x := by
  obtain ⟨ψ, rfl⟩ := (Ext.mk₀_bijective Y Z).2 x
  rw [Ext.mk₀_comp_mk₀]
  rw [show ∀ (A B : C) (g : A ⟶ B), Ext.homEquiv₀ (Ext.mk₀ g) = g from fun A B g =>
    (Equiv.ofBijective _ (Ext.mk₀_bijective A B)).symm_apply_apply g]
  rw [show ∀ (A B : C) (g : A ⟶ B), Ext.homEquiv₀ (Ext.mk₀ g) = g from fun A B g =>
    (Equiv.ofBijective _ (Ext.mk₀_bijective A B)).symm_apply_apply g]

/-- `Ext` out of a biproduct vanishes when it vanishes on both summands. -/
theorem subsingleton_ext_biprod {A B Y : C} (n : ℕ)
    (hA : Subsingleton (Ext A Y n)) (hB : Subsingleton (Ext B Y n)) :
    Subsingleton (Ext (A ⊞ B) Y n) :=
  ⟨fun _ _ => Ext.biprod_ext (@Subsingleton.elim _ hA _ _) (@Subsingleton.elim _ hB _ _)⟩

end ExtZero

/-! ### The Čech surjectivity of `P¹` in `Ext` form -/

/-- The accepted Čech surjectivity `restrict_difference_surjective`, on the square of the two
charts (the overlap `overlapOpen k` is the meet `chartOpen k 0 ⊓ chartOpen k 1`). -/
theorem cech_difference_surjective :
    Function.Surjective (fun ab : (structureAbelianSheaf k).val.obj (op (mvSquare k).X₂) ×
        (structureAbelianSheaf k).val.obj (op (mvSquare k).X₃) =>
      (structureAbelianSheaf k).val.map (mvSquare k).f₁₂.op ab.1 -
        (structureAbelianSheaf k).val.map (mvSquare k).f₁₃.op ab.2) := by
  change Function.Surjective
    (fun ab : Γ(projectiveSpace k 1, chartOpen k 0) × Γ(projectiveSpace k 1, chartOpen k 1) =>
      TransitionUnitGluing.res (projectiveSpace k 1) inf_le_left ab.1 -
        TransitionUnitGluing.res (projectiveSpace k 1) inf_le_right ab.2)
  intro s
  obtain ⟨⟨a, b⟩, hab⟩ := restrict_difference_surjective k
    (TransitionUnitGluing.res (projectiveSpace k 1) (overlapOpen_eq_inf k).le s)
  refine ⟨(a, b), ?_⟩
  have h := congrArg (TransitionUnitGluing.res (projectiveSpace k 1) (overlapOpen_eq_inf k).ge) hab
  rw [map_sub, TransitionUnitGluing.res_res, TransitionUnitGluing.res_self] at h
  change TransitionUnitGluing.res (projectiveSpace k 1) (overlapOpen_eq_inf k).ge
      (TransitionUnitGluing.res (projectiveSpace k 1) (overlapOpen_le_left k) a) -
    TransitionUnitGluing.res (projectiveSpace k 1) (overlapOpen_eq_inf k).ge
      (TransitionUnitGluing.res (projectiveSpace k 1) (overlapOpen_le_right k) b) = s at h
  rw [TransitionUnitGluing.res_res, TransitionUnitGluing.res_res] at h
  exact h

-- Heartbeats raised as in the accepted `SchemeKaehlerOpenRestrictionComp` (`restrictionCompIso_homEquiv`):
-- the Mayer–Vietoris map is unfolded through the sheafified free abelian sheaves.
set_option maxHeartbeats 1000000 in
/-- The degree-zero Mayer–Vietoris map, read through `Hom(ℤ[U], O) ≃ O(U)`, is the Čech difference. -/
theorem homFreeSheafEquiv_mv_desc
    (a : (structureAbelianSheaf k).val.obj (op (mvSquare k).X₂))
    (b : (structureAbelianSheaf k).val.obj (op (mvSquare k).X₃)) :
    homFreeSheafEquiv (mvSquare k).X₁ (structureAbelianSheaf k)
        ((mvSquare k).shortComplex.f ≫ biprod.desc
          ((homFreeSheafEquiv (mvSquare k).X₂ (structureAbelianSheaf k)).symm a)
          ((homFreeSheafEquiv (mvSquare k).X₃ (structureAbelianSheaf k)).symm b)) =
      (structureAbelianSheaf k).val.map (mvSquare k).f₁₂.op a -
        (structureAbelianSheaf k).val.map (mvSquare k).f₁₃.op b := by
  simp only [GrothendieckTopology.MayerVietorisSquare.shortComplex_f, biprod.lift_desc,
    Preadditive.neg_comp]
  rw [← sub_eq_add_neg, ← homFreeSheafAddEquiv_apply, map_sub, homFreeSheafAddEquiv_apply,
    homFreeSheafAddEquiv_apply, homFreeSheafEquiv_naturality, homFreeSheafEquiv_naturality,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

set_option maxHeartbeats 1000000 in
/-- **(H1) holds**: the degree-zero Mayer–Vietoris map `Ext⁰(ℤ[U₀] ⊞ ℤ[U₁], O) → Ext⁰(ℤ[U₀ ⊓ U₁], O)`
is surjective, by the accepted Čech surjectivity through `Ext⁰(ℤ[U], O) ≃ O(U)`. -/
theorem cech_surjective_ext :
    Function.Surjective
      ((Ext.mk₀ (mvSquare k).shortComplex.f).precomp (structureAbelianSheaf k) (zero_add 0)) := by
  intro z
  obtain ⟨⟨a, b⟩, hab⟩ := cech_difference_surjective k
    (homFreeSheafEquiv (mvSquare k).X₁ (structureAbelianSheaf k) (Ext.homEquiv₀ z))
  refine ⟨Ext.homEquiv₀.symm (biprod.desc
    ((homFreeSheafEquiv (mvSquare k).X₂ (structureAbelianSheaf k)).symm a)
    ((homFreeSheafEquiv (mvSquare k).X₃ (structureAbelianSheaf k)).symm b)), ?_⟩
  apply Ext.homEquiv₀.injective
  apply (homFreeSheafEquiv (mvSquare k).X₁ (structureAbelianSheaf k)).injective
  change homFreeSheafEquiv (mvSquare k).X₁ (structureAbelianSheaf k)
    (Ext.homEquiv₀ ((Ext.mk₀ (mvSquare k).shortComplex.f).comp (Ext.homEquiv₀.symm _) (zero_add 0))) = _
  rw [homEquiv₀_mk₀_comp, Equiv.apply_symm_apply, homFreeSheafEquiv_mv_desc]
  exact hab

/-- **`H¹(P¹, O) = 0` modulo affine vanishing**: the only remaining input is
`Ext¹(ℤ[U₀] ⊞ ℤ[U₁], O) = 0`. -/
theorem hOne_subsingleton_of_affine
    (hmid : Subsingleton (Ext (mvSquare k).shortComplex.X₂ (structureAbelianSheaf k) 1)) :
    Subsingleton (CategoryTheory.Sheaf.H (structureAbelianSheaf k) 1) :=
  hOne_subsingleton_of_cech k (cech_surjective_ext k) hmid

/-- **`g(P¹) = 0` modulo affine vanishing on the two charts**: `Ext¹(ℤ[U_i], O) = 0` for `i = 0, 1`. -/
theorem genus_projectiveLine_eq_zero_of_affine
    (h₀ : Subsingleton (Ext (freeSheaf (J := Opens.grothendieckTopology (projectiveSpace k 1))
      (chartOpen k 0)) (structureAbelianSheaf k) 1))
    (h₁ : Subsingleton (Ext (freeSheaf (J := Opens.grothendieckTopology (projectiveSpace k 1))
      (chartOpen k 1)) (structureAbelianSheaf k) 1)) :
    CurveCanonical.genus (projectiveSpaceToSpec k 1) = 0 :=
  genus_projectiveLine_eq_zero_of_cech k (cech_surjective_ext k)
    (subsingleton_ext_biprod 1 h₀ h₁)

end KltDP.Geometry.ProjectiveLineHOneVanishing
