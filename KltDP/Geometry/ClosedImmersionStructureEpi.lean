import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import KltDP.Geometry.SchemeConormal
import KltDP.Geometry.EffectiveCartierDegree

/-!
# The structure map `O_X → i_*O_Z` of a closed immersion is an epimorphism

For a closed immersion `i : Z → X`, the induced map on sections over an affine open `V` is
surjective (Mathlib: a closed immersion into an affine scheme is surjective on global sections,
transported through `Γ_map_morphismRestrict`). Since affine opens form a basis and module sheaves
are separated, this makes `structureToPushforwardUnit i : O_X ⟶ i_*O_Z` an epimorphism of sheaves of
modules. Applied to the closed immersion of the zero scheme of an effective Cartier divisor, this is
the input `hepi` of `lineDegree_neg_cartier_of_sequence`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section AffineSurjective

/-- Restriction along an equality of opens is injective. -/
theorem presheaf_map_eqToHom_injective (Z : Scheme.{u}) {U V : Z.Opens} (h : U = V) :
    Function.Injective (Z.presheaf.map (eqToHom h).op) := by
  subst h
  intro a b hab
  simpa using hab

variable {Y X : Scheme.{u}} (i : Y ⟶ X)

/-- A closed immersion is surjective on sections over every affine open. -/
theorem app_surjective_of_isAffineOpen [IsClosedImmersion i] (V : X.Opens)
    (hV : IsAffineOpen V) : Function.Surjective (i.app V) := by
  haveI : IsClosedImmersion (i ∣_ V) :=
    IsLocalAtTarget.restrict (P := @IsClosedImmersion) (f := i) inferInstance V
  haveI : IsAffine V.toScheme := hV
  obtain ⟨-, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (f := i ∣_ V)
  have hΓ := Γ_map_morphismRestrict i V
  rw [Scheme.Γ_map_op] at hΓ
  intro y
  obtain ⟨x, hx⟩ := hsurj (Y.presheaf.map (eqToHom (i ⁻¹ᵁ V).isOpenEmbedding_obj_top).op y)
  refine ⟨X.presheaf.map (eqToHom V.isOpenEmbedding_obj_top.symm).op x, ?_⟩
  apply presheaf_map_eqToHom_injective Y (i ⁻¹ᵁ V).isOpenEmbedding_obj_top
  rw [hΓ, CommRingCat.comp_apply, CommRingCat.comp_apply] at hx
  exact hx

end AffineSurjective

section Epi

variable {Y X : Scheme.{u}} (i : Y ⟶ X)

/-- Composite of module-sheaf morphisms on a section. -/
theorem moduleHom_comp_val_app {A B E : X.Modules} (a : A ⟶ B) (b : B ⟶ E) (V : X.Opensᵒᵖ)
    (x : A.val.obj V) : (a ≫ b).val.app V x = b.val.app V (a.val.app V x) := rfl

/-- **The structure map of a closed immersion is an epimorphism of module sheaves.** -/
theorem structureToPushforwardUnit_epi_of_isClosedImmersion [IsClosedImmersion i] :
    Epi (structureToPushforwardUnit i) := by
  constructor
  intro M g h hgh
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  have hcov : ∀ x : U.unop, ∃ V : X.Opens, IsAffineOpen V ∧ (x : X) ∈ V ∧ V ≤ U.unop :=
    fun x => (Opens.isBasis_iff_nbhd.mp (isBasis_affine_open X)) x.2
  choose W hW using hcov
  have hle : ∀ x : U.unop, W x ≤ U.unop := fun x => (hW x).2.2
  have hcover : U.unop ≤ iSup W := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, (hW ⟨x, hx⟩).2.1⟩
  refine TopCat.Sheaf.eq_of_locally_eq' ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) W
    U.unop (fun x => homOfLE (hle x)) hcover (g.val.app U t) (h.val.app U t) ?_
  intro x
  obtain ⟨s, hs⟩ := app_surjective_of_isAffineOpen i (W x) (hW x).1
    (((schemeModulePushforward i).obj (_root_.SheafOfModules.unit Y.ringCatSheaf)).val.map
      (homOfLE (hle x)).op t)
  have h1 := PresheafOfModules.naturality_apply g.val (homOfLE (hle x)).op t
  have h2 := PresheafOfModules.naturality_apply h.val (homOfLE (hle x)).op t
  have h3 := congrArg (fun q : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ M =>
    q.val.app (op (W x)) s) hgh
  have h4 : (structureToPushforwardUnit i).val.app (op (W x)) s = i.app (W x) s :=
    structureToPushforwardUnit_app i (W x) s
  have hg : g.val.app (op (W x))
      (((schemeModulePushforward i).obj (_root_.SheafOfModules.unit Y.ringCatSheaf)).val.map
        (homOfLE (hle x)).op t) =
      (structureToPushforwardUnit i ≫ g).val.app (op (W x)) s :=
    (congrArg (fun y => g.val.app (op (W x)) y) hs.symm).trans
      ((congrArg (fun y => g.val.app (op (W x)) y) h4.symm).trans
        (moduleHom_comp_val_app (structureToPushforwardUnit i) g (op (W x)) s).symm)
  have hh : h.val.app (op (W x))
      (((schemeModulePushforward i).obj (_root_.SheafOfModules.unit Y.ringCatSheaf)).val.map
        (homOfLE (hle x)).op t) =
      (structureToPushforwardUnit i ≫ h).val.app (op (W x)) s :=
    (congrArg (fun y => h.val.app (op (W x)) y) hs.symm).trans
      ((congrArg (fun y => h.val.app (op (W x)) y) h4.symm).trans
        (moduleHom_comp_val_app (structureToPushforwardUnit i) h (op (W x)) s).symm)
  exact h1.symm.trans (hg.trans (h3.trans (hh.symm.trans h2)))

end Epi

section Cartier

variable (X : Scheme.{u}) [IsIntegral X] (E : CartierDivisor X)
  (hE : HasRegularCartierEquations X E)

/-- **`O_X → i_*O_E` is an epimorphism** for the closed immersion of the zero scheme of an
effective Cartier divisor (the input `hepi` of the 0AYY computation). -/
theorem effectiveCartier_structureToPushforwardUnit_epi :
    Epi (structureToPushforwardUnit (effectiveCartierInclusion X E hE)) :=
  structureToPushforwardUnit_epi_of_isClosedImmersion (effectiveCartierInclusion X E hE)

end Cartier

end KltDP.Geometry
