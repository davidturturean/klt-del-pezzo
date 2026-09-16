/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Chris Birkbeck

Adapted from CBirkbeck/AINTLIB 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684,
projects/ModularCurves/ModularCurves/Picard/PicComparison.lean, lines 648–828.
The actual pairing maps and section computation are retained. The final
local tensor inverse is transported directly to the over-site by the
proved sheaf tensor restriction isomorphism, avoiding scheme pullback
and the separate over-site/scheme equivalence.
-/
import KltDP.Geometry.SheafTensorUnitPair
import KltDP.Geometry.InvertibleSheafPicard
import KltDP.Compatibility.SheafRestrictionTensor
import KltDP.CategoryTheory.TensorInvertibleSplit

/-!
# Tensor-invertible sheaves are locally free of rank one

The local unit pair gives maps from and to the actual unit sheaf on the
over-site, with one composite equal to its identity. Restriction of the
actual tensor inverse and categorical cancellation prove the other
composite. The resulting actual trivializations define the existing
local singleton-basis predicate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.SchemeTensorPairing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}}

open KltDP.SheafOfModules in
/-- **[CMP-L3a]** Pairing against a fixed section `n` of `N`, as a morphism on the
over-site: componentwise `s ↦ ⟨s ⊗ n|_V⟩` for the pairing of `ε`. -/
noncomputable def pairingHom {M N : X.Modules} (ε : tensorSheafification M N ≅ unitSheaf X)
    {W : X.Opens} (n : N.val.obj (Opposite.op W)) :
    M.over W ⟶ SheafOfModules.unit (X.ringCatSheaf.over W) := by
  let component (Vf : (Over W)ᵒᵖ) :
      (M.over W).val.obj Vf ⟶
        (SheafOfModules.unit (X.ringCatSheaf.over W)).val.obj Vf := by
    letI : Module ↑((X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj
        (Opposite.op (Opposite.unop Vf).left))
        ↑(M.val.obj (Opposite.op (Opposite.unop Vf).left)) :=
      inferInstanceAs (Module ↑(X.ringCatSheaf.val.obj
        (Opposite.op (Opposite.unop Vf).left))
        ↑(M.val.obj (Opposite.op (Opposite.unop Vf).left)))
    letI : Module ↑((X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj
        (Opposite.op (Opposite.unop Vf).left))
        ↑(N.val.obj (Opposite.op (Opposite.unop Vf).left)) :=
      inferInstanceAs (Module ↑(X.ringCatSheaf.val.obj
        (Opposite.op (Opposite.unop Vf).left))
        ↑(N.val.obj (Opposite.op (Opposite.unop Vf).left)))
    exact ModuleCat.ofHom
      ((ε.hom.val.app (Opposite.op (Opposite.unop Vf).left)).hom.comp
        (((tensorToSheafify M N).app (Opposite.op (Opposite.unop Vf).left)).hom.comp
          ((TensorProduct.mk
            ((X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj
              (Opposite.op (Opposite.unop Vf).left))
            (M.val.obj (Opposite.op (Opposite.unop Vf).left))
            (N.val.obj (Opposite.op (Opposite.unop Vf).left))).flip
              (N.val.map (Opposite.unop Vf).hom.op n))))
  refine ⟨{ app := component, naturality := fun {Vf Vf'} i => ?_ }⟩
  refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  have hw : i.unop.left ≫ (Opposite.unop Vf).hom = (Opposite.unop Vf').hom :=
    Over.w i.unop
  have h₁ : N.val.map ((Opposite.unop Vf').hom).op n =
      N.val.map (i.unop.left).op (N.val.map ((Opposite.unop Vf).hom).op n) := by
    show N.val.presheaf.map ((Opposite.unop Vf').hom).op n =
      N.val.presheaf.map (i.unop.left).op
        (N.val.presheaf.map ((Opposite.unop Vf).hom).op n)
    rw [← hw, op_comp, Functor.map_comp]
    rfl
  simp only [ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply]
  have hM : (M.over W).val.map i s = M.val.map (i.unop.left).op s := rfl
  have hO : (SheafOfModules.unit (X.ringCatSheaf.over W)).val.map i (component Vf s) =
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).map (i.unop.left).op
        (component Vf s) := rfl
  rw [hM, hO]
  change pairingElem ε (Opposite.unop Vf').left
      ((M.val.map (i.unop.left).op s) ⊗ₜ N.val.map ((Opposite.unop Vf').hom).op n) =
    (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).map (i.unop.left).op
      (pairingElem ε (Opposite.unop Vf).left
        (s ⊗ₜ N.val.map ((Opposite.unop Vf).hom).op n))
  refine (congrArg (fun t => pairingElem ε (Opposite.unop Vf').left
      ((M.val.map (i.unop.left).op s) ⊗ₜ t)) h₁).trans ?_
  refine (congrArg (pairingElem ε (Opposite.unop Vf').left)
      (PresheafOfModules.Monoidal.tensorObj_map_tmul (i.unop.left).op s
        (N.val.map ((Opposite.unop Vf).hom).op n)).symm).trans ?_
  exact pairingElem_map ε (i.unop.left).op _

open KltDP.SheafOfModules in
/-- **[CMP-L3b]** When the pairing value of `(m, n)` is `1`, multiplication by `m`
splits the pairing against `n`: the composite on the over-site is the identity of the
unit. -/
theorem unitHomEquiv_symm_overSection_comp_pairingHom {M N : X.Modules}
    (ε : tensorSheafification M N ≅ unitSheaf X) {W : X.Opens} (m : M.val.obj (Opposite.op W))
    (n : N.val.obj (Opposite.op W)) (h1 : pairingElem ε W (m ⊗ₜ n) = 1) :
    (M.over W).unitHomEquiv.symm (overSection X.ringCatSheaf M W m) ≫ pairingHom ε n =
      𝟙 (SheafOfModules.unit (X.ringCatSheaf.over W)) := by
  refine (SheafOfModules.unitHomEquiv_symm_comp (overSection X.ringCatSheaf M W m)
    (pairingHom ε n)).trans ?_
  refine Eq.trans
    (congrArg (SheafOfModules.unit (X.ringCatSheaf.over W)).unitHomEquiv.symm ?_)
    (Equiv.symm_apply_apply _ (𝟙 _))
  refine PresheafOfModules.sections_ext _ _ (fun V => ?_)
  rw [show (SheafOfModules.sectionsMap (pairingHom ε n)
      (overSection X.ringCatSheaf M W m)).val V =
      (pairingHom ε n).val.app V ((overSection X.ringCatSheaf M W m).val V) from rfl,
    SheafOfModules.unitHomEquiv_apply_coe]
  change (pairingHom ε n).val.app V (M.val.map (Opposite.unop V).hom.op m) = _
  change pairingElem ε (Opposite.unop V).left
      ((M.val.map (Opposite.unop V).hom.op m) ⊗ₜ
        N.val.map (Opposite.unop V).hom.op n) = _
  exact (congrArg (pairingElem ε (Opposite.unop V).left)
      (PresheafOfModules.Monoidal.tensorObj_map_tmul
        ((Opposite.unop V).hom).op m n).symm).trans
    ((pairingElem_map ε ((Opposite.unop V).hom).op (m ⊗ₜ n)).trans
      ((congrArg ((X.sheaf.val ⋙ forget₂ CommRingCat RingCat).map
          ((Opposite.unop V).hom).op) h1).trans
        (map_one (ConcreteCategory.hom ((X.sheaf.val ⋙ forget₂ CommRingCat
          RingCat).map ((Opposite.unop V).hom).op)))))


/-- A section pair whose pairing is one gives an actual rank-one
trivialization on its over-site. Both inverse identities are proved. -/
theorem nonempty_over_iso_unit_of_pairing {M N : X.Modules}
    (ε : tensorSheafification M N ≅ unitSheaf X) {W : X.Opens}
    (m : M.val.obj (Opposite.op W)) (n : N.val.obj (Opposite.op W))
    (h1 : pairingElem ε W (m ⊗ₜ n) = 1) :
    Nonempty (M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) := by
  let S := X.sheaf.val
  let hS := X.ringCatSheaf.cond
  let SW := (Over.forget W).op ⋙ S
  let hSW := KltDP.SheafOfModules.overRingSheafCondition S hS W
  letI : MonoidalCategory X.Modules :=
    PresheafOfModules.sheafOfModulesMonoidalCategory S hS
  letI : MonoidalCategory (SheafOfModules (X.ringCatSheaf.over W)) :=
    PresheafOfModules.sheafOfModulesMonoidalCategory SW hSW
  letI : SymmetricCategory (SheafOfModules (X.ringCatSheaf.over W)) :=
    PresheafOfModules.sheafOfModulesSymmetricCategory SW hSW
  let α : SheafOfModules.unit (X.ringCatSheaf.over W) ⟶ M.over W :=
    (M.over W).unitHomEquiv.symm
      (KltDP.SheafOfModules.overSection X.ringCatSheaf M W m)
  let β : M.over W ⟶ SheafOfModules.unit (X.ringCatSheaf.over W) := pairingHom ε n
  have hαβ : α ≫ β = 𝟙 (SheafOfModules.unit (X.ringCatSheaf.over W)) :=
    unitHomEquiv_symm_overSection_comp_pairingHom ε m n h1
  let eBase : M ⊗ N ≅ 𝟙_ X.Modules :=
    PresheafOfModules.sheafTensorIsoSheafification S hS M N ≪≫ ε ≪≫
      (PresheafOfModules.sheafTensorUnitIso S hS).symm
  let e : M.over W ⊗ N.over W ≅
      𝟙_ (SheafOfModules (X.ringCatSheaf.over W)) :=
    (KltDP.SheafOfModules.overTensorIso S hS W M N).symm ≪≫
      (SheafOfModules.overFunctor X.ringCatSheaf W).mapIso eBase ≪≫
        KltDP.SheafOfModules.overTensorUnitIso S hS W
  let e' : N.over W ⊗ M.over W ≅
      𝟙_ (SheafOfModules (X.ringCatSheaf.over W)) :=
    (β_ (N.over W) (M.over W)) ≪≫ e
  let eU : 𝟙_ (SheafOfModules (X.ringCatSheaf.over W)) ≅
      SheafOfModules.unit (X.ringCatSheaf.over W) :=
    PresheafOfModules.sheafTensorUnitIso SW hSW
  have hab : (eU.hom ≫ α) ≫ (β ≫ eU.inv) =
      𝟙 (𝟙_ (SheafOfModules (X.ringCatSheaf.over W))) := by
    simp only [Category.assoc]
    rw [← Category.assoc α β, hαβ, Category.id_comp, Iso.hom_inv_id]
  have hba := CategoryTheory.MonoidalCategory.whiskerRight_comp_eq_id_of_split
    e e' (eU.hom ≫ α) (β ≫ eU.inv) hab
  have hβα : β ≫ α = 𝟙 (M.over W) := by
    have hcomp : (β ≫ eU.inv) ≫ (eU.hom ≫ α) = β ≫ α := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact hcomp.symm.trans hba
  exact ⟨⟨β, α, hβα, hαβ⟩⟩

/-- An actual tensor inverse supplies a covering by actual rank-one
trivializations, hence the existing local singleton-basis predicate. -/
theorem isInvertible_of_tensorSheafification_iso_unit {M N : X.Modules}
    (ε : tensorSheafification M N ≅ unitSheaf X) :
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M := by
  choose V hxV m n h1 using fun x : X => exists_pairingElem_tmul_eq_one ε x
  let t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M := {
    I := X
    X := V
    coversTop := by
      intro U
      intro x hx
      refine ⟨U ⊓ V x, homOfLE inf_le_left, ?_, ⟨hx, hxV x⟩⟩
      exact ⟨x, ⟨homOfLE inf_le_right⟩⟩
    iso := fun x =>
      SheafOfModules.freeUniqueIsoUnit (R := X.ringCatSheaf.over (V x)) PUnit ≪≫
        (nonempty_over_iso_unit_of_pairing ε (m x) (n x) (h1 x)).some.symm }
  exact KltDP.SheafOfModules.LocalTrivializations.isInvertible (R := X.ringCatSheaf) t

/-- Unfolding an actual unit in the skeleton tensor monoid produces an
actual tensor inverse, which supplies the local rank-one structure. -/
theorem isInvertible_of_isUnit_toSkeleton (M : X.Modules)
    (hM : letI := Scheme.Modules.monoidalCategory X
      IsUnit (toSkeleton M)) :
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M := by
  letI := Scheme.Modules.monoidalCategory X
  obtain ⟨v, hv, -⟩ := isUnit_iff_exists.mp hM
  let N : X.Modules := (fromSkeleton X.Modules).obj v
  have hvClass : toSkeleton N = v := Quotient.out_eq v
  rw [← hvClass, ← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq] at hv
  obtain ⟨e⟩ := (show Nonempty (M ⊗ N ≅ 𝟙_ X.Modules) from Quotient.exact hv)
  let ε : tensorSheafification M N ≅ unitSheaf X :=
    (PresheafOfModules.sheafTensorIsoSheafification
      X.sheaf.val X.ringCatSheaf.cond M N).symm ≪≫ e ≪≫
        PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  exact isInvertible_of_tensorSheafification_iso_unit ε

/-- The actual local rank-one property and actual tensor-invertibility
agree for a structure-sheaf module. -/
theorem isInvertible_iff_isUnit_toSkeleton (M : X.Modules) :
    letI := Scheme.Modules.monoidalCategory X
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M ↔ IsUnit (toSkeleton M) := by
  letI := Scheme.Modules.monoidalCategory X
  constructor
  · intro hM
    letI := hM
    exact KltDP.SheafOfModules.IsInvertible.isUnit_toSkeleton
      X.sheaf.val X.ringCatSheaf.cond M
  · exact isInvertible_of_isUnit_toSkeleton M

end KltDP.Geometry.SchemeTensorPairing
