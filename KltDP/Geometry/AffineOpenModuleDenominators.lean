import KltDP.Geometry.AffineQuasicoherentCounit
import KltDP.Geometry.QuasicoherentOpenRestriction

/-!
# Denominator extension on the original affine opens

Restrict an original quasicoherent module along the canonical map
Spec Γ(X,U) → X. Its original scalar maps agree with the canonical
sections of Spec Γ(X,U). The actual image-open section equivalences
therefore transport denominator extension to U and its intrinsic basic
opens. In particular, the scalar on the original basic open is the
restriction of the original section of U.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace SchemeModuleRestriction

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
  (M : X.Modules)

local instance originalModule (U : X.Opens) :
    Module Γ(X, U) (M.val.presheaf.obj (op U)) :=
  (M.val.obj (op U)).isModule

/-- The original additive section comparison, with its image open identified. -/
def sectionsOfImageEq (V : Y.Opens) (W : X.Opens) (h : f ''ᵁ V = W) :
    ((restriction f).obj M).val.presheaf.obj (op V) ≃+
      M.val.presheaf.obj (op W) := by
  subst W
  exact (restrictionSectionsIso f M V).addCommGroupIsoToAddEquiv

/-- The comparison retains the original restriction maps. -/
theorem sectionsOfImageEq_naturality {V V' : Y.Opens} {W W' : X.Opens}
    (h : f ''ᵁ V = W) (h' : f ''ᵁ V' = W') (i : V' ≤ V) (j : W' ≤ W)
    (s : ((restriction f).obj M).val.obj (op V)) :
    sectionsOfImageEq f M V' W' h'
        (((restriction f).obj M).val.map (homOfLE i).op s) =
      M.val.map (homOfLE j).op (sectionsOfImageEq f M V W h s) := by
  subst W
  subst W'
  rfl

/-- The same comparison transports scalars through the original scheme map. -/
theorem sectionsOfImageEq_smul {U W : X.Opens} (V : Y.Opens)
    (h : f ''ᵁ V = W) (j : W ≤ U) (i : V ≤ f ⁻¹ᵁ U)
    (r : Γ(X, U)) (s : ((restriction f).obj M).val.obj (op V)) :
    sectionsOfImageEq f M V W h (f.appLE U V i r • s) =
      X.presheaf.map (homOfLE j).op r • sectionsOfImageEq f M V W h s := by
  subst W
  letI : Module Γ(X, f ''ᵁ V) (((restriction f).obj M).val.obj (op V)) :=
    (M.val.obj (op (f ''ᵁ V))).isModule
  change (f.appIso V).inv (f.appLE U V i r) •
      (s : M.val.obj (op (f ''ᵁ V))) =
    X.presheaf.map (homOfLE j).op r • (s : M.val.obj (op (f ''ᵁ V)))
  exact congrArg (fun a : Γ(X, f ''ᵁ V) => a • (s : M.val.obj (op (f ''ᵁ V))))
    (ConcreteCategory.congr_hom (Scheme.Hom.appLE_appIso_inv f i) r)

end SchemeModuleRestriction

namespace AffineOpenModule

open SchemeModuleRestriction AffineModuleTilde

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

/-- The canonical affine chart sends its whole source onto the original open. -/
theorem fromSpec_image_top : hU.fromSpec ''ᵁ ⊤ = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]

/-- On every source open, the original chart map is the canonical section map. -/
theorem fromSpec_appLE (V : (Spec Γ(X, U)).Opens)
    (h : V ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U V h =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫
        (Spec Γ(X, U)).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  rfl

variable (M : X.Modules)

local instance originalModule (W : X.Opens) :
    Module Γ(X, W) (M.val.presheaf.obj (op W)) :=
  (M.val.obj (op W)).isModule

/-- Original base-ring scalars on the affine chart become restrictions of
the same original sections of U. -/
theorem sectionsOfImageEq_base_smul (V : (Spec Γ(X, U)).Opens) (W : X.Opens)
    (h : hU.fromSpec ''ᵁ V = W) (j : W ≤ U) (r : Γ(X, U))
    (s : sectionModule ((restriction hU.fromSpec).obj M) V) :
    sectionsOfImageEq hU.fromSpec M V W h (r • s) =
      X.presheaf.map (homOfLE j).op r •
        sectionsOfImageEq hU.fromSpec M V W h s := by
  have i : V ≤ hU.fromSpec ⁻¹ᵁ U := by
    rw [hU.fromSpec_preimage_self]
    exact le_top
  letI : Module Γ(Spec Γ(X, U), V)
      (sectionModule ((restriction hU.fromSpec).obj M) V) :=
    (((restriction hU.fromSpec).obj M).val.obj (op V)).isModule
  rw [sectionModule_smul]
  change sectionsOfImageEq hU.fromSpec M V W h
      (((Scheme.ΓSpecIso Γ(X, U)).inv ≫
        (Spec Γ(X, U)).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op) r •
          (s : ((restriction hU.fromSpec).obj M).val.obj (op V))) = _
  rw [← fromSpec_appLE hU V i]
  exact sectionsOfImageEq_smul hU.fromSpec M V h j i r s

include hU in
/-- An original section on an intrinsic basic open extends to the
original affine open after multiplying by a power of its defining section. -/
theorem exists_restrict_eq_pow_smul [M.IsQuasicoherent]
    (f : Γ(X, U)) (s : M.val.obj (op (X.basicOpen f))) :
    ∃ (n : ℕ) (t : M.val.obj (op U)),
      M.val.map (homOfLE (X.basicOpen_le f)).op t =
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • s := by
  let N := (restriction hU.fromSpec).obj M
  let eTop := sectionsOfImageEq hU.fromSpec M ⊤ U (fromSpec_image_top hU)
  let eBasic := sectionsOfImageEq hU.fromSpec M (PrimeSpectrum.basicOpen f)
    (X.basicOpen f) (hU.fromSpec_image_basicOpen f)
  obtain ⟨n, t, ht⟩ :=
    (denominatorExtension_of_isQuasicoherent N).existence f le_top (eBasic.symm s)
  refine ⟨n, eTop t, ?_⟩
  calc
    M.val.map (homOfLE (X.basicOpen_le f)).op (eTop t) =
        eBasic (N.val.map (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op t) :=
      (sectionsOfImageEq_naturality hU.fromSpec M (fromSpec_image_top hU)
        (hU.fromSpec_image_basicOpen f) le_top (X.basicOpen_le f) t).symm
    _ = eBasic (f ^ n • (show sectionModule N (PrimeSpectrum.basicOpen f) from
        eBasic.symm s)) := congrArg eBasic ht
    _ = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) •
        eBasic (eBasic.symm s) :=
      sectionsOfImageEq_base_smul hU M (PrimeSpectrum.basicOpen f)
        (X.basicOpen f) (hU.fromSpec_image_basicOpen f) (X.basicOpen_le f)
        (f ^ n) (eBasic.symm s)
    _ = _ := by rw [AddEquiv.apply_symm_apply]

end AffineOpenModule

end KltDP.Geometry
