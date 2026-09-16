import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The actual sheaf of base-ring differentials

The pinned differential presheaf has a proved universal derivation.
Sheafifying that presheaf and using the original module-sheafification
adjunction proves its universal property into actual structure-module
sheaves. The source ring presheaf need not itself be a sheaf.

For an original structure morphism `f : X ⟶ Spec A`, the scalar map
is the constant presheaf `A` mapping to the original structure presheaf
through `ΓSpecIso.inv`, `f.appTop`, and restriction. The resulting
derivation kills the scalars specified by this map and commutes with
the original restriction maps. No cover or differential frame is supplied.

This constructs a global module sheaf and proves its representing
property for base-ring derivations. Affine tilde comparison, local
freeness on smooth schemes, top exterior powers, and comparison with
the general regular dualizing sheaf remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeKaehlerSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section RingPresheaf

variable {X : Scheme.{u}} {S : X.Opensᵒᵖ ⥤ CommRingCat.{u}}
variable (φ : S ⟶ X.presheaf)

/-- The existing componentwise differential presheaf, with its original
structure-ring action and restriction maps. -/
abbrev presheaf : X.PresheafOfModules :=
  _root_.PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ

/-- Sheafification of the actual differential presheaf. -/
def sheaf : X.Modules :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj (presheaf φ)

/-- The original module-sheafification unit on the differential presheaf. -/
def toSheaf : presheaf φ ⟶ (sheaf φ).val :=
  (_root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.val)).unit.app (presheaf φ)

/-- The original universal presheaf derivation, followed by sheafification. -/
def derivation : (sheaf φ).val.Derivation' φ :=
  (_root_.PresheafOfModules.DifferentialsConstruction.derivation' φ).postcomp
    (toSheaf φ)

/-- Every derivation into an actual module sheaf induces a morphism from
the constructed differential sheaf. -/
def desc {M : X.Modules} (d : M.val.Derivation' φ) : sheaf φ ⟶ M :=
  (_root_.PresheafOfModules.sheafificationHomEquiv
    (𝟙 X.ringCatSheaf.val)).symm
      ((_root_.PresheafOfModules.DifferentialsConstruction.isUniversal' φ).desc d)

/-- The sheafification adjunction is the original unit-composition map. -/
theorem toSheaf_comp {M : X.Modules} (g : sheaf φ ⟶ M) :
    toSheaf φ ≫ g.val =
      _root_.PresheafOfModules.sheafificationHomEquiv
        (𝟙 X.ringCatSheaf.val) g := by
  exact ((_root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.val)).homEquiv_unit (presheaf φ) M g).symm

/-- The induced sheaf map extends the original universal presheaf map. -/
theorem toSheaf_comp_desc {M : X.Modules} (d : M.val.Derivation' φ) :
    toSheaf φ ≫ (desc φ d).val =
      (_root_.PresheafOfModules.DifferentialsConstruction.isUniversal' φ).desc d := by
  rw [toSheaf_comp]
  exact (_root_.PresheafOfModules.sheafificationHomEquiv
    (𝟙 X.ringCatSheaf.val)).apply_symm_apply _

/-- The induced sheaf map recovers the given derivation on every open. -/
theorem derivation_postcomp_desc {M : X.Modules} (d : M.val.Derivation' φ) :
    (derivation φ).postcomp (desc φ d).val = d := by
  ext U b
  have h₁ := congrArg
    (fun g : presheaf φ ⟶ M.val =>
      g.app U
        ((_root_.PresheafOfModules.DifferentialsConstruction.derivation' φ).d b))
    (toSheaf_comp_desc φ d)
  have h₂ := _root_.PresheafOfModules.Derivation.congr_d
    ((_root_.PresheafOfModules.DifferentialsConstruction.isUniversal' φ).fac d) b
  exact h₁.trans h₂

/-- A morphism from the constructed sheaf is determined by its composite
with the original derivation; no local generation is assumed. -/
theorem hom_ext {M : X.Modules} {g h : sheaf φ ⟶ M}
    (heq : (derivation φ).postcomp g.val = (derivation φ).postcomp h.val) : g = h := by
  apply (_root_.PresheafOfModules.sheafificationHomEquiv
    (𝟙 X.ringCatSheaf.val)).injective
  rw [← toSheaf_comp, ← toSheaf_comp]
  apply (_root_.PresheafOfModules.DifferentialsConstruction.isUniversal' φ).postcomp_injective
  ext U b
  exact _root_.PresheafOfModules.Derivation.congr_d heq b

/-- The actual differential sheaf represents derivations into every
original structure-module sheaf. Both inverse laws are proved. -/
def homEquiv (M : X.Modules) :
    (sheaf φ ⟶ M) ≃ M.val.Derivation' φ where
  toFun g := (derivation φ).postcomp g.val
  invFun := desc φ
  left_inv g := hom_ext φ (derivation_postcomp_desc φ _)
  right_inv := derivation_postcomp_desc φ

/-- Evaluation of the sheaf differential is the actual unit applied to
the ordinary Kähler differential of a section. -/
theorem derivation_d (U : X.Opensᵒᵖ) (b : X.presheaf.obj U) :
    (derivation φ).d b =
      (toSheaf φ).app U (CommRingCat.KaehlerDifferential.d b) := rfl

/-- The global sheaf differential retains the original Leibniz rule. -/
theorem derivation_mul (U : X.Opensᵒᵖ) (a b : X.presheaf.obj U) :
    (derivation φ).d (a * b) = a • (derivation φ).d b + b • (derivation φ).d a :=
  (derivation φ).d_mul a b

/-- Differentiation commutes with every actual open restriction. -/
theorem derivation_restrict {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (b : X.presheaf.obj U) :
    (derivation φ).d (X.presheaf.map i b) =
      (sheaf φ).val.map i ((derivation φ).d b) :=
  (derivation φ).d_map i b

/-- The original source-presheaf scalars are killed on each actual open. -/
theorem derivation_scalar (U : X.Opensᵒᵖ) (a : S.obj U) :
    (derivation φ).d (φ.app U a) = 0 :=
  _root_.PresheafOfModules.Derivation'.d_app (derivation φ) a

end RingPresheaf

section BaseRing

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of A))

/-- The original base-ring scalar map on every open, using precisely the
same `ΓSpecIso.inv` and `appTop` normalization as base-ring cohomology. -/
def scalarPresheafHom :
    (Functor.const X.Opensᵒᵖ).obj (CommRingCat.of A) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫
    X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  naturality {U V} i := by
    ext a
    symm
    change X.presheaf.map i
        (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
          (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
      X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op
        (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))
    rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
    exact congrArg
      (fun j : op (⊤ : X.Opens) ⟶ V =>
        X.presheaf.map j (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))
      (Subsingleton.elim _ _)

/-- At the top open, the scalar map is exactly the original global
base-ring map used by the cohomology and affine geometry adapters. -/
theorem scalarPresheafHom_app_top :
    (scalarPresheafHom f).app (op (⊤ : X.Opens)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop := by
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫
    X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op = _
  rw [show (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op = 𝟙 _ from
    Subsingleton.elim _ _, X.presheaf.map_id, Category.comp_id]

/-- The global differential sheaf relative to the original base ring. -/
abbrev baseRingSheaf : X.Modules := sheaf (scalarPresheafHom f)

/-- Its original sectionwise derivation. -/
abbrev baseRingDerivation :
    (baseRingSheaf f).val.Derivation' (scalarPresheafHom f) :=
  derivation (scalarPresheafHom f)

/-- The actual scalar functions induced by `f` have zero differential. -/
theorem baseRingDerivation_scalar (U : X.Opens) (a : A) :
    (baseRingDerivation f).d
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) = 0 :=
  derivation_scalar (scalarPresheafHom f) (op U) a

/-- The constructed module sheaf represents base-ring derivations for
the original structure morphism; no global or local frame is an input. -/
def baseRingHomEquiv (M : X.Modules) :
    (baseRingSheaf f ⟶ M) ≃ M.val.Derivation' (scalarPresheafHom f) :=
  homEquiv (scalarPresheafHom f) M

end BaseRing

end KltDP.Geometry.SchemeKaehlerSheaf
