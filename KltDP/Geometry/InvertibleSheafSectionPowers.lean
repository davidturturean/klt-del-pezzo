import KltDP.Geometry.AmpleSerreDegreeBound
import KltDP.Geometry.SchemeStructureTensorScalar

/-!
# Actual tensor powers and their section coefficients

The power representative is built recursively from the original invertible
sheaf, the actual structure module and the existing sheaf tensor. Its Picard
class is the original power. The power section is an actual morphism from the
structure module, using the existing structure-module tensor multiplication.
An actual frame induces a frame of each power; its coefficient is the literal
power of the original section coefficient.

The scheme and frame may be any original chart. Comparing these constructions
under restriction and gluing twisted extensions across charts remain separate
steps. No ample sheaf or extension of a section is assumed or constructed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Geometry.InvertibleSheafSectionPowers

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance sectionPowerMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {X : Scheme.{u}}

open InvertibleSheafTensor

/-- The actual tensor-power representative, with the original structure
module in degree zero. -/
def power (L : InvertibleSheaf X) : ℕ → InvertibleSheaf X
  | 0 => InvertibleSheaf.trivial X
  | n + 1 => tensorInvertibleSheaf (power L n) L

/-- This constructed representative has the required original Picard class. -/
theorem power_toPic (L : InvertibleSheaf X) (n : ℕ) :
    (power L n).toPic = L.toPic ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact (RationalTreePicard.toPic_eq_one_iff_iso_unit (power L 0)).mpr
      ⟨Iso.refl _⟩
  | succ n ih =>
    change (tensorInvertibleSheaf (power L n) L).toPic = _
    rw [AmpleSerreDegreeBound.tensorInvertibleSheaf_toPic, ih, pow_succ]

/-- The original section tensored with itself, as an actual structure-module
morphism into the constructed power sheaf. -/
def powerSectionHom (L : InvertibleSheaf X) (s : L.obj.sections) :
    (n : ℕ) → _root_.SheafOfModules.unit X.ringCatSheaf ⟶ (power L n).obj
  | 0 => 𝟙 _
  | n + 1 =>
    (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (powerSectionHom L s n ⊗ L.obj.unitHomEquiv.symm s)

/-- The compatible family of actual sections defined by the power morphism. -/
def powerSection (L : InvertibleSheaf X) (s : L.obj.sections) (n : ℕ) :
    (power L n).obj.sections :=
  (power L n).obj.unitHomEquiv (powerSectionHom L s n)

/-- Tensoring the original frame gives an actual frame of every power. -/
def powerFrame (L : InvertibleSheaf X)
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) :
    (n : ℕ) → (power L n).obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf
  | 0 => Iso.refl _
  | n + 1 => (tensorIso (powerFrame L e n) e) ≪≫
    schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)

/-- The coefficient of the original section in the original frame. -/
def frameCoefficient (L : InvertibleSheaf X)
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf)
    (s : L.obj.sections) : Γ(X, ⊤) :=
  e.hom.val.app (op ⊤) (s.val (op ⊤))

/-- Applying a frame to the section morphism gives multiplication by its
literal coefficient, through the original unit-section equivalence. -/
theorem sectionHom_frame (L : InvertibleSheaf X)
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf)
    (s : L.obj.sections) :
    L.obj.unitHomEquiv.symm s ≫ e.hom = schemeScalarEnd (frameCoefficient L e s) := by
  have hs : (L.obj.unitHomEquiv.symm s).val.app (op ⊤) (1 : Γ(X, ⊤)) =
      s.val (op ⊤) :=
    congrArg (fun t : L.obj.sections => t.val (op ⊤))
      (L.obj.unitHomEquiv.apply_symm_apply s)
  apply (_root_.SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  apply (schemeModuleSectionsEquivTop _).injective
  change e.hom.val.app (op ⊤)
      ((L.obj.unitHomEquiv.symm s).val.app (op ⊤) (1 : Γ(X, ⊤))) =
    (schemeScalarEnd (frameCoefficient L e s)).val.app (op ⊤) (1 : Γ(X, ⊤))
  rw [hs, schemeScalarEnd_appTop, one_mul]
  rfl

private theorem scalar_one : schemeScalarEnd (1 : Γ(X, ⊤)) =
    𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf) := by
  apply (_root_.SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  apply (schemeModuleSectionsEquivTop _).injective
  change (schemeScalarEnd (1 : Γ(X, ⊤))).val.app (op ⊤) (1 : Γ(X, ⊤)) =
    (1 : Γ(X, ⊤))
  rw [schemeScalarEnd_appTop, one_mul]

/-- The actual power section, in its induced frame, is multiplication by
the literal power of the original coefficient. -/
theorem powerSectionHom_frame (L : InvertibleSheaf X)
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf)
    (s : L.obj.sections) (n : ℕ) :
    powerSectionHom L s n ≫ (powerFrame L e n).hom =
      schemeScalarEnd (frameCoefficient L e s ^ n) := by
  induction n with
  | zero =>
    simpa only [powerSectionHom, powerFrame, Iso.refl_hom, Category.id_comp,
      pow_zero] using (scalar_one (X := X)).symm
  | succ n ih =>
    simp only [powerSectionHom, powerFrame, Iso.trans_hom, tensorIso_hom,
      Category.assoc]
    rw [← tensor_comp_assoc, ih, sectionHom_frame, pow_succ]
    exact schemeStructureTensor_scalar_mul
      (frameCoefficient L e s ^ n) (frameCoefficient L e s)

/-- At every original open, the coefficient is the restriction of the
literal power of the original global coefficient. -/
theorem powerSection_frame_coefficient (L : InvertibleSheaf X)
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf)
    (s : L.obj.sections) (n : ℕ) (V : X.Opens) :
    (powerFrame L e n).hom.val.app (op V) ((powerSection L s n).val (op V)) =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (frameCoefficient L e s ^ n) := by
  have h := congrArg (fun f : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      _root_.SheafOfModules.unit X.ringCatSheaf =>
        f.val.app (op V) (1 : Γ(X, V))) (powerSectionHom_frame L e s n)
  change (powerFrame L e n).hom.val.app (op V)
      ((powerSection L s n).val (op V)) =
    (schemeScalarEnd (frameCoefficient L e s ^ n)).val.app (op V) (1 : Γ(X, V)) at h
  exact h.trans (by rw [schemeScalarEnd_app, one_mul])

/-- In particular, the coefficient on the chart itself is exactly the
ordinary power, with no transport left in the equation. -/
theorem powerSection_frame_coefficient_top (L : InvertibleSheaf X)
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf)
    (s : L.obj.sections) (n : ℕ) :
    frameCoefficient (power L n) (powerFrame L e n) (powerSection L s n) =
      frameCoefficient L e s ^ n := by
  have h := congrArg (fun f : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      _root_.SheafOfModules.unit X.ringCatSheaf =>
        f.val.app (op ⊤) (1 : Γ(X, ⊤))) (powerSectionHom_frame L e s n)
  change frameCoefficient (power L n) (powerFrame L e n) (powerSection L s n) =
    (schemeScalarEnd (frameCoefficient L e s ^ n)).val.app (op ⊤) (1 : Γ(X, ⊤)) at h
  exact h.trans (by rw [schemeScalarEnd_appTop, one_mul])

/-- Positive powers have the same actual nonvanishing open in the induced
frame as the original section. -/
theorem basicOpen_powerSection_frame (L : InvertibleSheaf X)
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf)
    (s : L.obj.sections) {n : ℕ} (hn : 0 < n) :
    X.basicOpen (frameCoefficient (power L n) (powerFrame L e n) (powerSection L s n)) =
      X.basicOpen (frameCoefficient L e s) := by
  rw [powerSection_frame_coefficient_top]
  exact X.basicOpen_pow _ hn

end KltDP.Geometry.InvertibleSheafSectionPowers
