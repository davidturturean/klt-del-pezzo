import KltDP.Geometry.SchemeConormal
import KltDP.Geometry.BaseRingCohomology

/-!
# Original scalar actions under module pushforward

Pushforward takes multiplication by the pullback of a global function
to multiplication by that function on the original pushforward module.
The proof uses the naturality of the original scheme structure map on
every open. Global sections and degree-zero cohomology are then compared
linearly over the original commutative base ring.

These statements apply to an arbitrary scheme morphism and module.
They do not assert a comparison of higher cohomology groups.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original section map commutes with restriction of a global scalar. -/
theorem app_restrictGlobal (r : Γ(Y, ⊤)) (U : Y.Opens) :
    f.app U (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) =
      X.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op (f.appTop r) := by
  exact ConcreteCategory.congr_hom
    (f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op) r

/-- Pushforward preserves the original scalar endomorphism, with its
scalar transported by the original structure map. -/
theorem globalSmulHom_pushforward (M : X.Modules) (r : Γ(Y, ⊤)) :
    globalSmulHom ((schemeModulePushforward f).obj M) r =
      (schemeModulePushforward f).map (globalSmulHom M (f.appTop r)) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let act : X.ringCatSheaf.val.obj (op (f ⁻¹ᵁ U.unop)) →
      M.val.obj (op (f ⁻¹ᵁ U.unop)) → M.val.obj (op (f ⁻¹ᵁ U.unop)) :=
    @SMul.smul _ _ (M.val.obj (op (f ⁻¹ᵁ U.unop))).isModule.toSMul
  change act (f.app U.unop
      (Y.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r)) s =
    act (X.presheaf.map (homOfLE (show f ⁻¹ᵁ U.unop ≤ ⊤ from le_top)).op
      (f.appTop r)) s
  rw [app_restrictGlobal]

variable {A : Type u} [CommRing A] (g : Y ⟶ Spec (CommRingCat.of A))

/-- The original base-ring scalar on a composite is its original pullback scalar. -/
theorem appTop_baseRingScalar (a : A) :
    f.appTop (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) =
      (f ≫ g).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) := rfl

/-- The global sections of the original pushforward are the original
source sections, linearly over the same base ring. -/
def pushforwardSectionsBaseRingLinearEquiv (M : X.Modules) :
    letI := baseRingSectionsModule g ((schemeModulePushforward f).obj M)
    letI := baseRingSectionsModule (f ≫ g) M
    sections ((schemeModulePushforward f).obj M) ≃ₗ[A] sections M := by
  letI := baseRingSectionsModule g ((schemeModulePushforward f).obj M)
  letI := baseRingSectionsModule (f ≫ g) M
  refine { AddEquiv.refl (sections M) with map_smul' := ?_ }
  intro a s
  let act : X.ringCatSheaf.val.obj (op (⊤ : X.Opens)) → sections M → sections M :=
    @SMul.smul _ _ (sections M).isModule.toSMul
  change act (f.appTop (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) s =
    act ((f ≫ g).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) s
  rfl

/-- In degree zero the original cohomology comparison is base-ring-linear. -/
def pushforwardHZeroBaseRingLinearEquiv (M : X.Modules) :
    letI := baseRingModule g ((schemeModulePushforward f).obj M) 0
    letI := baseRingModule (f ≫ g) M 0
    H ((schemeModulePushforward f).obj M) 0 ≃ₗ[A] H M 0 := by
  letI := baseRingModule g ((schemeModulePushforward f).obj M) 0
  letI := baseRingModule (f ≫ g) M 0
  letI := baseRingSectionsModule g ((schemeModulePushforward f).obj M)
  letI := baseRingSectionsModule (f ≫ g) M
  exact (hZeroBaseRingLinearEquivSections g ((schemeModulePushforward f).obj M)).trans
    ((pushforwardSectionsBaseRingLinearEquiv f g M).trans
      (hZeroBaseRingLinearEquivSections (f ≫ g) M).symm)

/-- The comparison retains the original degree-zero section map on both schemes. -/
theorem pushforwardHZeroBaseRingLinearEquiv_sections (M : X.Modules)
    (x : H ((schemeModulePushforward f).obj M) 0) :
    hZeroEquivGlobalSections M (pushforwardHZeroBaseRingLinearEquiv f g M x) =
      hZeroEquivGlobalSections ((schemeModulePushforward f).obj M) x := by
  dsimp only [pushforwardHZeroBaseRingLinearEquiv, pushforwardSectionsBaseRingLinearEquiv,
    hZeroBaseRingLinearEquivSections, hZeroCanonicalLinearEquivGlobalSections,
    LinearEquiv.trans, LinearEquiv.symm, LinearEquiv.restrictScalars, AddEquiv.refl]
  exact (hZeroEquivGlobalSections M).apply_symm_apply _

end KltDP.Geometry.ModuleCohomology
