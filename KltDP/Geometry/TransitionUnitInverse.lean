import KltDP.Geometry.TransitionUnitTensor
import KltDP.Geometry.TransitionUnitConstant
import KltDP.Geometry.InvertibleSheafPicard

/-!
# The inverse transition sheaf is the original line's actual dual

Inverse units satisfy the original cocycle equation. The already proved
tensor multiplication and identity-cocycle comparison identify their
module sheaf as a tensor inverse. Comparison with the original evaluation
then gives an actual isomorphism to the sheaf dual, retaining the
original coordinate identification.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u v w

namespace KltDP.Geometry.TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
  (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)

/-- The inverse of the original unit on each original double overlap. -/
def inverseUnits (i j : ι) : Γ(X, U i ⊓ U j)ˣ := (g i j)⁻¹

/-- Inverting the actual transition units preserves their cocycle law. -/
theorem inverseUnits_isCocycle (hg : IsCocycle X U g) :
    IsCocycle X U (inverseUnits X U g) where
  unit_self i := by
    have hi : g i i = 1 := Units.ext (hg.unit_self i)
    simp only [inverseUnits, hi, inv_one, Units.val_one]
  mul_res i j l := by
    let a : Γ(X, U i ⊓ U j ⊓ U l)ˣ :=
      Units.map (res X (inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U j)).toMonoidHom (g i j)
    let b : Γ(X, U i ⊓ U j ⊓ U l)ˣ :=
      Units.map (res X (inclCoc X U (U i) j l)).toMonoidHom (g j l)
    let c : Γ(X, U i ⊓ U j ⊓ U l)ˣ :=
      Units.map (res X (inclSnd X U (U i) j l)).toMonoidHom (g i l)
    have hab : a * b = c := Units.ext (hg.mul_res i j l)
    change ((a⁻¹ * b⁻¹ : Γ(X, U i ⊓ U j ⊓ U l)ˣ) :
      Γ(X, U i ⊓ U j ⊓ U l)) = (c⁻¹ : Γ(X, U i ⊓ U j ⊓ U l)ˣ)
    apply congrArg Units.val
    rw [← hab, mul_inv]

/-- The original transition and its inverse multiply to the identity transition. -/
theorem productUnits_inverseUnits :
    productUnits X U g (inverseUnits X U g) = oneUnits X U := by
  funext i j
  exact mul_inv_cancel (g i j)

local instance inverseTransitionModulesMonoidal : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance inverseTransitionModulesSymmetric : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

/-- Tensor multiplication is the actual inverse-cocycle evaluation. -/
def inverseUnitEvaluationIso (hg : IsCocycle X U g) (hU : (⨆ i, U i) = ⊤) :
    moduleSheaf X U g ⊗ moduleSheaf X U (inverseUnits X U g) ≅
      _root_.SheafOfModules.unit X.ringCatSheaf :=
  tensorIso X U g (inverseUnits X U g) hg (inverseUnits_isCocycle X U g hg) hU ≪≫
    eqToIso (congrArg (moduleSheaf X U) (productUnits_inverseUnits X U g)) ≪≫
      (unitIsoOne X U hU).symm

private def tensorInverseComparison
    {C : Type w} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    {A B D : C} (e : A ⊗ B ≅ 𝟙_ C) (d : A ⊗ D ≅ 𝟙_ C) : B ≅ D :=
  (λ_ B).symm ≪≫ MonoidalCategory.tensorIso (((β_ D A) ≪≫ d).symm) (Iso.refl B) ≪≫
    (α_ D A B) ≪≫ MonoidalCategory.tensorIso (Iso.refl D) e ≪≫ (ρ_ D)

local instance inverseCoordinateScalarComm :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

/-- If the original line has the given actual coordinate sheaf, the
inverse coordinates are its actual sheaf of linear functionals. -/
def inverseCoordinatesDualIso (hg : IsCocycle X U g) (hU : (⨆ i, U i) = ⊤)
    (L : InvertibleSheaf X) (eL : L.obj ≅ moduleSheaf X U g) :
    moduleSheaf X U (inverseUnits X U g) ≅ KltDP.SheafOfModules.dual X.ringCatSheaf L.obj :=
  tensorInverseComparison
    (MonoidalCategory.tensorIso eL (Iso.refl _) ≪≫ inverseUnitEvaluationIso X U g hg hU ≪≫
      (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).symm)
    (KltDP.SheafOfModules.tensorDualIsoUnit X.sheaf.val X.ringCatSheaf.cond L.obj)

end KltDP.Geometry.TransitionUnitGluing

#check @KltDP.Geometry.TransitionUnitGluing.inverseCoordinatesDualIso
#print axioms KltDP.Geometry.TransitionUnitGluing.inverseCoordinatesDualIso
