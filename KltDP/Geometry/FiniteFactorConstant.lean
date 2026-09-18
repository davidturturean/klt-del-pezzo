import KltDP.Geometry.LinearSystemTrivialConstant
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Constancy reflected through a finite morphism

For an original connected reduced proper scheme over an algebraically closed
field, a morphism whose composite with a finite morphism is a specified field
point is itself a field point. The proof factors the actual lift into the
finite affine fiber through the original structure morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.FiniteFactorConstant

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
  (σ : C ⟶ Spec (CommRingCat.of k))
  [IsProper σ] [IsReduced C] [ConnectedSpace C]

include σ

/-- The original structure morphism is an isomorphism on global functions. -/
theorem structure_appTop_isIso : IsIso σ.appTop := by
  letI : IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ σ.appTop) := by
    change IsIso (specHomRingHom σ)
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ProperConnectedReducedConstants.baseFieldToGlobalSections_bijective σ
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of k)).inv σ.appTop

/-- Postcomposition of the original structure morphism is injective for
actual affine targets. -/
theorem structure_comp_injective {W : Scheme.{u}} [IsAffine W] :
    Function.Injective (fun p : Spec (CommRingCat.of k) ⟶ W => σ ≫ p) := by
  letI := structure_appTop_isIso σ
  intro p q hpq
  apply ext_of_isAffine
  apply (cancel_mono σ.appTop).mp
  simpa only [Scheme.comp_appTop] using
    congrArg (fun t : C ⟶ W => t.appTop) hpq

/-- The point determined by an original morphism into an affine scheme. -/
def affinePoint {F : Scheme.{u}} [IsAffine F] (ℓ : C ⟶ F) :
    Spec (CommRingCat.of k) ⟶ F :=
  LinearSystemTrivialConstant.affineConstantPoint σ (ℓ ≫ F.isoSpec.hom) ≫ F.isoSpec.inv

/-- Factorization through the original structure map, with the actual affine target. -/
theorem structure_affinePoint {F : Scheme.{u}} [IsAffine F] (ℓ : C ⟶ F) :
    σ ≫ affinePoint σ ℓ = ℓ := by
  dsimp only [affinePoint]
  rw [← Category.assoc, LinearSystemTrivialConstant.structure_affineConstantPoint,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A specified field-point factorization is reflected through an actual finite map. -/
theorem exists_point_lift {Z Y : Scheme.{u}} (π : Z ⟶ Y) [IsFinite π]
    (y : Spec (CommRingCat.of k) ⟶ Y) (g : C ⟶ Z)
    (h : g ≫ π = σ ≫ y) :
    ∃ z : Spec (CommRingCat.of k) ⟶ Z, z ≫ π = y ∧ g = σ ≫ z := by
  letI : IsAffineHom (pullback.snd π y) :=
    MorphismProperty.pullback_snd π y (inferInstance : IsAffineHom π)
  letI : IsAffine (pullback π y : Scheme.{u}) :=
    isAffine_of_isAffineHom (pullback.snd π y)
  let ℓ : C ⟶ pullback π y := pullback.lift g σ h
  let p : Spec (CommRingCat.of k) ⟶ pullback π y := affinePoint σ ℓ
  have hp : σ ≫ p = ℓ := structure_affinePoint σ ℓ
  have hpOver : p ≫ pullback.snd π y = 𝟙 _ := by
    apply structure_comp_injective σ
    calc
      σ ≫ (p ≫ pullback.snd π y) = ℓ ≫ pullback.snd π y := by
        rw [← Category.assoc, hp]
      _ = σ := pullback.lift_snd g σ h
      _ = σ ≫ 𝟙 _ := (Category.comp_id σ).symm
  refine ⟨p ≫ pullback.fst π y, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hpOver, Category.id_comp]
  · calc
      g = ℓ ≫ pullback.fst π y := (pullback.lift_fst g σ h).symm
      _ = σ ≫ (p ≫ pullback.fst π y) := by rw [← Category.assoc, hp]

end KltDP.Geometry.FiniteFactorConstant
