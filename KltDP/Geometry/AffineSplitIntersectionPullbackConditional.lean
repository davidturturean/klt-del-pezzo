import KltDP.Geometry.AffineSplitLineEulerConditional
import KltDP.Geometry.EulerPairingUnconditional

/-!
# Degree-two intersection pullback from an actual affine line splitting

The original sheaf splitting f_*O ≅ O ⊞ N yields every pulled Picard Euler
value. Translation invariance of the original Euler second difference
follows from the already proved surface pairing bilinearity. The actual
intersection pairing therefore doubles on pullback, with no numerical
projection or degree formula supplied as a hypothesis.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance affineSplitIntersectionModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The original integer Euler second difference is invariant under
translation by an actual Picard class, by proved bilinearity. -/
private theorem translated_picardEulerPairing (S : NormalProjectiveSurface k)
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x) (r p q : S.toScheme.Pic) :
    picardEulerValue S.structureMorphism r -
        picardEulerValue S.structureMorphism (r * p⁻¹) -
        picardEulerValue S.structureMorphism (r * q⁻¹) +
        picardEulerValue S.structureMorphism (r * (p⁻¹ * q⁻¹)) = S.picardEulerPairing p q := by
  have h := S.picardEulerPairing_mul_left_of_regular hregular r⁻¹ p q
  simp only [picardEulerPairing, mul_inv, inv_inv, mul_assoc] at h ⊢
  omega

variable (hAffine : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsAffineHom f] (n : ℕ),
    ∃ e : ∀ (M : X.Modules), M.IsQuasicoherent →
      H ((schemeModulePushforward f).obj M) n ≃+ H M n,
      ∀ (M N : X.Modules) (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
        (φ : M ⟶ N) (x : H ((schemeModulePushforward f).obj M) n),
        e N hN ((zariskiFunctor Y n).map ((schemeModulePushforward f).map φ) x) =
          (zariskiFunctor X n).map φ (e M hM x))

include hAffine

variable (S T : NormalProjectiveSurface k) (f : T.toScheme ⟶ S.toScheme) [IsAffineHom f]
  (hf : f ≫ S.structureMorphism = T.structureMorphism)
  (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
  (hT : ∀ y : T.Point, RegularPoint T.toScheme y)
  (N : InvertibleSheaf S.toScheme)
  (e : (schemeModulePushforward f).obj (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) ≅
    _root_.SheafOfModules.unit S.toScheme.ringCatSheaf ⊞ N.obj)

include hf e

/-- The original surface intersection pairing doubles under the same
morphism having the actual rank-two structure-sheaf splitting. -/
theorem picardPairing_pullback_of_affine_line_split (p q : S.toScheme.Pic) :
    T.picardPairing hT (schemePicardPullbackHom f p) (schemePicardPullbackHom f q) =
      2 * S.picardPairing hS p q := by
  have hχ (a : S.toScheme.Pic) :
      picardEulerValue T.structureMorphism (schemePicardPullbackHom f a) =
        picardEulerValue S.structureMorphism a +
          picardEulerValue S.structureMorphism (N.toPic * a) := by
    rw [← hf]
    exact picardEulerValue_pullback_of_split hAffine S f N e a
  rw [← T.picardEulerPairing_eq_picardPairing_of_regular hT,
    ← S.picardEulerPairing_eq_picardPairing_of_regular hS]
  unfold picardEulerPairing
  rw [show (1 : T.toScheme.Pic) = schemePicardPullbackHom f 1 from (map_one _).symm,
    ← map_inv (schemePicardPullbackHom f) p, ← map_inv (schemePicardPullbackHom f) q,
    ← map_mul (schemePicardPullbackHom f) p⁻¹ q⁻¹,
    hχ 1, hχ p⁻¹, hχ q⁻¹, hχ (p⁻¹ * q⁻¹)]
  have h := translated_picardEulerPairing S hS N.toPic p q
  simp only [picardEulerPairing, mul_one] at h ⊢
  omega

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.picardPairing_pullback_of_affine_line_split
