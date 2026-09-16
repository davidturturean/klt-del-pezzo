import KltDP.Geometry.InvertibleSheafTwistFrame
import KltDP.Geometry.QuasicoherentSectionPowerZero

/-!
# Uniform twisted equality on an actual frame

For original quasicoherent sections equal on the coefficient nonvanishing
open, all sufficiently high powers of the original line-sheaf section give
equal original tensor sections. The exponent comes from the already proved
quasi-compact power-zero theorem. The actual power frame then transports
that scalar equality back to the original tensor twist.

This is the equality step for overlap gluing. A frame of the actual line
sheaf is explicit; neither a gluing family nor a killing exponent is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafFrameSectionPowerZero

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance framePowerZeroMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance originalSectionModule {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) :
    Module Γ(X, V) (M.val.obj (op V)) := (M.val.obj (op V)).isModule

open InvertibleSheafSectionPowers InvertibleSheafTwistFrame

variable {X : Scheme.{u}} (M : X.Modules) (L : InvertibleSheaf X)

/-- On any quasi-compact original open of a framed scheme, equality on
the literal coefficient basic open gives equality in every sufficiently
high actual tensor twist. Quasi-separatedness is unnecessary for this step. -/
theorem eventually_rightTwistMap_eq_of_restrict_eq [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact (U : Set X))
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (s : L.obj.sections)
    (t v : M.val.obj (op U))
    (heq : M.val.map
        (homOfLE (X.basicOpen_le
          (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
            (frameCoefficient L e s)))).op t =
      M.val.map
        (homOfLE (X.basicOpen_le
          (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
            (frameCoefficient L e s)))).op v) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (rightTwistMap M L s n).val.app (op U) t =
        (rightTwistMap M L s n).val.app (op U) v := by
  let a : Γ(X, U) := X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
    (frameCoefficient L e s)
  obtain ⟨N, hN⟩ :=
    QuasicoherentSectionPowerZero.exists_pow_smul_eq_of_isCompact M hU a t v heq
  refine ⟨N, fun n hn => ?_⟩
  have hpow : a ^ n • t = a ^ n • v := by
    have h := congrArg (fun z : M.val.obj (op U) => a ^ (n - N) • z) hN
    simpa only [smul_smul, ← pow_add, Nat.sub_add_cancel hn] using h
  let ε := rightTwistFrame M L e n
  have ht : ε.hom.val.app (op U) ((rightTwistMap M L s n).val.app (op U) t) =
      a ^ n • t := by
    simpa only [a, map_pow] using rightTwistMap_frame_apply M L e s n U t
  have hv : ε.hom.val.app (op U) ((rightTwistMap M L s n).val.app (op U) v) =
      a ^ n • v := by
    simpa only [a, map_pow] using rightTwistMap_frame_apply M L e s n U v
  have hinv (z : (M ⊗ (power L n).obj).val.obj (op U)) :
      ε.inv.val.app (op U) (ε.hom.val.app (op U) z) = z :=
    congrArg (fun g : M ⊗ (power L n).obj ⟶ M ⊗ (power L n).obj =>
      g.val.app (op U) z) ε.hom_inv_id
  exact (hinv _).symm.trans
    ((congrArg (ε.inv.val.app (op U)) (ht.trans (hpow.trans hv.symm))).trans (hinv _))

end KltDP.Geometry.InvertibleSheafFrameSectionPowerZero
