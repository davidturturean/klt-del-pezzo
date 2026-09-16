import KltDP.Geometry.InvertibleSheafTwistFrame
import KltDP.Geometry.QuasicoherentSectionExtension

/-!
# Actual twisted section extension on a frame

On a quasi-compact and quasi-separated scheme with an actual frame of an
invertible sheaf, a section of a quasicoherent coefficient module on the
nonvanishing open extends after multiplication by every sufficiently high
power of the original line-sheaf section. The output is an actual section
of the original tensor twist and its restriction is the original tensor
multiplication morphism applied to the given local section.

This is the chart extension used before overlap gluing. A global frame is
an explicit hypothesis here; the general nontrivial line-sheaf extension and
an actual Serre-ample witness remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafFrameSectionExtension

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance frameExtensionMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance originalSectionModule {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) :
    Module Γ(X, V) (M.val.obj (op V)) := (M.val.obj (op V)).isModule

open InvertibleSheafSectionPowers InvertibleSheafTwistFrame

variable {X : Scheme.{u}} (M : X.Modules) (L : InvertibleSheaf X)

set_option maxHeartbeats 800000 in
/-- Every sufficiently high actual power twist extends the original local
section after multiplication by the original power-section morphism. -/
theorem eventually_exists_twisted_extension [M.IsQuasicoherent]
    (hX : IsCompact (Set.univ : Set X)) (hXqs : IsQuasiSeparated (Set.univ : Set X))
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (s : L.obj.sections)
    (t : M.val.obj (op (X.basicOpen (frameCoefficient L e s)))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ v : (M ⊗ (power L n).obj).val.obj (op ⊤),
        (M ⊗ (power L n).obj).val.map
            (homOfLE (X.basicOpen_le (frameCoefficient L e s))).op v =
          (rightTwistMap M L s n).val.app (op (X.basicOpen (frameCoefficient L e s))) t := by
  let a := frameCoefficient L e s
  let D := X.basicOpen a
  let j : op (⊤ : X.Opens) ⟶ op D := (homOfLE (X.basicOpen_le a)).op
  obtain ⟨N, u, hu⟩ :=
    QuasicoherentSectionExtension.exists_restrict_eq_pow_smul_of_qcqs M
      (U := ⊤) hX hXqs a t
  change M.val.map j u = X.presheaf.map j (a ^ N) • t at hu
  refine ⟨N, fun n hn => ?_⟩
  let u' : M.val.obj (op ⊤) := a ^ (n - N) • u
  have hu' : M.val.map j u' = X.presheaf.map j (a ^ n) • t := by
    change M.val.map j (a ^ (n - N) • u) = _
    rw [M.val.map_smul, hu, smul_smul]
    change (X.presheaf.map j (a ^ (n - N)) * X.presheaf.map j (a ^ N)) • t = _
    rw [← map_mul, ← pow_add, Nat.sub_add_cancel hn]
  let ε := rightTwistFrame M L e n
  let v : (M ⊗ (power L n).obj).val.obj (op ⊤) := ε.inv.val.app (op ⊤) u'
  have hm : ε.hom.val.app (op D) ((rightTwistMap M L s n).val.app (op D) t) =
      X.presheaf.map j (a ^ n) • t :=
    rightTwistMap_frame_apply M L e s n D t
  refine ⟨v, ?_⟩
  calc
    _ = ε.inv.val.app (op D) (M.val.map j u') :=
      (PresheafOfModules.naturality_apply ε.inv.val j u').symm
    _ = ε.inv.val.app (op D) (X.presheaf.map j (a ^ n) • t) :=
      congrArg (ε.inv.val.app (op D)) hu'
    _ = ε.inv.val.app (op D)
        (ε.hom.val.app (op D) ((rightTwistMap M L s n).val.app (op D) t)) :=
      congrArg (ε.inv.val.app (op D)) hm.symm
    _ = _ := congrArg (fun g : M ⊗ (power L n).obj ⟶ M ⊗ (power L n).obj =>
      g.val.app (op D) ((rightTwistMap M L s n).val.app (op D) t)) ε.hom_inv_id

end KltDP.Geometry.InvertibleSheafFrameSectionExtension
