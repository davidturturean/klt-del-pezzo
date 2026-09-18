import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Two actual stalk germs represented on one affine neighborhood

Pinned germ representability gives neighborhoods for the two germs. The
original affine-open basis refines their intersection with a prescribed
open. Restriction preserves both literal original germs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Two original stalk elements have simultaneous representatives on an
actual affine neighborhood inside any specified neighborhood. -/
theorem exists_affine_pair_stalk_representatives
    (X : Scheme.{u}) (x : X) (v : Fin 2 → X.presheaf.stalk x)
    (U : X.Opens) (hxU : x ∈ U) :
    ∃ (V : X.affineOpens) (_ : V.1 ≤ U) (hxV : x ∈ V.1)
      (s : Fin 2 → Γ(X, V.1)),
      ∀ i, X.presheaf.germ V.1 x hxV (s i) = v i := by
  obtain ⟨U₀, hx₀, s₀, hs₀⟩ := X.presheaf.germ_exist x (v 0)
  obtain ⟨U₁, hx₁, s₁, hs₁⟩ := X.presheaf.germ_exist x (v 1)
  let W : X.Opens := (U₀ ⊓ U₁) ⊓ U
  have hxW : x ∈ W := ⟨⟨hx₀, hx₁⟩, hxU⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open hxW W.isOpen
  have hVU : V ≤ U := le_trans hVW inf_le_right
  have hV₀ : V ≤ U₀ := le_trans hVW (le_trans inf_le_left inf_le_left)
  have hV₁ : V ≤ U₁ := le_trans hVW (le_trans inf_le_left inf_le_right)
  refine ⟨⟨V, hV⟩, hVU, hxV,
    ![X.presheaf.map (homOfLE hV₀).op s₀,
      X.presheaf.map (homOfLE hV₁).op s₁], ?_⟩
  intro i
  fin_cases i
  · exact (X.presheaf.germ_res_apply (homOfLE hV₀) x hxV s₀).trans hs₀
  · exact (X.presheaf.germ_res_apply (homOfLE hV₁) x hxV s₁).trans hs₁

end KltDP.Geometry

#check @KltDP.Geometry.exists_affine_pair_stalk_representatives
#print axioms KltDP.Geometry.exists_affine_pair_stalk_representatives
