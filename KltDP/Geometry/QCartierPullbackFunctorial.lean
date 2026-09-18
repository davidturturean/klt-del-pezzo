import KltDP.Geometry.QCartierPullback

/-!
The original denominator-independent Q-Cartier pullback respects identity
and composition. Equality is checked on actual Cartier numerators, which
span the existing rational Cartier submodule by the proved positive-
multiple criterion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace KltDP.Geometry.QCartierPullback

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Actual Cartier numerators determine rational linear maps from the
existing rational Cartier space. -/
theorem linearMap_ext_on_cartier (X : NormalProjectiveSurface k)
    {V : Type v} [AddCommGroup V] [Module ℚ V]
    (F G : X.rationalCartierSubmodule →ₗ[ℚ] V)
    (h : ∀ A : CartierDivisor X.toScheme,
      F (X.rationalCartierMap A) = G (X.rationalCartierMap A)) : F = G := by
  apply LinearMap.ext
  intro D
  obtain ⟨n, hn, A, hA⟩ :=
    (X.qCartier_iff_exists_positive_multiple (D : X.RationalWeilDivisor)).mp D.property
  have hnum : X.rationalCartierMap A = n • D := Subtype.ext hA
  have heq : n • F D = n • G D := by
    simpa only [hnum, map_nsmul] using h A
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hscaled := congrArg (fun y : V => (n : ℚ)⁻¹ • y) heq
  simpa only [← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    inv_mul_cancel₀ hnq, one_smul] using hscaled

/-- The original identity morphism induces the identity rational map. -/
theorem pullbackLinearMap_id (X : NormalProjectiveSurface k) :
    pullbackLinearMap (𝟙 X.toScheme) = LinearMap.id := by
  apply linearMap_ext_on_cartier X
  intro A
  rw [pullbackLinearMap_cartier, DominantCartierPullback.pullbackHom_id]
  rfl

/-- Original composition induces the contravariant composite rational map. -/
theorem pullbackLinearMap_comp {X Y Z : NormalProjectiveSurface k}
    (f : X.toScheme ⟶ Y.toScheme) (g : Y.toScheme ⟶ Z.toScheme)
    [GenericPointPreserving f] [GenericPointPreserving g] :
    pullbackLinearMap (f ≫ g) =
      (pullbackLinearMap f).comp (pullbackLinearMap g) := by
  apply linearMap_ext_on_cartier Z
  intro A
  simp only [LinearMap.comp_apply, pullbackLinearMap_cartier]
  rw [DominantCartierPullback.pullbackHom_comp]
  rfl

/-- Identity pullback leaves the actual rational Weil divisor unchanged. -/
theorem pullback_id (X : NormalProjectiveSurface k)
    (D : X.RationalWeilDivisor) (hD : X.QCartier D) :
    pullback (𝟙 X.toScheme) D hD = D :=
  congrArg Subtype.val (LinearMap.congr_fun (pullbackLinearMap_id X) ⟨D, hD⟩)

/-- Pullback of actual Q-Cartier divisors respects the original composite
morphism, including the proved membership of the intermediate divisor. -/
theorem pullback_comp {X Y Z : NormalProjectiveSurface k}
    (f : X.toScheme ⟶ Y.toScheme) (g : Y.toScheme ⟶ Z.toScheme)
    [GenericPointPreserving f] [GenericPointPreserving g]
    (D : Z.RationalWeilDivisor) (hD : Z.QCartier D) :
    pullback (f ≫ g) D hD =
      pullback f (pullback g D hD) (pullback_qCartier g D hD) :=
  congrArg Subtype.val (LinearMap.congr_fun (pullbackLinearMap_comp f g) ⟨D, hD⟩)

end KltDP.Geometry.QCartierPullback
