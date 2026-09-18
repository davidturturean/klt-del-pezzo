import KltDP.Geometry.EffectiveCartierOfInvertibleIdeal
import KltDP.Geometry.KernelIdealIsoTransport

/-!
The original ideal of an effective Cartier divisor is killed by an
actual morphism exactly when its original local coefficients are killed.
The argument uses the existing affine-ideal locality and sheaf separatedness.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u v

namespace KltDP.Geometry.CartierIdealKernelEquations

variable {X Z : Scheme.{u}} [IsIntegral X]
  (D : CartierDivisor X) (hD : HasRegularCartierEquations X D)
  (f : Z ⟶ X) [QuasiCompact f]

/-- Killing the original ideal kills every original equation coefficient,
including on a nonaffine equation neighborhood. -/
theorem coefficient_eq_zero_of_le_ker
    (h : effectiveCartierIdealDataOfRegularEquations X D hD ≤ f.ker)
    (c : RegularCartierEquationChart X D) :
    f.app c.chart.openSet c.coefficient = 0 := by
  refine Z.sheaf.eq_of_locally_eq'
    (fun W : {W : X.affineOpens // W.1 ≤ c.chart.openSet} => f ⁻¹ᵁ W.1.1)
    (f ⁻¹ᵁ c.chart.openSet) (fun W => homOfLE (fun _ hx => W.2 hx))
    ?_ (f.app c.chart.openSet c.coefficient) 0 ?_
  · intro z hz
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVU⟩ :=
      (isBasis_affine_open X).exists_subset_of_mem_open hz c.chart.openSet.2
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hzV⟩
  · intro W
    change Z.presheaf.map (homOfLE _).op (f.app c.chart.openSet c.coefficient) =
      Z.presheaf.map (homOfLE _).op 0
    rw [map_zero, Scheme.Hom.app_map_restrict]
    by_cases hne : Nonempty W.1.1
    · letI : Nonempty W.1.1 := hne
      have hm : X.presheaf.map (homOfLE W.2).op c.coefficient ∈
          (effectiveCartierIdealDataOfRegularEquations X D hD).ideal W.1 := by
        have hspan : (effectiveCartierIdealDataOfRegularEquations X D hD).ideal W.1 =
            Ideal.span {X.presheaf.map (homOfLE W.2).op c.coefficient} :=
          effectiveCartierIdealDataOfRegularEquations_ideal_chart X D hD
            (RegularCartierEquationChart.restrict X D c W.1.1 W.2) W.1.2
        rw [hspan]
        exact Ideal.subset_span (Set.mem_singleton _)
      have hk := h W.1 hm
      rwa [Scheme.Hom.ker_apply, RingHom.mem_ker] at hk
    · have he : W.1.1 = ⊥ := by
        apply Opens.ext
        exact Set.eq_empty_of_forall_not_mem (fun x hx => hne ⟨⟨x, hx⟩⟩)
      haveI : Subsingleton Γ(X, W.1.1) :=
        CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty he)
      rw [Subsingleton.elim (X.presheaf.map (homOfLE W.2).op c.coefficient) 0,
        map_zero]

/-- A covering family of the actual equation coefficients detects
factorization through the original Cartier zero scheme. -/
theorem le_ker_iff_coefficients_eq_zero {ι : Type v}
    (c : ι → RegularCartierEquationChart X D)
    (hcover : ∀ x : X, ∃ i, x ∈ (c i).chart.openSet) :
    effectiveCartierIdealDataOfRegularEquations X D hD ≤ f.ker ↔
      ∀ i, f.app (c i).chart.openSet (c i).coefficient = 0 := by
  constructor
  · intro h i
    exact coefficient_eq_zero_of_le_ker D hD f h (c i)
  · intro h
    apply inf_eq_left.mp
    apply IdealSheafData.ext_of_affine_cover _ _
      (fun i => (c i).chart.openSet) hcover
    intro i W hW
    apply IdealSheafData.ideal_eq_of_nonempty
    intro hne
    letI : Nonempty W.1 := hne
    change (effectiveCartierIdealDataOfRegularEquations X D hD).ideal W ⊓
      f.ker.ideal W = (effectiveCartierIdealDataOfRegularEquations X D hD).ideal W
    apply inf_eq_left.mpr
    have hspan : (effectiveCartierIdealDataOfRegularEquations X D hD).ideal W =
        Ideal.span {X.presheaf.map (homOfLE hW).op (c i).coefficient} :=
      effectiveCartierIdealDataOfRegularEquations_ideal_chart X D hD
        (RegularCartierEquationChart.restrict X D (c i) W.1 hW) W.2
    rw [hspan, Scheme.Hom.ker_apply, Ideal.span_le, Set.singleton_subset_iff]
    change f.app W.1 (X.presheaf.map (homOfLE hW).op (c i).coefficient) = 0
    rw [← Scheme.Hom.app_map_restrict f hW, h i, map_zero]

#check KltDP.Geometry.CartierIdealKernelEquations.le_ker_iff_coefficients_eq_zero
#print axioms KltDP.Geometry.CartierIdealKernelEquations.le_ker_iff_coefficients_eq_zero

end KltDP.Geometry.CartierIdealKernelEquations
