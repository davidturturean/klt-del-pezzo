import KltDP.Geometry.CartierIdealSupport
import KltDP.Geometry.EffectiveCartierIdeal

/-!
# Actual Cartier ideals and reduced supports without square-root data

The original regular-equation ideal construction needs only the effective
Cartier divisor. We reuse the proved stalk-unit criterion and radical
section-ideal theorem to identify its support and reduced scheme ideal.
No Picard divisibility or square-root line bundle enters this adapter.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
universe u
namespace KltDP.Geometry.NormalProjectiveSurface
attribute [local instance] Types.instFunLike Types.instConcreteCategory
variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
local instance : X.toScheme.IsSeparated := surfaceSeparated X

theorem regularCartierIdealData_support
    [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]
    (E : CartierDivisor X.toScheme) (hE : EffectiveDivisor (X.cartierToWeilHom E))
    :
    let hD := X.hasRegularCartierEquations_of_effective_weil E hE
    let I := effectiveCartierIdealDataOfRegularEquations X.toScheme E hD
    (I.support : Set X.toScheme) = divisorSupport (X.cartierToWeilHom E) := by
  classical
  dsimp only
  ext x
  obtain ⟨c, hxc⟩ := X.hasRegularCartierEquations_of_effective_weil E hE x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVc⟩ :=
    (isBasis_affine_open X.toScheme).exists_subset_of_mem_open hxc c.chart.openSet.2
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let d := RegularCartierEquationChart.restrict X.toScheme E c V hVc
  refine (Scheme.IdealSheafData.mem_support_iff_of_mem
    (I := effectiveCartierIdealDataOfRegularEquations X.toScheme E
      (X.hasRegularCartierEquations_of_effective_weil E hE))
    (U := ⟨V, hV⟩) hxV).trans ?_
  have hideal : (effectiveCartierIdealDataOfRegularEquations X.toScheme E
      (X.hasRegularCartierEquations_of_effective_weil E hE)).ideal ⟨V, hV⟩ =
      Ideal.span ({d.coefficient} : Set Γ(X.toScheme, V)) :=
    effectiveCartierIdealDataOfRegularEquations_ideal_chart X.toScheme E
      (X.hasRegularCartierEquations_of_effective_weil E hE) d hV
  rw [hideal, X.toScheme.zeroLocus_span, X.toScheme.zeroLocus_singleton]
  change (x ∉ X.toScheme.basicOpen d.coefficient) ↔
    x ∈ divisorSupport (X.cartierToWeilHom E)
  rw [X.toScheme.mem_basicOpen d.coefficient x hxV,
    X.regularCartierEquation_germ_isUnit_iff E d ⟨x, hxV⟩, mem_divisorSupport]
  constructor
  · intro h
    by_contra hn
    apply h
    intro C hxC
    by_contra hC
    exact hn ⟨C, hC, hxC⟩
  · rintro ⟨C, hC, hxC⟩ hz
    exact hC (hz C hxC)


/-- Weil coefficients at most one make the actual regular-equation ideal radical. -/
theorem regularCartierIdealData_radical
    [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]
    (E : CartierDivisor X.toScheme) (hE : EffectiveDivisor (X.cartierToWeilHom E))
    (hE_one : ∀ C, X.cartierToWeilHom E C ≤ 1) :
    let I := effectiveCartierIdealDataOfRegularEquations X.toScheme E
      (X.hasRegularCartierEquations_of_effective_weil E hE)
    I.radical = I := by
  dsimp only
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.radical_ideal,
    effectiveCartierIdealDataOfRegularEquations_ideal]
  exact (X.cartierSectionIdeal_isRadical E hE hE_one U.1).radical

/-- The radical of the actual divisor ideal is the vanishing ideal of its Weil support. -/
theorem regularCartierIdealData_radical_eq_vanishingIdeal
    [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]
    (E : CartierDivisor X.toScheme) (hE : EffectiveDivisor (X.cartierToWeilHom E)) :
    (effectiveCartierIdealDataOfRegularEquations X.toScheme E
      (X.hasRegularCartierEquations_of_effective_weil E hE)).radical =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨divisorSupport (X.cartierToWeilHom E), divisorSupport_isClosed _⟩ := by
  have hs : (effectiveCartierIdealDataOfRegularEquations X.toScheme E
      (X.hasRegularCartierEquations_of_effective_weil E hE)).support =
      (⟨divisorSupport (X.cartierToWeilHom E), divisorSupport_isClosed _⟩ :
        Closeds X.toScheme) :=
    SetLike.coe_injective (X.regularCartierIdealData_support E hE)
  rw [← Scheme.IdealSheafData.vanishingIdeal_support, hs]

/-- For a reduced Weil divisor the original ideal itself is that vanishing ideal. -/
theorem regularCartierIdealData_eq_vanishingIdeal
    [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]
    (E : CartierDivisor X.toScheme) (hE : EffectiveDivisor (X.cartierToWeilHom E))
    (hE_one : ∀ C, X.cartierToWeilHom E C ≤ 1) :
    effectiveCartierIdealDataOfRegularEquations X.toScheme E
      (X.hasRegularCartierEquations_of_effective_weil E hE) =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨divisorSupport (X.cartierToWeilHom E), divisorSupport_isClosed _⟩ := by
  rw [← X.regularCartierIdealData_radical E hE hE_one]
  exact X.regularCartierIdealData_radical_eq_vanishingIdeal E hE

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.regularCartierIdealData_eq_vanishingIdeal
