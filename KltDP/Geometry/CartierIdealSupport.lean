import KltDP.Geometry.CartierIdealReduced
import KltDP.Geometry.StalkCurveUnit

/-!
# The original Cartier subscheme and the actual Weil support

The coefficient germ of an original regular Cartier chart is a unit
exactly when the original Cartier-to-Weil coefficients vanish on every
actual curve through that point. This uses the existing curve-order
criterion for units of the actual factorial stalk and its canonical
embedding in the original function field.

The affine components of the original divisor ideal then identify its
support with `divisorSupport`: the existing finite union of actual closed
curves having nonzero Weil coefficient. Effectivity derives the regular
equation cover; no support identity is supplied. With coefficients at
most one, the previously proved radicality identifies the entire ideal
with the vanishing ideal of this original finite union. Equality of the
actual ideal data gives an isomorphism of their existing quotient-chart
gluings commuting with the original inclusions into the surface.

No node-specific coefficient formula, quadratic-atlas comparison, or
branch/cover smoothness follows here. Those geometric identifications
remain separate. Reuse: pinned ideal support/vanishing-ideal Galois
connection and actual basic opens; project curve orders, regular
Cartier equations, radicality, and original glued inclusions. No source
port or change to the gluing construction is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

local instance : X.toScheme.IsSeparated := surfaceSeparated X

local instance : MonoidalCategory X.toScheme.Modules :=
  Scheme.Modules.monoidalCategory X.toScheme

/-- The original coefficient germ is a unit exactly off all original
curves with nonzero Cartier-to-Weil coefficient through the point. -/
theorem regularCartierEquation_germ_isUnit_iff
    (E : CartierDivisor X.toScheme) (c : RegularCartierEquationChart X.toScheme E)
    (x : c.chart.openSet) [UniqueFactorizationMonoid (X.stalk x)] :
    IsUnit (X.toScheme.presheaf.germ c.chart.openSet x x.property c.coefficient) ↔
      ∀ C : X.PrimeCurve, (x : X.toScheme) ∈ C → X.cartierToWeilHom E C = 0 := by
  have ha : algebraMap (X.stalk x) X.toScheme.functionField
      (X.toScheme.presheaf.germ c.chart.openSet x x.property c.coefficient) =
      (c.chart.equation : X.toScheme.functionField) :=
    (ConcreteCategory.congr_hom (X.toScheme.presheaf.germ_stalkSpecializes x.property
      ((genericPoint_spec X.toScheme).specializes trivial)) c.coefficient).trans c.germ_eq
  constructor
  · rintro ⟨a, haeq⟩ C hxC
    have hu : Units.map (algebraMap (X.stalk x) X.toScheme.functionField) a =
        c.chart.equation := by
      apply Units.ext
      change algebraMap (X.stalk x) X.toScheme.functionField (a : X.stalk x) = _
      rw [haeq, ha]
    have hzero := (X.curve_orders_eq_zero_iff_stalk_unit x c.chart.equation).mpr ⟨a, hu⟩
    rw [X.cartierToWeilHom_apply_of_equation E C c.chart.openSet
      (C.genericPoint_mem_of_mem x hxC) c.chart.equation c.chart.represents]
    exact hzero C hxC
  · intro h
    have hzero (C : X.PrimeCurve) (hxC : (x : X.toScheme) ∈ C) :
        C.order c.chart.equation = 0 := by
      rw [← X.cartierToWeilHom_apply_of_equation E C c.chart.openSet
        (C.genericPoint_mem_of_mem x hxC) c.chart.equation c.chart.represents]
      exact h C hxC
    obtain ⟨a, hu⟩ := (X.curve_orders_eq_zero_iff_stalk_unit x c.chart.equation).mp hzero
    refine ⟨a, ?_⟩
    apply IsFractionRing.injective (X.stalk x) X.toScheme.functionField
    exact (congrArg (fun z : X.toScheme.functionFieldˣ =>
      (z : X.toScheme.functionField)) hu).trans ha.symm

/-- The actual divisor ideal has precisely the original finite union of
closed curves with nonzero Weil coefficient as its support. -/
theorem effectiveCartierIdealData_support
    [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]
    (E : CartierDivisor X.toScheme) (hE : EffectiveDivisor (X.cartierToWeilHom E))
    (L : InvertibleSheaf X.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X.toScheme E) :
    let hD := X.hasRegularCartierEquations_of_effective_weil E hE
    let I := effectiveCartierIdealData X.toScheme E hD L e
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
    (I := effectiveCartierIdealData X.toScheme E
      (X.hasRegularCartierEquations_of_effective_weil E hE) L e)
    (U := ⟨V, hV⟩) hxV).trans ?_
  have hideal : (effectiveCartierIdealData X.toScheme E
      (X.hasRegularCartierEquations_of_effective_weil E hE) L e).ideal ⟨V, hV⟩ =
      Ideal.span ({d.coefficient} : Set Γ(X.toScheme, V)) :=
    effectiveCartierIdealData_ideal_chart X.toScheme E
      (X.hasRegularCartierEquations_of_effective_weil E hE) L e d hV
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

/-- The original glued inclusion has the original finite curve union as
its image, retaining the actual gluing and actual map into the surface. -/
theorem effectiveCartierSubscheme_range
    [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]
    (E : CartierDivisor X.toScheme) (hE : EffectiveDivisor (X.cartierToWeilHom E))
    (L : InvertibleSheaf X.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X.toScheme E) :
    let hD := X.hasRegularCartierEquations_of_effective_weil E hE
    let I := effectiveCartierIdealData X.toScheme E hD L e
    Set.range I.gluedTo.base = divisorSupport (X.cartierToWeilHom E) := by
  dsimp only
  rw [Scheme.IdealSheafData.range_gluedTo]
  exact X.effectiveCartierIdealData_support E hE L e

/-- With original coefficients at most one, the entire original Cartier
ideal equals the vanishing ideal of that actual finite closed curve union. -/
theorem effectiveCartierIdealData_eq_vanishingIdeal
    [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]
    (E : CartierDivisor X.toScheme) (hE : EffectiveDivisor (X.cartierToWeilHom E))
    (hE_one : ∀ C, X.cartierToWeilHom E C ≤ 1) (L : InvertibleSheaf X.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X.toScheme E) :
    let hD := X.hasRegularCartierEquations_of_effective_weil E hE
    let I := effectiveCartierIdealData X.toScheme E hD L e
    I = Scheme.IdealSheafData.vanishingIdeal
      ⟨divisorSupport (X.cartierToWeilHom E), divisorSupport_isClosed _⟩ := by
  dsimp only
  let I := effectiveCartierIdealData X.toScheme E
    (X.hasRegularCartierEquations_of_effective_weil E hE) L e
  have hs : I.support =
      (⟨divisorSupport (X.cartierToWeilHom E), divisorSupport_isClosed _⟩ :
        Closeds X.toScheme) :=
    SetLike.coe_injective (X.effectiveCartierIdealData_support E hE L e)
  calc
    I = I.radical := (X.effectiveCartierIdealData_radical E hE hE_one L e).symm
    _ = Scheme.IdealSheafData.vanishingIdeal I.support :=
      Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = _ := congrArg Scheme.IdealSheafData.vanishingIdeal hs

private theorem gluedIso_over_of_eq {I J : X.toScheme.IdealSheafData} (h : I = J) :
    ∃ f : I.glueData.glued ≅ J.glueData.glued, f.hom ≫ J.gluedTo = I.gluedTo := by
  subst J
  exact ⟨Iso.refl _, Category.id_comp _⟩

/-- The original Cartier subscheme is isomorphic over the original surface
to the reduced closed subscheme of the original finite Weil-support union. -/
theorem effectiveCartierSubscheme_iso_reducedWeilUnion
    [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]
    (E : CartierDivisor X.toScheme) (hE : EffectiveDivisor (X.cartierToWeilHom E))
    (hE_one : ∀ C, X.cartierToWeilHom E C ≤ 1) (L : InvertibleSheaf X.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X.toScheme E) :
    let hD := X.hasRegularCartierEquations_of_effective_weil E hE
    let I := effectiveCartierIdealData X.toScheme E hD L e
    let J := Scheme.IdealSheafData.vanishingIdeal
      ⟨divisorSupport (X.cartierToWeilHom E), divisorSupport_isClosed _⟩
    ∃ f : I.glueData.glued ≅ J.glueData.glued, f.hom ≫ J.gluedTo = I.gluedTo := by
  dsimp only
  exact gluedIso_over_of_eq X (X.effectiveCartierIdealData_eq_vanishingIdeal E hE hE_one L e)

end KltDP.Geometry.NormalProjectiveSurface
