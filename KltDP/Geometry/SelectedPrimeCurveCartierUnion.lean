import KltDP.Geometry.CartierIdealSupport
import KltDP.Geometry.WeilClassPicard
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The Cartier subscheme of a finite selection of actual prime curves

The original finite set of prime curves defines the actual integral Weil
sum of their singleton divisors with coefficient one. Its coefficients,
effectivity, upper bound one, and geometric support are computed. The
existing Cartier-Weil equivalence supplies its actual Cartier inverse
image on the original locally factorial surface.

A literal equality to twice an element of the original integral Picard
group supplies an actual rank-one sheaf and an actual square isomorphism
to O(E). This uses the original Picard representative and equality in the
actual skeleton of module sheaves; no rational numerical class, supplied
square isomorphism, or desired subscheme is used as an input.

The preceding actual ideal and support theorems then give a reduced
Cartier subscheme isomorphic over the original surface to the reduced
closed subscheme of the literal selected finite union. The selected
curves may be arbitrary prime curves. Their being the manuscript's
isolated smooth nodes, the canonical-section/quadratic-atlas comparison,
and branch/cover smoothness are separate geometric obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open scoped BigOperators

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

local instance : DecidableEq X.PrimeCurve := Classical.decEq _

/-- The actual integral divisor formed from the selected original curves. -/
def selectedPrimeWeil (N : Finset X.PrimeCurve) : X.WeilDivisor :=
  ∑ C ∈ N, Finsupp.single C 1

/-- Each selected curve occurs exactly once; all other coefficients vanish. -/
theorem selectedPrimeWeil_apply (N : Finset X.PrimeCurve) (C : X.PrimeCurve) :
    X.selectedPrimeWeil N C = if C ∈ N then 1 else 0 := by
  classical
  simp only [selectedPrimeWeil, Finsupp.finset_sum_apply, Finsupp.single_apply,
    Finset.sum_ite_eq']

/-- The actual finite component set is precisely the original selection. -/
theorem selectedPrimeWeil_support (N : Finset X.PrimeCurve) :
    (X.selectedPrimeWeil N).support = N := by
  classical
  ext C
  rw [Finsupp.mem_support_iff, X.selectedPrimeWeil_apply]
  by_cases hC : C ∈ N <;> simp [hC]

theorem selectedPrimeWeil_effective (N : Finset X.PrimeCurve) :
    EffectiveDivisor (X.selectedPrimeWeil N) := by
  intro C
  rw [X.selectedPrimeWeil_apply]
  split_ifs <;> norm_num

theorem selectedPrimeWeil_le_one (N : Finset X.PrimeCurve) (C : X.PrimeCurve) :
    X.selectedPrimeWeil N C ≤ 1 := by
  rw [X.selectedPrimeWeil_apply]
  split_ifs <;> norm_num

/-- The literal finite union of the selected actual closed curves. -/
def selectedPrimeClosedUnion (N : Finset X.PrimeCurve) : Closeds X.toScheme :=
  ⟨⋃ C ∈ N, (C : Set X.toScheme), isClosed_biUnion_finset (fun C _ => C.isClosed)⟩

theorem selectedPrimeWeil_divisorSupport (N : Finset X.PrimeCurve) :
    divisorSupport (X.selectedPrimeWeil N) = (X.selectedPrimeClosedUnion N : Set X.toScheme) := by
  change (⋃ C ∈ (X.selectedPrimeWeil N).support, (C : Set X.toScheme)) = _
  rw [X.selectedPrimeWeil_support]
  rfl

/-- Nonempty selection gives an actual point of the original curve union. -/
theorem selectedPrimeClosedUnion_nonempty (N : Finset X.PrimeCurve) (hN : N.Nonempty) :
    (X.selectedPrimeClosedUnion N : Set X.toScheme).Nonempty := by
  obtain ⟨C, hC⟩ := hN
  obtain ⟨x, hx⟩ := C.nonempty
  refine ⟨x, ?_⟩
  change x ∈ ⋃ C ∈ N, (C : Set X.toScheme)
  exact Set.mem_iUnion.mpr ⟨C, Set.mem_iUnion.mpr ⟨hC, hx⟩⟩

variable [IsAlgClosed k] [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]

local instance : X.toScheme.IsSeparated := surfaceSeparated X

local instance : MonoidalCategory X.toScheme.Modules :=
  Scheme.Modules.monoidalCategory X.toScheme

/-- The actual Cartier inverse image of the original selected Weil sum. -/
def selectedPrimeCartier (N : Finset X.PrimeCurve) : CartierDivisor X.toScheme :=
  X.cartierWeilEquiv.symm (X.selectedPrimeWeil N)

theorem selectedPrimeCartier_weil (N : Finset X.PrimeCurve) :
    X.cartierToWeilHom (X.selectedPrimeCartier N) = X.selectedPrimeWeil N :=
  X.cartierWeilEquiv.apply_symm_apply (X.selectedPrimeWeil N)

theorem selectedPrimeCartier_effective (N : Finset X.PrimeCurve) :
    EffectiveDivisor (X.cartierToWeilHom (X.selectedPrimeCartier N)) := by
  rw [X.selectedPrimeCartier_weil]
  exact X.selectedPrimeWeil_effective N

theorem selectedPrimeCartier_le_one (N : Finset X.PrimeCurve) (C : X.PrimeCurve) :
    X.cartierToWeilHom (X.selectedPrimeCartier N) C ≤ 1 := by
  rw [X.selectedPrimeCartier_weil]
  exact X.selectedPrimeWeil_le_one N C

private theorem exists_squareRoot_of_picard_square
    (E : CartierDivisor X.toScheme) (p : X.toScheme.Pic)
    (hp : cartierPicardClass X.toScheme E = p ^ 2) :
    ∃ (L : InvertibleSheaf X.toScheme)
      (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X.toScheme E), L.toPic = p := by
  obtain ⟨M, hM, hclass⟩ := exists_invertible_representative_of_picard X.toScheme p
  have hpclass : (cartierPicardClass X.toScheme E : Skeleton X.toScheme.Modules) =
      ((p ^ 2 : X.toScheme.Pic) : Skeleton X.toScheme.Modules) :=
    congrArg (fun q : X.toScheme.Pic => (q : Skeleton X.toScheme.Modules)) hp
  rw [cartierPicardClass_val] at hpclass
  change toSkeleton (cartierDivisorModule X.toScheme E) =
    (p : Skeleton X.toScheme.Modules) ^ 2 at hpclass
  have htensor : toSkeleton (M ⊗ M) =
      toSkeleton (cartierDivisorModule X.toScheme E) := by
    rw [Skeleton.toSkeleton_tensorObj, hclass, ← pow_two]
    exact hpclass.symm
  obtain ⟨e⟩ := (show Nonempty (M ⊗ M ≅ cartierDivisorModule X.toScheme E) from
    Quotient.exact htensor)
  let L : InvertibleSheaf X.toScheme := ⟨M, hM⟩
  refine ⟨L, e, ?_⟩
  apply Units.ext
  change (L.toPic : Skeleton X.toScheme.Modules) = (p : Skeleton X.toScheme.Modules)
  rw [InvertibleSheaf.toPic_val]
  exact hclass

/-- Literal divisibility by two in the original integral Picard group
produces an actual square-root line bundle for the derived Cartier divisor. -/
theorem selectedPrimeCartier_squareRoot
    (N : Finset X.PrimeCurve) (m : Additive X.toScheme.Pic)
    (heven : X.weilClassPicardEquiv (X.weilClassMap (X.selectedPrimeWeil N)) =
      (2 : ℕ) • m) :
    ∃ (L : InvertibleSheaf X.toScheme)
      (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X.toScheme (X.selectedPrimeCartier N)),
      L.toPic = m.toMul := by
  apply exists_squareRoot_of_picard_square X (X.selectedPrimeCartier N) m.toMul
  have hclass : (X.weilClassPicardEquiv (X.weilClassMap (X.selectedPrimeWeil N))).toMul =
      m.toMul ^ 2 := by
    rw [heven, _root_.toMul_nsmul]
  exact (X.weilClassPicardEquiv_representative (X.selectedPrimeWeil N)).symm.trans hclass

/-- From the actual finite curve selection and its literal integral Picard
half-class, obtain the original reduced Cartier subscheme, its exact ideal
and image, and its isomorphism over the original surface to the selected union. -/
theorem selectedPrimeCurve_reducedUnion_of_even_picard
    (N : Finset X.PrimeCurve) (m : Additive X.toScheme.Pic)
    (heven : X.weilClassPicardEquiv (X.weilClassMap (X.selectedPrimeWeil N)) =
      (2 : ℕ) • m) :
    let E := X.selectedPrimeCartier N
    ∃ (L : InvertibleSheaf X.toScheme)
      (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X.toScheme E),
      L.toPic = m.toMul ∧
      let I := effectiveCartierIdealData X.toScheme E
        (X.hasRegularCartierEquations_of_effective_weil E (X.selectedPrimeCartier_effective N)) L e
      let J := Scheme.IdealSheafData.vanishingIdeal (X.selectedPrimeClosedUnion N)
      I = J ∧ AlgebraicGeometry.IsReduced I.glueData.glued ∧
        Set.range I.gluedTo.base = (X.selectedPrimeClosedUnion N : Set X.toScheme) ∧
        ∃ f : I.glueData.glued ≅ J.glueData.glued, f.hom ≫ J.gluedTo = I.gluedTo := by
  dsimp only
  obtain ⟨L, e, hL⟩ := X.selectedPrimeCartier_squareRoot N m heven
  let E := X.selectedPrimeCartier N
  have hE := X.selectedPrimeCartier_effective N
  have hE_one := X.selectedPrimeCartier_le_one N
  have hs : (⟨divisorSupport (X.cartierToWeilHom E), divisorSupport_isClosed _⟩ :
      Closeds X.toScheme) = X.selectedPrimeClosedUnion N := by
    apply SetLike.coe_injective
    change divisorSupport (X.cartierToWeilHom (X.selectedPrimeCartier N)) = _
    rw [X.selectedPrimeCartier_weil]
    exact X.selectedPrimeWeil_divisorSupport N
  have hI := X.effectiveCartierIdealData_eq_vanishingIdeal E hE hE_one L e
  dsimp only at hI
  rw [hs] at hI
  have hred := X.effectiveCartierSubscheme_isReduced E hE hE_one L e
  have hrange := X.effectiveCartierSubscheme_range E hE L e
  dsimp only at hrange
  rw [show X.cartierToWeilHom E = X.selectedPrimeWeil N from
    X.selectedPrimeCartier_weil N, X.selectedPrimeWeil_divisorSupport] at hrange
  have hiso := X.effectiveCartierSubscheme_iso_reducedWeilUnion E hE hE_one L e
  dsimp only at hiso
  rw [hs] at hiso
  exact ⟨L, e, hL, hI, hred, hrange, hiso⟩

end KltDP.Geometry.NormalProjectiveSurface
