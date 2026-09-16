import KltDP.Geometry.EffectiveCartierIdeal
import KltDP.Geometry.PrimeCurveSubscheme
import KltDP.Geometry.RankIndexedCurveDegree
import KltDP.Geometry.ProperCurveEuler
import KltDP.AdmissionProbe.ProperCohomologyConsumers
import KltDP.Geometry.InvertibleCoherentModule
import KltDP.Geometry.FiniteTypeNoetherian
import KltDP.Compatibility.ConstantRankTensor

/-!
# The degree `deg(D) = dim_k Γ(D, O_D)` of an effective Cartier divisor (candidate 0AYY)

INACTIVE CANDIDATE TEXT. This module defines the right-hand side of Stacks
Lemma 33.44.9 (tag 0AYY) over existing objects and proves ordinary adapters.
It declares no literature input; the literal itself lives only in an
isolated probe outside `KltDP/`.

For an integral scheme `X` (the project's Cartier divisors are defined on
integral schemes) and a Cartier divisor `D` with regular local equations
(`HasRegularCartierEquations`), the actual closed subscheme `D ⊂ X` is the
quotient-chart gluing of the ideal data `O ∩ O(-D)` constructed without
square-root data in `EffectiveCartierIdeal` (laneA1), with the accepted glued
closed immersion. Over a field `k` with structure morphism `f : X → Spec k`:

* `effectiveCartierToSpec := i ≫ f` is proper (closed immersion ⇒ finite ⇒
  proper, composed with `f` proper);
* `effectiveCartierDegree := finrank_k H⁰(D, O_D)` is the published
  `dim_k Γ(D, O_D)` (the accepted `hZeroEquivGlobalSections` identifies
  `H⁰` with global sections additively);
* `effectiveCartierDegree_finiteDimensional`: `Γ(D, O_D)` is finite
  dimensional, from the accepted proper-cohomology consumer (Stacks 02O6
  literal) applied to the coherent structure sheaf of the proper scheme `D`;
* `effectiveCartierDegree_eq_zero_of_isEmpty`, `effectiveCartierScheme_isEmpty_of_eq_top`;
* `cartierTwist D E := E ⊗ O_X(D)` and its constant rank `n` from the proved
  product-basis theorem (rank `n * 1`).

Not proved here: finiteness of `D → Spec k` (part of the published lemma),
`deg(D)` of the zero divisor, additivity of `deg` over disjoint supports, and
the local-length formula; see the candidate README.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open scoped CategoryTheory.MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)
  (hD : HasRegularCartierEquations X D)

/-- The actual closed subscheme cut out by the effective Cartier divisor `D`:
the quotient-chart gluing of its original ideal data `O ∩ O(-D)`. -/
def effectiveCartierScheme : Scheme.{u} :=
  (effectiveCartierIdealDataOfRegularEquations X D hD).glueData.glued

/-- The original closed immersion `i : D → X`. -/
def effectiveCartierInclusion : effectiveCartierScheme X D hD ⟶ X :=
  (effectiveCartierIdealDataOfRegularEquations X D hD).gluedTo

instance effectiveCartierInclusion_isClosedImmersion :
    IsClosedImmersion (effectiveCartierInclusion X D hD) :=
  inferInstanceAs (IsClosedImmersion (effectiveCartierIdealDataOfRegularEquations X D hD).gluedTo)

/-- The image of `i` is the support of the original divisor ideal. -/
theorem range_effectiveCartierInclusion :
    Set.range (effectiveCartierInclusion X D hD).base =
      (effectiveCartierIdealDataOfRegularEquations X D hD).support :=
  Scheme.IdealSheafData.range_gluedTo _

/-- If the divisor ideal is the unit ideal, the subscheme is empty. -/
theorem effectiveCartierScheme_isEmpty_of_eq_top
    (h : effectiveCartierIdealDataOfRegularEquations X D hD = ⊤) :
    IsEmpty (effectiveCartierScheme X D hD) := by
  refine ⟨fun x => ?_⟩
  have hx : (effectiveCartierInclusion X D hD).base x ∈
      Set.range (effectiveCartierInclusion X D hD).base := ⟨x, rfl⟩
  rw [range_effectiveCartierInclusion, h, Scheme.IdealSheafData.support_top] at hx
  simp [TopologicalSpace.Closeds.coe_bot] at hx

section Base

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

/-- The structure morphism of the closed subscheme `D` over the base field. -/
def effectiveCartierToSpec : effectiveCartierScheme X D hD ⟶ Spec (CommRingCat.of k) :=
  effectiveCartierInclusion X D hD ≫ f

/-- A closed subscheme of a proper `k`-scheme is proper over `k`: closed
immersions are finite, finite morphisms are proper, and properness composes. -/
instance effectiveCartierToSpec_isProper [IsProper f] :
    IsProper (effectiveCartierToSpec X D hD f) := by
  unfold effectiveCartierToSpec
  infer_instance

/-- The published `deg(D) = dim_k Γ(D, O_D)`: the `k`-dimension (finrank) of
the zeroth cohomology of the structure sheaf of the actual subscheme `D`,
with the scalar action induced by `i ≫ f`. -/
def effectiveCartierDegree : ℕ :=
  cohomologyDimension (effectiveCartierToSpec X D hD f)
    (_root_.SheafOfModules.unit (effectiveCartierScheme X D hD).ringCatSheaf) 0

theorem effectiveCartierDegree_def :
    effectiveCartierDegree X D hD f =
      Module.finrank k ((baseFunctor (effectiveCartierToSpec X D hD f) 0).obj
        (_root_.SheafOfModules.unit (effectiveCartierScheme X D hD).ringCatSheaf)) := rfl

/-- `Γ(D, O_D)` is finite dimensional over `k`: the structure sheaf of the
proper scheme `D` is coherent (it is locally Noetherian, being of finite type
over a field), so the accepted proper-cohomology consumer applies. -/
theorem effectiveCartierDegree_finiteDimensional [IsProper f] :
    FiniteDimensional k ((baseFunctor (effectiveCartierToSpec X D hD f) 0).obj
      (_root_.SheafOfModules.unit (effectiveCartierScheme X D hD).ringCatSheaf)) := by
  letI : IsLocallyNoetherian (effectiveCartierScheme X D hD) :=
    isLocallyNoetherian_of_locallyOfFiniteType_toSpec (effectiveCartierToSpec X D hD f)
  letI : IsCoherentModule
      (_root_.SheafOfModules.unit (effectiveCartierScheme X D hD).ringCatSheaf) :=
    (InvertibleSheaf.trivial (effectiveCartierScheme X D hD)).isCoherent
  exact KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional
    (effectiveCartierToSpec X D hD f) _ 0

/-- The empty subscheme has degree zero (all its cohomology vanishes). -/
theorem effectiveCartierDegree_eq_zero_of_isEmpty [IsEmpty (effectiveCartierScheme X D hD)] :
    effectiveCartierDegree X D hD f = 0 := by
  haveI : Subsingleton
      (H (_root_.SheafOfModules.unit (effectiveCartierScheme X D hD).ringCatSheaf) 0) := by
    apply scheme_H_subsingleton_of_isEmpty
  exact cohomologyDimension_eq_zero_of_subsingleton _ _ _

end Base

section Twist

local instance effectiveCartierDegree_monoidalCategory : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The published `E(D) = E ⊗_{O_X} O_X(D)`, with the existing sheaf tensor
product and the constructed `O_X(D)`. -/
abbrev cartierTwist (E : X.Modules) : X.Modules := E ⊗ cartierDivisorModule X D

/-- `E(D)` has the constant rank `n` of `E`: the proved product-basis theorem
gives rank `n * 1` from the rank-one atlas of `O_X(D)`. -/
theorem isLocallyFreeOfRank_cartierTwist {E : X.Modules} {n : ℕ}
    (hE : KltDP.SheafOfModules.IsLocallyFreeOfRank (R := X.ringCatSheaf) E n) :
    KltDP.SheafOfModules.IsLocallyFreeOfRank (R := X.ringCatSheaf) (cartierTwist X D E) n := by
  have h := KltDP.SheafOfModules.IsLocallyFreeOfRank.tensor (X := X) hE
    (KltDP.SheafOfModules.IsInvertible.isLocallyFreeOfRank (cartierDivisorModule X D))
  simpa only [Nat.mul_one] using h

end Twist

end KltDP.Geometry
