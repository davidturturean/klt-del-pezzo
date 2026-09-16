import KltDP.Geometry.CartierPullbackKernelTransport
import KltDP.Examples.FrobeniusTowerGraphIdentity
import KltDP.Examples.FrobeniusTowerTransportCartier
import KltDP.Examples.FrobeniusTowerTransportCurves

/-!
# The actual strict graph and Cartier identity on a translated contact tower

The Cartier strict graph transported along the stage isomorphism has exactly
the kernel ideal of the translated tower's original graph closure. The origin
Cartier factorization therefore transports with its actual strict-graph term.

In characteristic `p`, for prime `p`, the graph divisor is invariant under the
inverse product translation. Functoriality identifies the transported total
graph with the pullback of the original graph along the translated tower's
own projection. At stage `N+1` for `p = m+(N+1)` this gives the intrinsic
Cartier graph identity with the accepted transported exceptional divisors.

This is one selected translated tower. Global factorization on `multiSurface`
still requires identification of all exceptional kernel ideals on the cluster
cover and compatibility with the original global total-graph divisor there.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusTranslatedGraphCartierIdentity

open KltDP.Geometry KltDP.Geometry.CartierDivisorPullbackAdd
  KltDP.Geometry.CartierDivisorPullbackComp
  KltDP.Geometry.CartierPullbackKernelTransport
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
  FrobeniusGraphPicardClassIntegral FrobeniusGraphZeroCartier
  FrobeniusGraphStrictCartier FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
  FrobeniusStrictTransformClosure FrobeniusContactTowerSelectedPoint FrobeniusTranslatedCharts
  FrobeniusTowerGraphPullback FrobeniusTowerGraphIdentity FrobeniusExceptionalFinalConfiguration
  FrobeniusTowerTransport FrobeniusTowerTransportCurves FrobeniusTowerTransportCartier
  ProjectiveProductTranslation
open KltDP.Geometry.ProjectiveLineTranslation

variable {k : Type u} [Field k]

local instance translatedGraphProductIntegral :
    IsIntegral (projectiveProduct k) := projectiveProduct_isIntegral

local instance translatedGraphOriginIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier := projectiveProduct_isIntegral

local instance translatedGraphInitialIntegral (p : ℕ) (a : k) :
    IsIntegral (translatedInitial p a).carrier := projectiveProduct_isIntegral

/-- The origin total graph with its accepted regular equations. -/
def originTotalGraph (N p : ℕ) : regularDivisors (projectiveContactStage (k := k) N) :=
  ⟨totalGraphDivisor N p, totalGraphDivisor_hasRegularEquations N p⟩

/-- The origin strict graph with its accepted regular equations. -/
def originStrictGraph (N m : ℕ) : regularDivisors (projectiveContactStage (k := k) N) :=
  ⟨graphStrictDivisor N m, graphStrictDivisor_hasRegularEquations N m⟩

/-- Transport of the total graph divisor to the selected translated tower. -/
def translatedGraphTotalDivisor (p : ℕ) (a : k) (N : ℕ) :
    CartierDivisor (selectedStage p a N) :=
  transportDivisorHom p a N (originTotalGraph N p)

/-- Transport of the strict graph divisor to the selected translated tower. -/
def translatedGraphStrictDivisor (p : ℕ) (a : k) (N m : ℕ) :
    CartierDivisor (selectedStage p a N) :=
  transportDivisorHom p a N (originStrictGraph N m)

theorem translatedGraphTotalDivisor_hasRegularEquations (p : ℕ) (a : k) (N : ℕ) :
    HasRegularCartierEquations _ (translatedGraphTotalDivisor p a N) :=
  pullbackDivisor_hasRegularEquations (stageTranslationIso p a N).inv
    (totalGraphDivisor N p) (totalGraphDivisor_hasRegularEquations N p)

theorem translatedGraphStrictDivisor_hasRegularEquations (p : ℕ) (a : k) (N m : ℕ) :
    HasRegularCartierEquations _ (translatedGraphStrictDivisor p a N m) :=
  pullbackDivisor_hasRegularEquations (stageTranslationIso p a N).inv
    (graphStrictDivisor N m) (graphStrictDivisor_hasRegularEquations N m)

/-- The transported strict graph has the kernel of the translated tower's
actual graph closure, as ideal data with its original inclusion. -/
theorem translatedGraphStrictDivisor_idealData (p : ℕ) (a : k) (N m : ℕ) :
    effectiveCartierIdealDataOfRegularEquations _ (translatedGraphStrictDivisor p a N m)
        (translatedGraphStrictDivisor_hasRegularEquations p a N m) =
      (closureInclusion (translatedInitial p a) N m).ker := by
  have sq : closureInclusion (translatedInitial p a) N m ≫ (stageTranslationIso p a N).inv =
      (graphClosureTranslationIso p a N m).inv ≫
        closureInclusion (projectiveProductInitial (k := k)) N m := by
    apply (cancel_mono (stageTranslationIso p a N).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← graphClosureTranslationIso_hom, Iso.inv_hom_id_assoc]
  have hI : effectiveCartierIdealDataOfRegularEquations _ (graphStrictDivisor (k := k) N m)
        (graphStrictDivisor_hasRegularEquations N m) =
      (closureInclusion (projectiveProductInitial (k := k)) N m).ker := by
    rw [graphStrictDivisor_idealData, strictTransformIdeal_eq_local]
    exact (liftedGraphClosureIdeal (projectiveProductInitial (k := k)) N m).ker_gluedTo.symm
  exact pullbackIdealData_eq_kernel_of_iso (stageTranslationIso p a N).symm
    (graphStrictDivisor N m) (graphStrictDivisor_hasRegularEquations N m)
    (closureInclusion (projectiveProductInitial (k := k)) N m)
    (closureInclusion (translatedInitial p a) N m)
    (graphClosureTranslationIso p a N m).symm sq hI

/-- The translated strict graph's original kernel has regular principal
generators, supplied by the actual transported Cartier divisor. -/
theorem translatedGraphKernel_locallyPrincipalRegular (p : ℕ) (a : k) (N m : ℕ) :
    IdealLocallyPrincipalRegular (closureInclusion (translatedInitial p a) N m).ker := by
  rw [← translatedGraphStrictDivisor_idealData p a N m]
  exact effectiveCartierIdealDataOfRegularEquations_regular _ _ _

/-- The transported divisor is the effective Cartier divisor constructed
from the actual translated graph kernel. -/
theorem translatedGraphStrictDivisor_eq_ofKernel (p : ℕ) (a : k) (N m : ℕ) :
    translatedGraphStrictDivisor p a N m =
      cartierDivisorOfIdeal _ (closureInclusion (translatedInitial p a) N m).ker
        (translatedGraphKernel_locallyPrincipalRegular p a N m) :=
  eq_cartierDivisorOfIdeal _ _ (translatedGraphKernel_locallyPrincipalRegular p a N m)
    (translatedGraphStrictDivisor p a N m)
    (translatedGraphStrictDivisor_hasRegularEquations p a N m)
    (translatedGraphStrictDivisor_idealData p a N m)

/-- The accepted origin identity in the additive submonoid of divisors
with regular equations. -/
theorem originGraph_identity (N m : ℕ) :
    originTotalGraph (k := k) (N + 1) (m + (N + 1)) =
      originStrictGraph (N + 1) m +
        ∑ j : Fin N, (j.val + 1) • originOldFinal (N + 1) j.val (by omega) +
        (N + 1) • originStepExceptional N := by
  apply Subtype.ext
  push_cast
  exact totalGraphDivisor_eq N m

/-- Transport of the origin Cartier identity, whose strict term is now
identified with the translated tower's actual graph kernel. -/
theorem translatedGraphTotalDivisor_eq (N m : ℕ) (a : k) :
    translatedGraphTotalDivisor (m + (N + 1)) a (N + 1) =
      translatedGraphStrictDivisor (m + (N + 1)) a (N + 1) m +
        ∑ j : Fin N, (j.val + 1) •
          translatedOldFinalDivisor (m + (N + 1)) a (N + 1) j.val (by omega) +
        (N + 1) • translatedStepExceptionalDivisor (m + (N + 1)) a N := by
  unfold translatedGraphTotalDivisor translatedGraphStrictDivisor
    translatedOldFinalDivisor translatedStepExceptionalDivisor
  rw [originGraph_identity N m, map_add, map_add, map_sum, map_nsmul]
  simp_rw [map_nsmul]

section Frobenius

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The original parametrized graph commutes with the actual product and
parameter translations. -/
theorem projectiveGraph_translation (a : k) :
    projectiveGraphMorphism p ≫ productTranslation a (a ^ p) =
      projectiveTranslation a ≫ projectiveGraphMorphism p := by
  apply pullback.hom_ext
  · rw [Category.assoc, productTranslation_fst, ← Category.assoc, projectiveGraphMorphism_fst,
      Category.id_comp, Category.assoc, projectiveGraphMorphism_fst, Category.comp_id]
  · rw [Category.assoc, productTranslation_snd, ← Category.assoc, projectiveGraphMorphism_snd,
      Category.assoc, projectiveGraphMorphism_snd]
    exact (projectiveTranslation_power p a).symm

/-- Inverse translation preserves the actual Cartier graph divisor,
proved from its original kernel and the actual commuting isomorphisms. -/
theorem graphZeroDivisor_pullback_inverse_translation (a : k) :
    pullbackDivisor (stageTranslationIso p a 0).inv (graphZeroDivisor p)
        (graphZeroDivisor_hasRegularEquations p) = graphZeroDivisor p := by
  have sq : projectiveGraphMorphism p ≫ (stageTranslationIso p a 0).inv =
      (projectiveTranslationIso a).inv ≫ projectiveGraphMorphism (k := k) p := by
    apply (cancel_mono (stageTranslationIso p a 0).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [stageTranslationIso_zero_hom, projectiveGraph_translation]
    exact (Iso.inv_hom_id_assoc (projectiveTranslationIso a) _).symm
  have hI := pullbackIdealData_eq_kernel_of_iso (stageTranslationIso p a 0).symm
    (graphZeroDivisor p) (graphZeroDivisor_hasRegularEquations p)
    (projectiveGraphMorphism (k := k) p) (projectiveGraphMorphism (k := k) p)
    (projectiveTranslationIso a).symm sq (graphZeroDivisor_idealData p)
  apply cartierDivisor_eq_of_idealData (projectiveProduct k) _ _
    (pullbackDivisor_hasRegularEquations _ _ _) (graphZeroDivisor_hasRegularEquations p)
  exact hI.trans (graphZeroDivisor_idealData p).symm

/-- The transported total graph is the pullback of the original graph
along the translated tower's own composite blowdown. -/
theorem translatedGraphTotalDivisor_eq_intrinsic (a : k) (N : ℕ) :
    translatedGraphTotalDivisor p a N =
      pullbackDivisor (between (translatedInitial p a) (Nat.zero_le N))
        (graphZeroDivisor p) (graphZeroDivisor_hasRegularEquations p) := by
  change pullbackDivisor (stageTranslationIso p a N).inv
      (pullbackDivisor (between (projectiveProductInitial (k := k)) (Nat.zero_le N))
        (graphZeroDivisor p) (graphZeroDivisor_hasRegularEquations p))
      (pullbackDivisor_hasRegularEquations _ _ _) = _
  rw [← pullbackDivisor_comp]
  calc
    _ = pullbackDivisor (between (translatedInitial p a) (Nat.zero_le N) ≫
        (stageTranslationIso p a 0).inv) (graphZeroDivisor p)
        (graphZeroDivisor_hasRegularEquations p) :=
      pullbackDivisor_congr_hom (inv_comp_between_eq p a N) _ _
    _ = _ := by
      rw [pullbackDivisor_comp]
      have h : (⟨pullbackDivisor (stageTranslationIso p a 0).inv (graphZeroDivisor p)
            (graphZeroDivisor_hasRegularEquations p),
          pullbackDivisor_hasRegularEquations _ _ _⟩ : regularDivisors (projectiveProduct k)) =
          ⟨graphZeroDivisor p, graphZeroDivisor_hasRegularEquations p⟩ :=
        Subtype.ext (graphZeroDivisor_pullback_inverse_translation p a)
      exact congrArg (pullbackDivisorHom
        (between (translatedInitial p a) (Nat.zero_le N))) h

end Frobenius

/-- The intrinsic Cartier identity on the selected tower, using its own
projection and the original Frobenius graph. -/
theorem translatedGraphIntrinsic_identity (N m : ℕ) (a : k)
    [Fact (m + (N + 1)).Prime] [CharP k (m + (N + 1))] :
    pullbackDivisor (between (translatedInitial (m + (N + 1)) a) (Nat.zero_le (N + 1)))
        (graphZeroDivisor (m + (N + 1))) (graphZeroDivisor_hasRegularEquations (m + (N + 1))) =
      translatedGraphStrictDivisor (m + (N + 1)) a (N + 1) m +
        ∑ j : Fin N, (j.val + 1) •
          translatedOldFinalDivisor (m + (N + 1)) a (N + 1) j.val (by omega) +
        (N + 1) • translatedStepExceptionalDivisor (m + (N + 1)) a N := by
  rw [← translatedGraphTotalDivisor_eq_intrinsic, translatedGraphTotalDivisor_eq]

end KltDP.Examples.FrobeniusTranslatedGraphCartierIdentity
