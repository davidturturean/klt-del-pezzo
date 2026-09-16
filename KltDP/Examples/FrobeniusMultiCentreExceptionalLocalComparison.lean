import KltDP.Examples.FrobeniusMultiCentreExceptionalCartier
import KltDP.Geometry.CartierDivisorPullbackComp
import KltDP.Geometry.CartierOpenRestrictionEquations
import KltDP.Geometry.CartierPullbackKernelTransport
import KltDP.Examples.FrobeniusMultiCentreCurveKernels

/-!
# Exceptional Cartier divisors on their own cluster opens

The original global exceptional Cartier divisor restricts on its own
cluster to the pullback of the original translated final component.
This is equality of actual Cartier divisors under the original open
immersion, followed by equality with the original restricted kernel and
a comparison preserving its inclusion into the structure sheaf.

The cluster is nonempty by the accepted contact point and actual cluster
isomorphism. All required integrality and generic-point maps are produced.
Algebraic closure and distinct selected affine parameters are explicit;
primality, characteristic, projectivity and numerical conclusions are
not required. The weighted global graph identity is a later gluing step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreExceptionalLocalComparison

open KltDP.Geometry KltDP.Geometry.CartierDivisorPullbackComp
  KltDP.Geometry.CartierPullbackKernelTransport KltDP.Geometry.OpenImmersionRational
open FrobeniusGraphPicardClassIntegral FrobeniusTranslatedCharts
  FrobeniusContactTowerSelectedPoint FrobeniusExceptionalFinalConfiguration
  FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphNewest
  FrobeniusMultiCentreCurveKernels FrobeniusMultiCentreIntegral FrobeniusMultiCentreGenericPoint
  FrobeniusMultiCentreExceptionalCartier FrobeniusTranslatedExceptionalCartierKernels
  FrobeniusTowerTransportCartier

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance openGenericPointPreserving {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsOpenImmersion f] : GenericPointPreserving f :=
  ⟨genericPoint_eq_of_isOpenImmersion f⟩

/-- On an open immersion, the regular-equation pullback is the actual
Cartier cokernel restriction map. Both use the original generic stalk map. -/
theorem pullbackDivisor_eq_cartierRestriction {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsOpenImmersion f]
    (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D) :
    pullbackDivisor f D hD = cartierRestrictionHom f D := by
  have hfield : functionFieldMap f = (OpenImmersionRational.functionFieldIso f).hom := rfl
  apply cartierDivisor_eq_of_restrict_eq X
    (fun c : RegularCartierEquationChart Y D => f ⁻¹ᵁ c.chart.openSet)
    (pulled_cover f D hD)
  intro c
  rw [pullbackDivisor_restrict]
  simpa only [pulledEquation, hfield] using
    (cartierRestriction_globalEquation_preimage f D c.chart.openSet
      c.chart.equation c.chart.represents)

variable {k : Type u} [Field k]

local instance localComparisonInitialIntegral (p : ℕ) (a : k) :
    IsIntegral (translatedInitial p a).carrier := projectiveProduct_isIntegral

variable [IsAlgClosed k] (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  (i : Fin n)

include ha

/-- The original own-cluster open is integral. Its nonemptiness is
witnessed by the actual terminal contact point through the cluster isomorphism. -/
theorem ownCluster_isIntegral : IsIntegral (isoPreimage q n a i).toScheme := by
  letI : Nonempty (isoPreimage q n a i).toScheme :=
    ⟨(clusterIso q n a i).inv.base
      ⟨contactPoint q n a i, contactPoint_mem_isoOpen q n a ha i⟩⟩
  exact isIntegral_of_isOpenImmersion (isoMap q n a i)

/-- The original translated final-component divisor pulled to the own-cluster open. -/
def localExceptionalDivisor (idx : FinalIndex.{0} q) :
    letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
    CartierDivisor (isoPreimage q n a i).toScheme := by
  letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
  exact pullbackDivisor (isoMap q n a i)
    (translatedFinalCartier (q + 1) (a i) q idx)
    (translatedFinalCartier_hasRegularEquations (q + 1) (a i) q idx)

theorem localExceptionalDivisor_hasRegularEquations (idx : FinalIndex.{0} q) :
    letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
    HasRegularCartierEquations _ (localExceptionalDivisor q n a ha i idx) := by
  letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
  exact pullbackDivisor_hasRegularEquations _ _ _

/-- Pulling the actual global exceptional divisor to its own cluster
agrees with pulling the actual translated component along the cluster map. -/
theorem global_pullback_eq_local (idx : FinalIndex.{0} q) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
    pullbackDivisor (isoPreimage q n a i).ι (multiExceptionalDivisor q n a ha i idx)
        (multiExceptionalDivisor_hasRegularEquations q n a ha i idx) =
      localExceptionalDivisor q n a ha i idx := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
  letI : GenericPointPreserving (towerProjection (q + 1) n a i) :=
    towerProjection_genericPointPreserving q n a ha i
  exact (pullbackDivisor_comp (isoPreimage q n a i).ι (towerProjection (q + 1) n a i)
      (translatedFinalCartier (q + 1) (a i) q idx)
      (translatedFinalCartier_hasRegularEquations (q + 1) (a i) q idx)).symm.trans
    (pullbackDivisor_congr_hom (isoMap_eq q n a i).symm _ _)

/-- The actual Cartier restriction of the global exceptional divisor
is the local translated exceptional divisor. -/
theorem global_restriction_eq_local (idx : FinalIndex.{0} q) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
    cartierRestrictionHom (isoPreimage q n a i).ι (multiExceptionalDivisor q n a ha i idx) =
      localExceptionalDivisor q n a ha i idx := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
  rw [← pullbackDivisor_eq_cartierRestriction _ _
    (multiExceptionalDivisor_hasRegularEquations q n a ha i idx)]
  exact global_pullback_eq_local q n a ha i idx

/-- The local Cartier ideal is exactly the kernel of the original global
exceptional immersion restricted to the own-cluster open. -/
theorem localExceptionalDivisor_idealData (idx : FinalIndex.{0} q) :
    letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
    effectiveCartierIdealDataOfRegularEquations _ (localExceptionalDivisor q n a ha i idx)
        (localExceptionalDivisor_hasRegularEquations q n a ha i idx) =
      (exceptionalCurveι q n a i idx ∣_ isoPreimage q n a i).ker := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
  have h := pullbackIdealData_eq_kernel (isoPreimage q n a i).ι
    (multiExceptionalDivisor q n a ha i idx)
    (multiExceptionalDivisor_hasRegularEquations q n a ha i idx)
    (exceptionalCurveι q n a i idx)
    (exceptionalCurveι q n a i idx ∣_ isoPreimage q n a i)
    (exceptionalCurveι q n a i idx ⁻¹ᵁ isoPreimage q n a i).ι
    (isPullback_morphismRestrict (exceptionalCurveι q n a i idx) (isoPreimage q n a i))
    (multiExceptionalDivisor_idealData q n a ha i idx)
  simpa only [pullbackIdealData, global_pullback_eq_local q n a ha i idx] using h

/-- The negative local divisor module is the original restricted exceptional kernel. -/
def localExceptionalDivisor_kernelIso (idx : FinalIndex.{0} q) :
    letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
    cartierDivisorModule _ (-localExceptionalDivisor q n a ha i idx) ≅
      schemeKernelIdeal (exceptionalCurveι q n a i idx ∣_ isoPreimage q n a i) := by
  letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
  letI : IsClosedImmersion (exceptionalCurveι q n a i idx ∣_ isoPreimage q n a i) :=
    MorphismProperty.of_isPullback
      (isPullback_morphismRestrict (exceptionalCurveι q n a i idx) (isoPreimage q n a i)).flip
      inferInstance
  let I := effectiveCartierIdealDataOfRegularEquations _ (localExceptionalDivisor q n a ha i idx)
    (localExceptionalDivisor_hasRegularEquations q n a ha i idx)
  exact effectiveCartierKernelIso _ (localExceptionalDivisor q n a ha i idx)
      (localExceptionalDivisor_hasRegularEquations q n a ha i idx) ≪≫
    kernelIsoOfKerEq I.gluedTo (exceptionalCurveι q n a i idx ∣_ isoPreimage q n a i)
      (I.ker_gluedTo.trans (localExceptionalDivisor_idealData q n a ha i idx))

/-- The local comparison preserves the original kernel inclusion and
the normalized inclusion of the negative Cartier divisor. -/
theorem localExceptionalDivisor_kernelIso_inclusion (idx : FinalIndex.{0} q) :
    letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
    (localExceptionalDivisor_kernelIso q n a ha i idx).hom ≫
        schemeKernelIdealι (exceptionalCurveι q n a i idx ∣_ isoPreimage q n a i) =
      effectiveCartierNegativeInclusion _ (localExceptionalDivisor q n a ha i idx)
        (localExceptionalDivisor_hasRegularEquations q n a ha i idx) := by
  letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
  letI : IsClosedImmersion (exceptionalCurveι q n a i idx ∣_ isoPreimage q n a i) :=
    MorphismProperty.of_isPullback
      (isPullback_morphismRestrict (exceptionalCurveι q n a i idx) (isoPreimage q n a i)).flip
      inferInstance
  simp only [localExceptionalDivisor_kernelIso, Iso.trans_hom, Category.assoc, schemeKernelIdealι]
  rw [kernelIsoOfKerEq_hom_ι]
  exact effectiveCartierKernelIso_hom_ι _ _ _

/-- On its own cluster the global old component restricts to the
accepted translated old exceptional Cartier divisor. -/
theorem global_restriction_eq_old (j : Fin q) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
    cartierRestrictionHom (isoPreimage q n a i).ι
        (multiExceptionalDivisor q n a ha i (.inl j)) =
      pullbackDivisor (isoMap q n a i)
        (translatedOldFinalDivisor (q + 1) (a i) (q + 1) j.val (by omega))
        (translatedFinalCartier_hasRegularEquations (q + 1) (a i) q (.inl j)) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
  exact global_restriction_eq_local q n a ha i (.inl j)

/-- On its own cluster the global newest component restricts to the
accepted translated newest exceptional Cartier divisor. -/
theorem global_restriction_eq_newest :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
    cartierRestrictionHom (isoPreimage q n a i).ι
        (multiExceptionalDivisor q n a ha i (.inr PUnit.unit)) =
      pullbackDivisor (isoMap q n a i)
        (translatedStepExceptionalDivisor (q + 1) (a i) q)
        (translatedFinalCartier_hasRegularEquations (q + 1) (a i) q (.inr PUnit.unit)) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
  exact global_restriction_eq_local q n a ha i (.inr PUnit.unit)

end KltDP.Examples.FrobeniusMultiCentreExceptionalLocalComparison
