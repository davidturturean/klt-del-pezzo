import KltDP.Examples.FrobeniusMultiCentreIntegral
import KltDP.Examples.FrobeniusMultiCentreExceptional
import KltDP.Examples.FrobeniusPreviousStrictIsoProjectiveLine

/-!
# The newest exceptional curves `P_i` of `S_{p,n}` as prime curves

Lane F realises the exceptional curves `E_{i,idx}` of the multi-centre surface `S_{p,n}` (with
`p = q + 1`) as closed subschemes `exceptionalCurveι q n a i idx : exceptionalCurve … ⟶ multiSurface (q+1) n a`,
and proves that the newest one `P_i = E_{i,p}` (index `Sum.inr PUnit.unit`) is integral and isomorphic to
`P¹` (`newestCurve_isIntegral`, `newestCurveIso`). Here `P_i` becomes an actual `PrimeCurve` of the surface
`multiSurfaceSurface (q+1) n a ha hproj` (`newestPrimeCurve`): its range is an irreducible closed subset of
dimension one. The second part does the same for every `E_{i,idx}`, the older curves `C_{ij}` being `P¹` by the
accepted `previousStrictIsoProjectiveLine` (`exceptionalPrimeCurveSPn`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreExceptionalPrime

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGlobalBlowupStages
open FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint FrobeniusMultiCentreSurface
open FrobeniusMultiCentreExceptional FrobeniusMultiCentreNormal FrobeniusMultiCentreIntegral

variable {k : Type u} [Field k] [IsAlgClosed k] (q n : ℕ) (a : Fin n → k)
  (ha : Function.Injective a) (i : Fin n)

include ha in
/-- `P_i` has dimension one (it is `P¹`). -/
theorem newestCurve_topologicalKrullDim :
    topologicalKrullDim (exceptionalCurve q n a i (Sum.inr PUnit.unit)) = 1 := by
  let e := newestCurveIso q n a ha i
  calc
    topologicalKrullDim (exceptionalCurve q n a i (Sum.inr PUnit.unit)) =
        topologicalKrullDim (projectiveSpace k 1) :=
      IsHomeomorph.topologicalKrullDim_eq e.schemeIsoToHomeo e.schemeIsoToHomeo.isHomeomorph
    _ = ((1 : ℕ) : WithBot ℕ∞) := projectiveSpace_topologicalKrullDim k 1
    _ = 1 := Nat.cast_one

include ha in
/-- The range of `P_i` in `S_{p,n}` is irreducible. -/
theorem range_newestCurveι_isIrreducible :
    IsIrreducible (Set.range (exceptionalCurveι q n a i (Sum.inr PUnit.unit)).base) := by
  letI := newestCurve_isIntegral q n a ha i
  have h := (IrreducibleSpace.isIrreducible_univ
    (exceptionalCurve q n a i (Sum.inr PUnit.unit))).image
    (exceptionalCurveι q n a i (Sum.inr PUnit.unit)).base
    (exceptionalCurveι q n a i (Sum.inr PUnit.unit)).continuous.continuousOn
  simpa only [Set.image_univ] using h

omit [IsAlgClosed k] in
/-- The range of `P_i` in `S_{p,n}` is closed. -/
theorem range_newestCurveι_isClosed :
    IsClosed (Set.range (exceptionalCurveι q n a i (Sum.inr PUnit.unit)).base) :=
  (exceptionalCurveι q n a i (Sum.inr PUnit.unit)).isClosedEmbedding.isClosed_range

include ha in
/-- The range of `P_i` in `S_{p,n}` has dimension one. -/
theorem range_newestCurveι_topologicalKrullDim :
    topologicalKrullDim (Set.range (exceptionalCurveι q n a i (Sum.inr PUnit.unit)).base) = 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _
    (exceptionalCurveι q n a i
      (Sum.inr PUnit.unit)).isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm.trans
    (newestCurve_topologicalKrullDim q n a ha i)

/-- **`P_i = E_{i,p}` as a prime curve of `S_{p,n}`** (`p = q + 1`). -/
def newestPrimeCurve (hproj : IsProjectiveOverField (multiStructure (q + 1) n a)) :
    (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve :=
  ⟨⟨Set.range (exceptionalCurveι q n a i (Sum.inr PUnit.unit)).base,
      range_newestCurveι_isIrreducible q n a ha i, range_newestCurveι_isClosed q n a i⟩,
    range_newestCurveι_topologicalKrullDim q n a ha i⟩

@[simp] theorem coe_newestPrimeCurve (hproj : IsProjectiveOverField (multiStructure (q + 1) n a)) :
    (newestPrimeCurve q n a ha i hproj :
      Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) =
      Set.range (exceptionalCurveι q n a i (Sum.inr PUnit.unit)).base := rfl

end KltDP.Examples.FrobeniusMultiCentreExceptionalPrime

/-! ## All exceptional curves `E_{i,idx}` of `S_{p,n}` as prime curves

The older curves `C_{ij}` (index `Sum.inl j`) are isomorphic to `P¹` by the accepted
`previousStrictIsoProjectiveLine` (the strict transform of an exceptional curve under the later
blowups is again `P¹`), through lane F's `exceptionalCurveIso`; so every `E_{i,idx}` is integral of
dimension one and gives a prime curve of `multiSurfaceSurface` (`exceptionalPrimeCurveSPn`). -/

namespace KltDP.Examples.FrobeniusMultiCentreExceptionalPrime

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGlobalBlowupStages
open FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint FrobeniusMultiCentreSurface
open FrobeniusMultiCentreExceptional FrobeniusMultiCentreNormal FrobeniusMultiCentreIntegral
open FrobeniusExceptionalFinalConfiguration FrobeniusPreviousStrictIsoProjectiveLine

variable {k : Type u} [Field k] [IsAlgClosed k] (q n : ℕ) (a : Fin n → k)
  (ha : Function.Injective a) (i : Fin n) (idx : FinalIndex.{0} q)

/-- Every exceptional curve `E_{i,idx}` of `S_{p,n}` is isomorphic to `P¹`. -/
def exceptionalCurveProjectiveLineIso : exceptionalCurve q n a i idx ≅ projectiveSpace k 1 :=
  match idx with
  | Sum.inl j =>
      exceptionalCurveIso q n a ha i (Sum.inl j) ≪≫
        previousStrictIsoProjectiveLine ((translatedInitial (q + 1) (a i)).stage j.val)
  | Sum.inr PUnit.unit => newestCurveIso q n a ha i

local instance sPnProjectiveLineIsIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

include ha in
theorem exceptionalCurve_nonempty : Nonempty (exceptionalCurve q n a i idx) :=
  ⟨(exceptionalCurveProjectiveLineIso q n a ha i idx).inv.base (projectiveSpace_nonempty k 1).some⟩

include ha in
/-- Every `E_{i,idx}` is integral. -/
theorem exceptionalCurve_isIntegral : IsIntegral (exceptionalCurve q n a i idx) := by
  letI := exceptionalCurve_nonempty q n a ha i idx
  exact isIntegral_of_isOpenImmersion (exceptionalCurveProjectiveLineIso q n a ha i idx).hom

include ha in
/-- Every `E_{i,idx}` has dimension one. -/
theorem exceptionalCurve_topologicalKrullDim :
    topologicalKrullDim (exceptionalCurve q n a i idx) = 1 := by
  let e := exceptionalCurveProjectiveLineIso q n a ha i idx
  calc
    topologicalKrullDim (exceptionalCurve q n a i idx) = topologicalKrullDim (projectiveSpace k 1) :=
      IsHomeomorph.topologicalKrullDim_eq e.schemeIsoToHomeo e.schemeIsoToHomeo.isHomeomorph
    _ = ((1 : ℕ) : WithBot ℕ∞) := projectiveSpace_topologicalKrullDim k 1
    _ = 1 := Nat.cast_one

include ha in
theorem range_exceptionalCurveι_isIrreducible :
    IsIrreducible (Set.range (exceptionalCurveι q n a i idx).base) := by
  letI := exceptionalCurve_isIntegral q n a ha i idx
  have h := (IrreducibleSpace.isIrreducible_univ (exceptionalCurve q n a i idx)).image
    (exceptionalCurveι q n a i idx).base (exceptionalCurveι q n a i idx).continuous.continuousOn
  simpa only [Set.image_univ] using h

omit [IsAlgClosed k] in
theorem range_exceptionalCurveι_isClosed :
    IsClosed (Set.range (exceptionalCurveι q n a i idx).base) :=
  (exceptionalCurveι q n a i idx).isClosedEmbedding.isClosed_range

include ha in
theorem range_exceptionalCurveι_topologicalKrullDim :
    topologicalKrullDim (Set.range (exceptionalCurveι q n a i idx).base) = 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _
    (exceptionalCurveι q n a i idx).isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm.trans
    (exceptionalCurve_topologicalKrullDim q n a ha i idx)

/-- **Every exceptional curve `E_{i,idx}` of `S_{p,n}` as a prime curve** of `multiSurfaceSurface`
(`p = q + 1`; `idx = Sum.inl j` is `C_{ij}`, `idx = Sum.inr ()` is `P_i`). -/
def exceptionalPrimeCurveSPn (hproj : IsProjectiveOverField (multiStructure (q + 1) n a)) :
    (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve :=
  ⟨⟨Set.range (exceptionalCurveι q n a i idx).base,
      range_exceptionalCurveι_isIrreducible q n a ha i idx, range_exceptionalCurveι_isClosed q n a i idx⟩,
    range_exceptionalCurveι_topologicalKrullDim q n a ha i idx⟩

@[simp] theorem coe_exceptionalPrimeCurveSPn (hproj : IsProjectiveOverField (multiStructure (q + 1) n a)) :
    (exceptionalPrimeCurveSPn q n a ha i idx hproj :
      Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) =
      Set.range (exceptionalCurveι q n a i idx).base := rfl

end KltDP.Examples.FrobeniusMultiCentreExceptionalPrime
