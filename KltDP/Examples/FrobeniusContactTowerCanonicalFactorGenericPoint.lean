import KltDP.Examples.FrobeniusTowerFunctionField
import KltDP.Examples.FrobeniusExceptionalFinalConfiguration
import KltDP.Geometry.CartierDivisorPullback

/-!
# Generic points of all original between-stage projections

The original to-initial projection is an isomorphism over the original
nonempty puncture. The pinned open-immersion generic-point theorem therefore
proves its generic-point preservation. The accepted stage-restart isomorphism
then gives every actual between-stage projection, including projections from
the creation stage of an older exceptional divisor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorGenericPoint

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
open FrobeniusStageComplement.PlaneChartedScheme FrobeniusTowerFunctionField.PlaneChartedScheme

private theorem genericPoint_of_restrict_isIso {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (U : Y.Opens) [Nonempty U.toScheme]
    [IsIso (f ∣_ U)] : f.base (genericPoint X) = genericPoint Y := by
  let V := f ⁻¹ᵁ U
  letI : Nonempty V.toScheme :=
    ⟨(inv (f ∣_ U)).base (Classical.choice (inferInstance : Nonempty U.toScheme))⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  letI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  rw [← genericPoint_eq_of_isOpenImmersion V.ι,
    ← genericPoint_eq_of_isOpenImmersion U.ι,
    ← genericPoint_eq_of_isOpenImmersion (f ∣_ U)]
  have h := congrArg (fun t : V.toScheme ⟶ Y => t.base (genericPoint V.toScheme))
    (morphismRestrict_ι f U)
  simpa only [Scheme.comp_base_apply] using h.symm

variable {k : Type u} [Field k] (A : PlaneChartedScheme k) [IsIntegral A.carrier]

/-- The original projection to the initial stage preserves its actual generic point. -/
theorem toInitial_base_genericPoint (N : ℕ) :
    (A.toInitial N).base (genericPoint (A.stage N).carrier) = genericPoint A.carrier := by
  letI := toInitial_restrict_isIso A N
  exact genericPoint_of_restrict_isIso (A.toInitial N) (initialPuncture A)

/-- Every original projection between whole stages preserves the actual generic point. -/
theorem between_base_genericPoint (i N : ℕ) (h : i ≤ N) :
    (between A h).base (genericPoint (A.stage N).carrier) =
      genericPoint (A.stage i).carrier := by
  rw [← genericPoint_eq_of_isOpenImmersion (stageFinishIso A i N h).hom,
    ← Scheme.comp_base_apply, stageFinishIso_hom_between]
  exact toInitial_base_genericPoint (A.stage i) (N - i)

/-- The accepted Cartier pullback class now applies to every original between-stage projection. -/
theorem between_genericPointPreserving (i N : ℕ) (h : i ≤ N) :
    GenericPointPreserving (between A h) :=
  ⟨between_base_genericPoint A i N h⟩

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorGenericPoint
