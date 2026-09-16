import KltDP.Examples.FrobeniusStageExceptionalSelfIntersection
import KltDP.Examples.FrobeniusExceptionalEulerUnconditional
import KltDP.Geometry.SchemeIsoEulerTransport
import KltDP.Geometry.SchemeInvertibleDualPullback
import KltDP.AdmissionProbe.CurveTensorDegreeConsumers

/-!
# `E·E = −1` on the contact-tower stages

The exceptional prime curve `E = exceptionalPrimeCurve n hproj` of the stage-`(n+1)` surface has
lane D's self-intersection number `−1`. The BRIEF8 reduction gave `E·E = −deg_E(conormal line)`
(`selfIntersectionNumber_eq_neg_conormal_degree`); this module computes `deg_E(conormal) = 1`.

Route. The prime-curve scheme of `E` is isomorphic over `k` to the accepted centre fibre
(`exceptionalLift`, an isomorphism with `exceptionalLift ≫ E.toSpec = globalExceptionalStructure`),
and the centre fibre is isomorphic over `k` to `P¹` (accepted `globalExceptionalProjectiveLineIso`,
`globalExceptionalProjectiveLineIso_hom_structure`). The Euler transport
`eulerCharacteristic_eq_pullback_inv` (this lane's `SchemeIsoEulerTransport`, built on the accepted
`SchemeIsoCohomology`) therefore identifies the Euler characteristics on `E` of the pulled-back
normal line and of `O_E` with the corresponding Euler characteristics on `P¹`, where the accepted
F09 input `f09_exceptional_euler_difference` gives the difference `−1`:
`deg_E(normal line) = −1` (`lineDegree_exceptionalNormalLine`). The pulled-back normal line is the
dual of the pulled-back conormal line (accepted `schemeModulePullbackDualIso`), so the accepted
evaluation isomorphism `L ⊗ L^∨ ≅ O` and the admitted 0AYX additivity
(`lineDegree_eq_add_of_tensorIso`) give `deg_E(conormal) + deg_E(normal) = 0`, hence
`deg_E(conormal) = 1` and **`E·E = −1`** (`selfIntersectionNumber_eq_neg_one`), exported as
`KltDP.Examples.f09_exceptional_self_intersection`.

Hypotheses: `k` algebraically closed and the projectivity hypothesis `hproj` of the stage surface;
nothing else.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusStageExceptionalSelfIntersectionValue

open KltDP.Geometry KltDP.Geometry.ModuleCohomology KltDP.Geometry.NormalProjectiveSurface
open FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalNormal FrobeniusGlobalExceptionalBase
open FrobeniusStrictTransformProductKernel FrobeniusStageSurface
open FrobeniusStageExceptionalPullback FrobeniusStageExceptionalSelfIntersection

variable {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- The centre fibre of the `(n+1)`-st blowup as an isomorphism onto the prime-curve scheme of
`E`. -/
abbrev exceptionalLiftIso :
    globalExceptionalScheme ((projectiveProductInitial (k := k)).stage n) ≅
      (exceptionalPrimeCurve n hproj).toScheme :=
  asIso (exceptionalLift n hproj)

/-- The isomorphism is over `k`: composed with the structure morphism of `E` it is the accepted
structure morphism of the centre fibre. -/
theorem exceptionalLiftIso_hom_structure :
    (exceptionalLiftIso n hproj).hom ≫ (exceptionalPrimeCurve n hproj).toSpec =
      globalExceptionalStructure ((projectiveProductInitial (k := k)).stage n) := by
  rw [PrimeCurve.toSpec, stageSurface_structureMorphism, asIso_hom, ← Category.assoc,
    exceptionalLift_inclusion]
  rfl

/-- Euler characteristics on `E` of modules pulled back from the centre fibre. -/
theorem eulerCharacteristic_exceptional_pullback
    (M : (globalExceptionalScheme ((projectiveProductInitial (k := k)).stage n)).Modules) :
    eulerCharacteristic (exceptionalPrimeCurve n hproj).toSpec
        ((schemeModulePullback (inv (exceptionalLift n hproj))).obj M) =
      eulerCharacteristic (globalExceptionalStructure ((projectiveProductInitial (k := k)).stage n))
        M :=
  (eulerCharacteristic_eq_pullback_inv (exceptionalLiftIso n hproj) _ _
    (exceptionalLiftIso_hom_structure n hproj) M).symm

/-- The same for invertible sheaves, in the `pullbackInvertibleSheaf` form. -/
theorem eulerCharacteristic_exceptional_pullbackLine
    (L : InvertibleSheaf (globalExceptionalScheme ((projectiveProductInitial (k := k)).stage n))) :
    eulerCharacteristic (exceptionalPrimeCurve n hproj).toSpec
        (pullbackInvertibleSheaf (inv (exceptionalLift n hproj)) L).obj =
      eulerCharacteristic (globalExceptionalStructure ((projectiveProductInitial (k := k)).stage n))
        L.obj :=
  eulerCharacteristic_exceptional_pullback n hproj L.obj

/-- `χ(O_E) = χ(O_{centre fibre})`. -/
theorem eulerCharacteristic_exceptional_unit :
    eulerCharacteristic (exceptionalPrimeCurve n hproj).toSpec
        (_root_.SheafOfModules.unit (exceptionalPrimeCurve n hproj).toScheme.ringCatSheaf) =
      eulerCharacteristic (globalExceptionalStructure ((projectiveProductInitial (k := k)).stage n))
        (_root_.SheafOfModules.unit
          (globalExceptionalScheme ((projectiveProductInitial (k := k)).stage n)).ringCatSheaf) :=
  (eulerCharacteristic_unit_eq (exceptionalLiftIso n hproj) _ _
    (exceptionalLiftIso_hom_structure n hproj)).symm

omit [IsAlgClosed k] in
/-- Euler characteristics on `P¹` of invertible sheaves pulled back from the centre fibre along the
accepted centre-fibre/`P¹` isomorphism. -/
theorem eulerCharacteristic_projectiveLine_pullbackLine
    (L : InvertibleSheaf (globalExceptionalScheme ((projectiveProductInitial (k := k)).stage n))) :
    eulerCharacteristic (projectiveSpaceToSpec k 1)
        (pullbackInvertibleSheaf
          (globalExceptionalProjectiveLineIso ((projectiveProductInitial (k := k)).stage n)).inv
          L).obj =
      eulerCharacteristic (globalExceptionalStructure ((projectiveProductInitial (k := k)).stage n))
        L.obj :=
  (eulerCharacteristic_eq_pullback_inv
    (globalExceptionalProjectiveLineIso ((projectiveProductInitial (k := k)).stage n)) _ _
    (globalExceptionalProjectiveLineIso_hom_structure
      ((projectiveProductInitial (k := k)).stage n)) L.obj).symm

omit [IsAlgClosed k] in
/-- `χ(O_{P¹}) = χ(O_{centre fibre})`. -/
theorem eulerCharacteristic_projectiveLine_unit :
    eulerCharacteristic (projectiveSpaceToSpec k 1)
        (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) =
      eulerCharacteristic (globalExceptionalStructure ((projectiveProductInitial (k := k)).stage n))
        (_root_.SheafOfModules.unit
          (globalExceptionalScheme ((projectiveProductInitial (k := k)).stage n)).ringCatSheaf) :=
  (eulerCharacteristic_unit_eq
    (globalExceptionalProjectiveLineIso ((projectiveProductInitial (k := k)).stage n)) _ _
    (globalExceptionalProjectiveLineIso_hom_structure
      ((projectiveProductInitial (k := k)).stage n))).symm

/-- The accepted normal line `O_X(E)|_E` of the centre fibre, transported to the prime-curve scheme
of `E`. -/
abbrev exceptionalNormalLine : InvertibleSheaf (exceptionalPrimeCurve n hproj).toScheme :=
  pullbackInvertibleSheaf (inv (exceptionalLift n hproj))
    (globalNormalLine ((projectiveProductInitial (k := k)).stage n))

/-- **`deg_E(normal line) = −1`**: the accepted F09 Euler difference on `P¹`, transported to `E`. -/
theorem lineDegree_exceptionalNormalLine :
    (exceptionalPrimeCurve n hproj).lineDegree (exceptionalNormalLine n hproj) = -1 := by
  unfold PrimeCurve.lineDegree
  rw [eulerCharacteristic_exceptional_pullbackLine n hproj, eulerCharacteristic_exceptional_unit,
    ← eulerCharacteristic_projectiveLine_pullbackLine n
      (globalNormalLine ((projectiveProductInitial (k := k)).stage n)),
    ← eulerCharacteristic_projectiveLine_unit n]
  exact f09_exceptional_euler_difference k ((projectiveProductInitial (k := k)).stage n)

/-- The transported normal line is the dual of the transported conormal line. -/
def exceptionalNormalDualIso :
    (exceptionalNormalLine n hproj).obj ≅ schemeDualSheaf (exceptionalConormalLine n hproj).obj :=
  schemeModulePullbackDualIso (inv (exceptionalLift n hproj))
    (globalConormalLine ((projectiveProductInitial (k := k)).stage n))

/-- `deg_E(conormal) + deg_E(normal) = 0` (evaluation `L ⊗ L^∨ ≅ O`, admitted 0AYX additivity). -/
theorem lineDegree_conormal_add_normal :
    (exceptionalPrimeCurve n hproj).lineDegree (exceptionalConormalLine n hproj) +
      (exceptionalPrimeCurve n hproj).lineDegree (exceptionalNormalLine n hproj) = 0 := by
  letI := Scheme.Modules.monoidalCategory (exceptionalPrimeCurve n hproj).toScheme
  have h := KltDP.AdmissionProbe.CurveTensorDegreeConsumers.lineDegree_eq_add_of_tensorIso
    (exceptionalPrimeCurve n hproj) (exceptionalConormalLine n hproj)
    (exceptionalNormalLine n hproj) (InvertibleSheaf.trivial _)
    ((schemeDualEvaluationIso (exceptionalConormalLine n hproj)).symm ≪≫
      whiskerLeftIso (exceptionalConormalLine n hproj).obj (exceptionalNormalDualIso n hproj).symm)
  rw [PrimeCurve.lineDegree_trivial] at h
  exact h.symm

/-- **`deg_E(conormal line) = 1`.** -/
theorem lineDegree_exceptionalConormalLine :
    (exceptionalPrimeCurve n hproj).lineDegree (exceptionalConormalLine n hproj) = 1 := by
  have h := lineDegree_conormal_add_normal n hproj
  rw [lineDegree_exceptionalNormalLine n hproj] at h
  omega

/-- **`E·E = −1`** in lane D's `selfIntersectionNumber`. -/
theorem selfIntersectionNumber_eq_neg_one :
    (exceptionalPrimeCurve n hproj).selfIntersectionNumber (stageRegular n hproj) = -1 := by
  rw [selfIntersectionNumber_eq_neg_conormal_degree n hproj,
    lineDegree_exceptionalConormalLine n hproj]

end KltDP.Examples.FrobeniusStageExceptionalSelfIntersectionValue

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStageSurface
  FrobeniusStageExceptionalSelfIntersection FrobeniusStageExceptionalSelfIntersectionValue

/-- **F09, self-intersection clause: `E·E = −1`** for the exceptional prime curve `E` of stage
`n+1` of the contact tower, in lane D's `selfIntersectionNumber` on the stage surface. Hypotheses:
`k` algebraically closed and a closed projective embedding `hproj` of the stage over `k`. -/
theorem f09_exceptional_self_intersection (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap) :
    (exceptionalPrimeCurve n hproj).selfIntersectionNumber (stageRegular n hproj) = -1 :=
  selfIntersectionNumber_eq_neg_one n hproj

/-- The statement has exactly one universe parameter. -/
theorem f09_exceptional_self_intersection_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap) :
    True := by
  have _ := f09_exceptional_self_intersection.{u} k n hproj
  trivial

end KltDP.Examples
