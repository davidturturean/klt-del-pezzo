import KltDP.Geometry.CartierDivisorPullback
import KltDP.Examples.FrobeniusBlowdownGenericPoint

/-!
# Pullback of Cartier divisors along the blowdowns of the origin tower (BRIEF16, item 3, part 1)

The blowdowns `stepProjection n : stage (n+1) ⟶ stage n` and `projectiveContactProjection N :
stage N ⟶ stage 0` map generic points to generic points (`FrobeniusBlowdownGenericPoint`), so they
are `GenericPointPreserving` (instances `stepProjection_genericPointPreserving`,
`projectiveContactProjection_genericPointPreserving`, `between_genericPointPreserving`), and the
accepted `pullbackDivisor` applies: `blowdownPullbackDivisor n D hD : CartierDivisor (stage (n+1))`
for every effective Cartier divisor `D` on stage `n` with regular equations, and
`towerPullbackDivisor N D hD` from stage `0`.

**Not proved here** (the two remaining items of the accepted `CartierDivisorPullback` header): the
compatibility `cartierPicardHom (pullbackDivisor π D hD) = schemePicardPullbackHom π (cartierPicardHom D)`
and the additivity of `pullbackDivisor`; both need the base change of the zero scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.CartierDivisorPullbackBlowdown

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
open FrobeniusBlowdownGenericPoint

variable {k : Type u} [Field k]

/-- The base of the origin tower is integral (accepted), as a local instance. -/
local instance initial_isIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- The same accepted instance, stated on the projective product. -/
local instance product_isIntegral : IsIntegral (FrobeniusProjectivePoints.projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- Generic-point preservation is closed under composition. -/
theorem genericPointPreserving_comp {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [GenericPointPreserving f] [GenericPointPreserving g] :
    GenericPointPreserving (f ≫ g) :=
  ⟨by rw [Scheme.comp_base_apply, GenericPointPreserving.base_genericPoint,
    GenericPointPreserving.base_genericPoint]⟩

/-- Generic-point preservation of the identity. -/
theorem genericPointPreserving_id {X : Scheme.{u}} [IsIntegral X] :
    GenericPointPreserving (𝟙 X) := ⟨rfl⟩

/-- **`GenericPointPreserving (stepProjection n)`.** -/
instance stepProjection_genericPointPreserving (n : ℕ) :
    GenericPointPreserving ((projectiveProductInitial (k := k)).stepProjection n) :=
  ⟨stepProjection_base_genericPoint n⟩

/-- **`GenericPointPreserving (projectiveContactProjection N)`.** -/
instance projectiveContactProjection_genericPointPreserving (N : ℕ) :
    GenericPointPreserving (projectiveContactProjection (k := k) N) :=
  ⟨projectiveContactProjection_base_genericPoint N⟩

/-- **`GenericPointPreserving (between A h)`** for every pair of stages. -/
instance between_genericPointPreserving {i j : ℕ} (h : i ≤ j) :
    GenericPointPreserving (between (projectiveProductInitial (k := k)) h) := by
  induction j, h using Nat.le_induction with
  | base =>
    rw [between_refl]
    exact genericPointPreserving_id
  | succ j hij ih =>
    rw [between_succ (projectiveProductInitial (k := k)) hij]
    exact genericPointPreserving_comp _ _

/-- **The pullback along the step blowdown** of an effective Cartier divisor with regular
equations on stage `n` (the accepted `pullbackDivisor`). -/
abbrev blowdownPullbackDivisor (n : ℕ) (D : CartierDivisor (projectiveContactStage (k := k) n))
    (hD : HasRegularCartierEquations (projectiveContactStage (k := k) n) D) :
    CartierDivisor (projectiveContactStage (k := k) (n + 1)) :=
  pullbackDivisor ((projectiveProductInitial (k := k)).stepProjection n) D hD

/-- **The pullback from stage `0` to stage `N`.** -/
abbrev towerPullbackDivisor (N : ℕ) (D : CartierDivisor (projectiveContactStage (k := k) 0))
    (hD : HasRegularCartierEquations (projectiveContactStage (k := k) 0) D) :
    CartierDivisor (projectiveContactStage (k := k) N) :=
  pullbackDivisor (projectiveContactProjection (k := k) N) D hD

/-- The pulled-back divisor again has regular equations (accepted `pullbackDivisor_hasRegularEquations`),
so the pullbacks compose along the tower. -/
theorem blowdownPullbackDivisor_hasRegularEquations (n : ℕ)
    (D : CartierDivisor (projectiveContactStage (k := k) n))
    (hD : HasRegularCartierEquations (projectiveContactStage (k := k) n) D) :
    HasRegularCartierEquations (projectiveContactStage (k := k) (n + 1))
      (blowdownPullbackDivisor n D hD) :=
  pullbackDivisor_hasRegularEquations _ D hD

end KltDP.Examples.CartierDivisorPullbackBlowdown
