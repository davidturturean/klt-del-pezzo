import KltDP.Examples.FrobeniusTowerCartierIdentity
import KltDP.Examples.FrobeniusTowerTransport
import KltDP.Geometry.CartierDivisorPullbackAdd
import KltDP.Geometry.CartierDivisorPullbackComp

/-!
# The Cartier fibre identity transported to the translated contact towers

The Cartier divisors of the origin tower with regular equations — the total transform of the
fibre `y = 0` (`totalFiberDivisor`), the strict fibre `F̃` (`fiberStrictDivisor`), the older
exceptional curves `C_j` (`oldFinalDivisor`) and the newest exceptional curve `P`
(`stepExceptionalDivisor`) — are carried to the translated tower over `(a, a^p)` by the pullback
along the inverse of the stage isomorphism `stageTranslationIso p a N` (an isomorphism of integral
schemes preserves the generic point, so the accepted `pullbackDivisor` applies).  Since this
pullback is an additive homomorphism on the divisors with regular equations
(`CartierDivisorPullbackAdd.pullbackDivisorHom`), the Cartier identity
`π^*(y = 0) = F̃ + Σ_{j<N} (j+1)·C_j + (N+1)·P` (`f29_tower_fiber_relation`) holds between the
transported divisors on every stage `N+1` of the translated tower
(`translated_totalFiberDivisor_eq`).

The transported divisors are *defined* as pullbacks along the isomorphism.  By the functoriality
of the pullback (`CartierDivisorPullbackComp`), the transported total transform is the total
transform, along the translated tower's own blowdown `between (translatedInitial p a) _`, of the
fibre `y = a^p` — the image of `y = 0` under the translation
(`translatedTotalFiberDivisor_eq_intrinsic`, `translated_totalFiberDivisor'_eq`).  The
identification of `translatedFiberStrictDivisor` etc. with the Cartier divisors of the translated
tower's own curves (`cartierDivisorOfIdeal` of the translated kernels) is **not** treated here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusTowerTransportCartier

open KltDP.Geometry KltDP.Geometry.CartierDivisorPullbackAdd
  KltDP.Geometry.CartierDivisorPullbackComp
open FrobeniusGlobalBlowupStages FrobeniusFiberZeroClass FrobeniusExceptionalFinalConfiguration
  FrobeniusContactTowerSelectedPoint FrobeniusTranslatedCharts FrobeniusTowerTransport
  FrobeniusTowerFiberPullback FrobeniusTowerCartierIdentity FrobeniusFiberStrictCartier
  FrobeniusOldExceptionalLaterCartier FrobeniusExceptionalCartier
  FrobeniusGraphPicardClassIntegral FrobeniusProjectivePoints

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance towerTransportCartierInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isIntegral

local instance towerTransportCartierTranslatedIntegral (p : ℕ) (a : k) :
    IsIntegral (translatedInitial p a).carrier :=
  projectiveProduct_isIntegral

/-! ## The divisors of the origin tower as divisors with regular equations -/

/-- `π_N^*(y = 0)` with its regular equations. -/
def originTotalFiber (N : ℕ) : regularDivisors (projectiveContactStage (k := k) N) :=
  ⟨totalFiberDivisor N, totalFiberDivisor_hasRegularEquations N⟩

/-- `F̃` on stage `N` with its regular equations. -/
def originFiberStrict (N : ℕ) : regularDivisors (projectiveContactStage (k := k) N) :=
  ⟨fiberStrictDivisor N, fiberStrictDivisor_hasRegularEquations N⟩

/-- `C_j` on stage `N` with its regular equations. -/
def originOldFinal (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    regularDivisors (projectiveContactStage (k := k) N) :=
  ⟨oldFinalDivisor N j h, oldFinalDivisor_hasRegularEquations N j h⟩

/-- `P` on stage `N + 1` with its regular equations. -/
def originStepExceptional (N : ℕ) : regularDivisors (projectiveContactStage (k := k) (N + 1)) :=
  ⟨stepExceptionalDivisor N, stepExceptionalDivisor_hasRegularEquations N⟩

/-- The Cartier identity of the origin tower, in the submonoid of divisors with regular
equations. -/
theorem origin_identity (N : ℕ) :
    originTotalFiber (k := k) (N + 1) =
      originFiberStrict (N + 1) +
        ∑ j : Fin N, (j.val + 1) • originOldFinal (N + 1) j.val (by omega) +
        (N + 1) • originStepExceptional N := by
  apply Subtype.ext
  push_cast
  exact totalFiberDivisor_eq N

/-! ## Transport along the stage isomorphisms -/

/-- The transport of Cartier divisors with regular equations from stage `N` of the origin tower to
stage `N` of the translated tower: pullback along `(stageTranslationIso p a N).inv`. -/
abbrev transportDivisorHom (p : ℕ) (a : k) (N : ℕ) :
    regularDivisors (projectiveContactStage (k := k) N) →+ CartierDivisor (selectedStage p a N) :=
  pullbackDivisorHom (stageTranslationIso p a N).inv

/-- The total transform of the fibre on stage `N` of the translated tower (transported). -/
def translatedTotalFiberDivisor (p : ℕ) (a : k) (N : ℕ) : CartierDivisor (selectedStage p a N) :=
  transportDivisorHom p a N (originTotalFiber N)

/-- `F̃` on stage `N` of the translated tower (transported). -/
def translatedFiberStrictDivisor (p : ℕ) (a : k) (N : ℕ) : CartierDivisor (selectedStage p a N) :=
  transportDivisorHom p a N (originFiberStrict N)

/-- `C_j` on stage `N` of the translated tower (transported). -/
def translatedOldFinalDivisor (p : ℕ) (a : k) (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    CartierDivisor (selectedStage p a N) :=
  transportDivisorHom p a N (originOldFinal N j h)

/-- `P` on stage `N + 1` of the translated tower (transported). -/
def translatedStepExceptionalDivisor (p : ℕ) (a : k) (N : ℕ) :
    CartierDivisor (selectedStage p a (N + 1)) :=
  transportDivisorHom p a (N + 1) (originStepExceptional N)

theorem translatedTotalFiberDivisor_eq_pullback (p : ℕ) (a : k) (N : ℕ) :
    translatedTotalFiberDivisor p a N =
      pullbackDivisor (stageTranslationIso p a N).inv (totalFiberDivisor N)
        (totalFiberDivisor_hasRegularEquations N) := rfl

theorem translatedTotalFiberDivisor_hasRegularEquations (p : ℕ) (a : k) (N : ℕ) :
    HasRegularCartierEquations _ (translatedTotalFiberDivisor p a N) :=
  pullbackDivisor_hasRegularEquations (stageTranslationIso p a N).inv (totalFiberDivisor N)
    (totalFiberDivisor_hasRegularEquations N)

theorem translatedFiberStrictDivisor_hasRegularEquations (p : ℕ) (a : k) (N : ℕ) :
    HasRegularCartierEquations _ (translatedFiberStrictDivisor p a N) :=
  pullbackDivisor_hasRegularEquations (stageTranslationIso p a N).inv (fiberStrictDivisor N)
    (fiberStrictDivisor_hasRegularEquations N)

theorem translatedOldFinalDivisor_hasRegularEquations (p : ℕ) (a : k) (N j : ℕ)
    (h : j + 1 + 1 ≤ N) : HasRegularCartierEquations _ (translatedOldFinalDivisor p a N j h) :=
  pullbackDivisor_hasRegularEquations (stageTranslationIso p a N).inv (oldFinalDivisor N j h)
    (oldFinalDivisor_hasRegularEquations N j h)

theorem translatedStepExceptionalDivisor_hasRegularEquations (p : ℕ) (a : k) (N : ℕ) :
    HasRegularCartierEquations _ (translatedStepExceptionalDivisor p a N) :=
  pullbackDivisor_hasRegularEquations (stageTranslationIso p a (N + 1)).inv
    (stepExceptionalDivisor N) (stepExceptionalDivisor_hasRegularEquations N)

/-- **The Cartier fibre identity on stage `N+1` of the translated tower**, between the transported
divisors: `π^*(y = 0) = F̃ + Σ_{j<N} (j+1)·C_j + (N+1)·P`. -/
theorem translated_totalFiberDivisor_eq (p : ℕ) (a : k) (N : ℕ) :
    translatedTotalFiberDivisor p a (N + 1) =
      translatedFiberStrictDivisor p a (N + 1) +
        ∑ j : Fin N, (j.val + 1) • translatedOldFinalDivisor p a (N + 1) j.val (by omega) +
        (N + 1) • translatedStepExceptionalDivisor p a N := by
  unfold translatedTotalFiberDivisor translatedFiberStrictDivisor translatedOldFinalDivisor
    translatedStepExceptionalDivisor
  rw [origin_identity N, map_add, map_add, map_sum, map_nsmul]
  simp_rw [map_nsmul]

/-! ## The total transform of the translated fibre along the translated tower -/

/-- The fibre `y = a^p` of the plane of the translated tower: the image of the fibre `y = 0` under
the translation `τ_a × τ_{a^p}` (pullback along the inverse translation). -/
def translatedFiberZeroDivisor (p : ℕ) (a : k) : CartierDivisor (selectedStage p a 0) :=
  pullbackDivisor (stageTranslationIso p a 0).inv fiberZeroDivisor
    fiberZeroDivisor_hasRegularEquations

theorem between_translated_eq (p : ℕ) (a : k) (N : ℕ) :
    between (translatedInitial p a) (Nat.zero_le N) =
      (stageTranslationIso p a N).inv ≫
        between (projectiveProductInitial (k := k)) (Nat.zero_le N) ≫
          (stageTranslationIso p a 0).hom :=
  (Iso.eq_inv_comp _).mpr (stageTranslationIso_hom_between p a (Nat.zero_le N))

/-- The blowdown of the translated tower to its plane preserves the generic point. -/
instance translated_between_genericPointPreserving (p : ℕ) (a : k) (N : ℕ) :
    GenericPointPreserving (between (translatedInitial p a) (Nat.zero_le N)) := by
  have hN : (stageTranslationIso p a N).inv.base (genericPoint (selectedStage p a N)) =
      genericPoint (projectiveContactStage (k := k) N) :=
    (genericPointPreserving_of_isIso (stageTranslationIso p a N).inv).base_genericPoint
  have h0 : (stageTranslationIso p a 0).hom.base (genericPoint (projectiveContactStage (k := k) 0)) =
      genericPoint (selectedStage p a 0) :=
    (genericPointPreserving_of_isIso (stageTranslationIso p a 0).hom).base_genericPoint
  refine ⟨?_⟩
  rw [between_translated_eq p a N, Scheme.comp_base_apply, Scheme.comp_base_apply, hN,
    between_genericPoint N, h0]

/-- The total transform of the fibre `y = a^p` along the translated tower's own blowdown. -/
def translatedTotalFiberDivisor' (p : ℕ) (a : k) (N : ℕ) : CartierDivisor (selectedStage p a N) :=
  pullbackDivisor (between (translatedInitial p a) (Nat.zero_le N)) (translatedFiberZeroDivisor p a)
    (pullbackDivisor_hasRegularEquations _ _ _)

theorem translatedTotalFiberDivisor'_hasRegularEquations (p : ℕ) (a : k) (N : ℕ) :
    HasRegularCartierEquations _ (translatedTotalFiberDivisor' p a N) :=
  pullbackDivisor_hasRegularEquations (between (translatedInitial p a) (Nat.zero_le N))
    (translatedFiberZeroDivisor p a) (pullbackDivisor_hasRegularEquations _ _ _)

theorem inv_comp_between_eq (p : ℕ) (a : k) (N : ℕ) :
    (stageTranslationIso p a N).inv ≫ between (projectiveProductInitial (k := k)) (Nat.zero_le N) =
      between (translatedInitial p a) (Nat.zero_le N) ≫ (stageTranslationIso p a 0).inv := by
  rw [between_translated_eq p a N]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The transported total transform is the total transform of the translated fibre `y = a^p`
along the translated tower** (functoriality of the pullback). -/
theorem translatedTotalFiberDivisor_eq_intrinsic (p : ℕ) (a : k) (N : ℕ) :
    translatedTotalFiberDivisor p a N = translatedTotalFiberDivisor' p a N := by
  change pullbackDivisor (stageTranslationIso p a N).inv
      (pullbackDivisor (between (projectiveProductInitial (k := k)) (Nat.zero_le N)) fiberZeroDivisor
        fiberZeroDivisor_hasRegularEquations) (pullbackDivisor_hasRegularEquations _ _ _) =
    pullbackDivisor (between (translatedInitial p a) (Nat.zero_le N))
      (pullbackDivisor (stageTranslationIso p a 0).inv fiberZeroDivisor
        fiberZeroDivisor_hasRegularEquations) (pullbackDivisor_hasRegularEquations _ _ _)
  rw [← pullbackDivisor_comp, ← pullbackDivisor_comp]
  exact pullbackDivisor_congr_hom (inv_comp_between_eq p a N) _ _

/-- **The Cartier fibre identity on stage `N+1` of the translated tower for the total transform of
the translated fibre**: `π^*(y = a^p) = F̃ + Σ_{j<N} (j+1)·C_j + (N+1)·P`. -/
theorem translated_totalFiberDivisor'_eq (p : ℕ) (a : k) (N : ℕ) :
    translatedTotalFiberDivisor' p a (N + 1) =
      translatedFiberStrictDivisor p a (N + 1) +
        ∑ j : Fin N, (j.val + 1) • translatedOldFinalDivisor p a (N + 1) j.val (by omega) +
        (N + 1) • translatedStepExceptionalDivisor p a N := by
  rw [← translatedTotalFiberDivisor_eq_intrinsic, translated_totalFiberDivisor_eq]

/-- The bundle has exactly one universe parameter. -/
theorem translated_totalFiberDivisor_eq_universe_check (k : Type u) [Field k] (p : ℕ) (a : k) :
    True := by
  have _ := translated_totalFiberDivisor_eq.{u} p a
  have _ := translated_totalFiberDivisor'_eq.{u} p a
  trivial

end KltDP.Examples.FrobeniusTowerTransportCartier
