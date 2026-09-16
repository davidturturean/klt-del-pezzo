import KltDP.Examples.FrobeniusGlobalBlowupSmooth
import KltDP.Examples.FrobeniusGraphPicardClassCharts
import KltDP.Examples.FrobeniusMultiCentreSurface
import KltDP.Geometry.AffineBlowupCover
import KltDP.Examples.FrobeniusExceptionalChainPicard

/-!
# The tower stages are Noetherian and of finite type over `k`

BRIEF20, task 1. Every stage `(A.stage n).carrier` of a charted plane `A` whose carrier is a
Noetherian space, locally Noetherian, and proper over `k`, is again a Noetherian space, locally
Noetherian, and of finite type over `k`; in particular every stage `projectiveContactStage k n`
of the Frobenius contact tower (base `P¹ × P¹`, four polynomial charts). This discharges the three
instance hypotheses `[NoetherianSpace (chainStage q A)]`, `[IsLocallyNoetherian (chainStage q A)]`,
`[LocallyOfFiniteType (A.stage (q + 1)).structureMap]` of BRIEF19's `chain_rationalTreePicard`
(`chain_rationalTreePicard_of_tower`, `chainPicardEquivFin_of_tower`, and the contact-tower forms).

The Noetherian properties are proved chart by chart, following lane A2's `FrobeniusStageNormal`
pattern: a scheme covered by the images of open immersions from (locally) Noetherian schemes is
(locally) Noetherian (`isLocallyNoetherian_of_charts` through Mathlib's
`isLocallyNoetherian_iff_openCover`; `noetherianSpace_of_charts` through
`NoetherianSpace.iUnion`/`NoetherianSpace.range`). The polynomial plane `k[u][v]` is Noetherian
(Hilbert), the two Rees charts of the blowup of the plane at the origin are polynomial planes
(accepted `chartPolynomialEquiv`, `vChartPolynomialEquiv`), and the affine Rees blowup is covered by
them (accepted `generatingAffineCover`, `span_centerGenerator`); each global stage is glued from the
affine Rees blowup and the puncture of the previous stage (accepted `PointBlowupGluing.pieces_cover`),
and an open subscheme of a (locally) Noetherian scheme is (locally) Noetherian. Finite type is
immediate: the stage structure morphisms are proper (accepted `stageStructure_isProper`), and proper
morphisms are locally of finite type.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace KltDP.Examples.FrobeniusStageNoetherianFiniteType

open KltDP.Geometry KltDP.Geometry.AffineBlowup KltDP.Geometry.RationalTreePicard
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusProjectivePoints FrobeniusGraphPicardClassCharts FrobeniusGlobalBlowupStages
open FrobeniusMultiCentreSurface

variable {k : Type u} [Field k]

/-! ## Noetherian properties from a cover by open immersions -/

section Charts

variable {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u}) (g : ∀ i, Y i ⟶ X)
  [∀ i, IsOpenImmersion (g i)]
  (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), (g i).base y = x)

/-- The open cover given by a family of open immersions with jointly surjective images. -/
def openCoverOfCharts : Scheme.OpenCover.{v} X where
  J := ι
  obj := Y
  map := g
  f x := (hcover x).choose
  covers x := (hcover x).choose_spec
  map_prop _ := inferInstance

include g hcover in
/-- A scheme covered by open immersions from locally Noetherian schemes is locally Noetherian. -/
theorem isLocallyNoetherian_of_charts (hnoeth : ∀ i, IsLocallyNoetherian (Y i)) :
    IsLocallyNoetherian X :=
  (isLocallyNoetherian_iff_openCover (openCoverOfCharts Y g hcover)).mpr hnoeth

include g hcover in
omit [∀ i, IsOpenImmersion (g i)] in
/-- A scheme covered by finitely many open immersions from Noetherian spaces is a Noetherian
space. -/
theorem noetherianSpace_of_charts [Finite ι] (hnoeth : ∀ i, NoetherianSpace (Y i)) :
    NoetherianSpace X := by
  apply TopologicalSpace.noetherian_univ_iff.mp
  have huniv : (⋃ i, Set.range (g i).base) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, y, hy⟩ := hcover x
    exact Set.mem_iUnion.mpr ⟨i, y, hy⟩
  rw [← huniv]
  haveI : ∀ i, NoetherianSpace (Set.range (g i).base) := fun i =>
    haveI := hnoeth i
    NoetherianSpace.range (g i).base (g i).base.hom.continuous
  exact NoetherianSpace.iUnion _

end Charts

section TwoCharts

variable {X Y₁ Y₂ : Scheme.{u}} (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X) [IsOpenImmersion g₁]
  [IsOpenImmersion g₂]

/-- Two schemes as a `Bool`-indexed family (`true ↦ Y₁`, `false ↦ Y₂`). -/
def twoChartObj (Y₁ Y₂ : Scheme.{u}) : Bool → Scheme.{u} := fun b => Bool.rec Y₂ Y₁ b

/-- Two morphisms as a `Bool`-indexed family. -/
def twoChartMap : ∀ b, twoChartObj Y₁ Y₂ b ⟶ X :=
  fun b => Bool.rec (motive := fun b => twoChartObj Y₁ Y₂ b ⟶ X) g₂ g₁ b

instance twoChartMap_isOpenImmersion (b : Bool) : IsOpenImmersion (twoChartMap g₁ g₂ b) := by
  cases b
  · exact (inferInstance : IsOpenImmersion g₂)
  · exact (inferInstance : IsOpenImmersion g₁)

omit [IsOpenImmersion g₁] [IsOpenImmersion g₂] in
theorem twoChart_cover (hcover : ∀ x : X, (∃ y, g₁.base y = x) ∨ (∃ y, g₂.base y = x)) :
    ∀ x : X, ∃ (b : Bool) (y : twoChartObj Y₁ Y₂ b), (twoChartMap g₁ g₂ b).base y = x := by
  intro x
  rcases hcover x with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact ⟨true, y, hy⟩
  · exact ⟨false, y, hy⟩

/-- A scheme covered by two open immersions from locally Noetherian schemes is locally
Noetherian. -/
theorem isLocallyNoetherian_of_two_charts
    (hcover : ∀ x : X, (∃ y, g₁.base y = x) ∨ (∃ y, g₂.base y = x))
    [IsLocallyNoetherian Y₁] [IsLocallyNoetherian Y₂] : IsLocallyNoetherian X :=
  isLocallyNoetherian_of_charts (twoChartObj Y₁ Y₂) (twoChartMap g₁ g₂)
    (twoChart_cover g₁ g₂ hcover) (fun b => by
      cases b
      · exact (inferInstance : IsLocallyNoetherian Y₂)
      · exact (inferInstance : IsLocallyNoetherian Y₁))

omit [IsOpenImmersion g₁] [IsOpenImmersion g₂] in
/-- A scheme covered by two open immersions from Noetherian spaces is a Noetherian space. -/
theorem noetherianSpace_of_two_charts
    (hcover : ∀ x : X, (∃ y, g₁.base y = x) ∨ (∃ y, g₂.base y = x))
    [NoetherianSpace Y₁] [NoetherianSpace Y₂] : NoetherianSpace X :=
  noetherianSpace_of_charts (twoChartObj Y₁ Y₂) (twoChartMap g₁ g₂)
    (twoChart_cover g₁ g₂ hcover) (fun b => by
      cases b
      · exact (inferInstance : NoetherianSpace Y₂)
      · exact (inferInstance : NoetherianSpace Y₁))

end TwoCharts

/-- An open subscheme of a Noetherian space is a Noetherian space. -/
theorem noetherianSpace_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    [NoetherianSpace Y] : NoetherianSpace X :=
  f.isEmbedding.isInducing.noetherianSpace

/-! ## The polynomial plane, the Rees charts, the affine blowup, the projective product -/

theorem planeRing_isNoetherianRing : IsNoetherianRing (planeRing k) := inferInstance

theorem reesChartRing_isNoetherianRing : IsNoetherianRing (reesChartRing k) :=
  isNoetherianRing_of_ringEquiv (planeRing k) (chartPolynomialEquiv (k := k)).symm

theorem reesVChartRing_isNoetherianRing : IsNoetherianRing (reesVChartRing k) :=
  isNoetherianRing_of_ringEquiv (planeRing k) (vChartPolynomialEquiv (k := k)).symm

/-- The two degree-one chart rings of the blowup of the plane at the origin are Noetherian. -/
theorem chartRing_isNoetherianRing (i : Bool) :
    IsNoetherianRing (chartRing centerIdeal (centerGenerator (k := k) i)) := by
  cases i
  · exact reesChartRing_isNoetherianRing
  · exact reesVChartRing_isNoetherianRing

/-- The affine Rees blowup of the plane at the origin is locally Noetherian. -/
theorem affineBlowup_isLocallyNoetherian :
    IsLocallyNoetherian (scheme (centerIdeal (k := k))) := by
  refine isLocallyNoetherian_of_charts
    (fun i : Bool => Spec (CommRingCat.of (chartRing centerIdeal (centerGenerator (k := k) i))))
    (fun i => chartι centerIdeal (centerGenerator i)) ?_ ?_
  · intro x
    obtain ⟨y, hy⟩ :=
      (generatingAffineCover centerIdeal centerGenerator (span_centerGenerator (k := k))).covers x
    exact ⟨_, y, hy⟩
  · intro i
    haveI := chartRing_isNoetherianRing (k := k) i
    infer_instance

/-- The affine Rees blowup of the plane at the origin is a Noetherian space. -/
theorem affineBlowup_noetherianSpace : NoetherianSpace (scheme (centerIdeal (k := k))) := by
  refine noetherianSpace_of_charts
    (fun i : Bool => Spec (CommRingCat.of (chartRing centerIdeal (centerGenerator (k := k) i))))
    (fun i => chartι centerIdeal (centerGenerator i)) ?_ ?_
  · intro x
    obtain ⟨y, hy⟩ :=
      (generatingAffineCover centerIdeal centerGenerator (span_centerGenerator (k := k))).covers x
    exact ⟨_, y, hy⟩
  · intro i
    haveI := chartRing_isNoetherianRing (k := k) i
    infer_instance

/-- `P¹ × P¹` is locally Noetherian: it is covered by four polynomial planes. -/
theorem projectiveProduct_isLocallyNoetherian : IsLocallyNoetherian (projectiveProduct k) := by
  refine isLocallyNoetherian_of_charts
    (fun _ : Fin 2 × Fin 2 => Spec (CommRingCat.of (planeRing k)))
    (fun ij => productChart (k := k) ij.1 ij.2) ?_ (fun _ => inferInstance)
  intro x
  obtain ⟨i, j, y, hy⟩ := productCharts_cover x
  exact ⟨(i, j), y, hy⟩

/-- `P¹ × P¹` is a Noetherian space. -/
theorem projectiveProduct_noetherianSpace : NoetherianSpace (projectiveProduct k) := by
  refine noetherianSpace_of_charts
    (fun _ : Fin 2 × Fin 2 => Spec (CommRingCat.of (planeRing k)))
    (fun ij => productChart (k := k) ij.1 ij.2) ?_ (fun _ => inferInstance)
  intro x
  obtain ⟨i, j, y, hy⟩ := productCharts_cover x
  exact ⟨(i, j), y, hy⟩

/-! ## The stages -/

namespace PlaneChartedScheme

variable (A : PlaneChartedScheme k)

local instance stageNoetherianOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

/-- The glued next stage of a locally Noetherian charted plane is locally Noetherian: it is
covered by the affine Rees blowup and by the puncture of the carrier. -/
theorem nextScheme_isLocallyNoetherian [IsLocallyNoetherian A.carrier] :
    IsLocallyNoetherian A.nextScheme := by
  haveI : IsLocallyNoetherian (AffineBlowup.scheme (originPoint (k := k)).asIdeal) :=
    affineBlowup_isLocallyNoetherian
  haveI : IsLocallyNoetherian
      (PointBlowupGluing.puncture A.chart (originPoint (k := k)) A.center_closed).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion
      (PointBlowupGluing.puncture A.chart (originPoint (k := k)) A.center_closed).ι
  exact isLocallyNoetherian_of_two_charts
    (PointBlowupGluing.affineBlowupι A.chart (originPoint (k := k)) A.center_closed)
    (PointBlowupGluing.complementι A.chart (originPoint (k := k)) A.center_closed)
    (PointBlowupGluing.pieces_cover A.chart (originPoint (k := k)) A.center_closed)

/-- The glued next stage of a charted plane with Noetherian carrier is a Noetherian space. -/
theorem nextScheme_noetherianSpace [NoetherianSpace A.carrier] :
    NoetherianSpace A.nextScheme := by
  haveI : NoetherianSpace (AffineBlowup.scheme (originPoint (k := k)).asIdeal) :=
    affineBlowup_noetherianSpace
  haveI : NoetherianSpace
      (PointBlowupGluing.puncture A.chart (originPoint (k := k)) A.center_closed).toScheme :=
    noetherianSpace_of_isOpenImmersion
      (PointBlowupGluing.puncture A.chart (originPoint (k := k)) A.center_closed).ι
  exact noetherianSpace_of_two_charts
    (PointBlowupGluing.affineBlowupι A.chart (originPoint (k := k)) A.center_closed)
    (PointBlowupGluing.complementι A.chart (originPoint (k := k)) A.center_closed)
    (PointBlowupGluing.pieces_cover A.chart (originPoint (k := k)) A.center_closed)

/-- Every stage over a locally Noetherian charted plane is locally Noetherian. -/
theorem stage_isLocallyNoetherian [IsLocallyNoetherian A.carrier] :
    ∀ n : ℕ, IsLocallyNoetherian (A.stage n).carrier
  | 0 => (inferInstance : IsLocallyNoetherian A.carrier)
  | n + 1 =>
    haveI := stage_isLocallyNoetherian n
    nextScheme_isLocallyNoetherian (A.stage n)

/-- Every stage over a charted plane with Noetherian carrier is a Noetherian space. -/
theorem stage_noetherianSpace [NoetherianSpace A.carrier] :
    ∀ n : ℕ, NoetherianSpace (A.stage n).carrier
  | 0 => (inferInstance : NoetherianSpace A.carrier)
  | n + 1 =>
    haveI := stage_noetherianSpace n
    nextScheme_noetherianSpace (A.stage n)

/-- Every stage over a charted plane proper over `k` is of finite type over `k` (its structure
morphism is proper, accepted `stageStructure_isProper`). -/
theorem stage_locallyOfFiniteType [IsProper A.structureMap] (n : ℕ) :
    LocallyOfFiniteType (A.stage n).structureMap :=
  inferInstance

end PlaneChartedScheme

/-! ## The Frobenius contact tower -/

/-- The base `P¹ × P¹` of the contact tower is proper over `k`. -/
theorem projectiveProductInitial_structure_isProper :
    IsProper (projectiveProductInitial (k := k)).structureMap :=
  (inferInstance : IsProper (projectiveProductToSpec (k := k)))

theorem projectiveContactStage_isLocallyNoetherian (n : ℕ) :
    IsLocallyNoetherian (projectiveContactStage (k := k) n) :=
  haveI : IsLocallyNoetherian (projectiveProductInitial (k := k)).carrier :=
    projectiveProduct_isLocallyNoetherian
  PlaneChartedScheme.stage_isLocallyNoetherian projectiveProductInitial n

theorem projectiveContactStage_noetherianSpace (n : ℕ) :
    NoetherianSpace (projectiveContactStage (k := k) n) :=
  haveI : NoetherianSpace (projectiveProductInitial (k := k)).carrier :=
    projectiveProduct_noetherianSpace
  PlaneChartedScheme.stage_noetherianSpace projectiveProductInitial n

theorem projectiveContactStage_locallyOfFiniteType (n : ℕ) :
    LocallyOfFiniteType ((projectiveProductInitial (k := k)).stage n).structureMap :=
  haveI := projectiveProductInitial_structure_isProper (k := k)
  PlaneChartedScheme.stage_locallyOfFiniteType projectiveProductInitial n

/-! ## Discharging the instance hypotheses of the exceptional-chain corollary -/

section Chain

open FrobeniusExceptionalChainPicard

variable [IsAlgClosed k] (A : PlaneChartedScheme k) [NoetherianSpace A.carrier]
  [IsLocallyNoetherian A.carrier] [IsProper A.structureMap] (q : ℕ)

instance chainStage_noetherianSpace : NoetherianSpace (chainStage q A) :=
  PlaneChartedScheme.stage_noetherianSpace A (q + 1)

instance chainStage_isLocallyNoetherian : IsLocallyNoetherian (chainStage q A) :=
  PlaneChartedScheme.stage_isLocallyNoetherian A (q + 1)

instance chainStage_locallyOfFiniteType : LocallyOfFiniteType (A.stage (q + 1)).structureMap :=
  PlaneChartedScheme.stage_locallyOfFiniteType A (q + 1)

variable (hyp : ChainSinglePoints q A) (htrans : ChainTransversal q A hyp)

include htrans in
/-- **`chain_rationalTreePicard` with the Noetherian and finite-type hypotheses discharged**: for
a charted plane `A` with Noetherian, locally Noetherian carrier proper over `k`, the multidegree
map of the exceptional chain of `A_{q+1}` is bijective (modulo lane F's chain transversality). -/
theorem chain_rationalTreePicard_of_tower :
    Function.Bijective (multidegreeHom k (chainScheme q A)
      (lineIdentification (chainScheme q A) (chainCurve q A) (chainCurve_cover q A)
        (chainCurve_distinct q A hyp))) :=
  chain_rationalTreePicard q A hyp htrans

/-- `Pic(C_1 ∪ ⋯ ∪ C_q ∪ P) ≃* ℤ^{q+1}` for a tower over a Noetherian charted plane proper over `k`. -/
def chainPicardEquivFin_of_tower : (chainScheme q A).Pic ≃* (Fin (q + 1) → Multiplicative ℤ) :=
  chainPicardEquivFin q A hyp htrans

end Chain

section ContactTower

open FrobeniusExceptionalChainPicard

variable [IsAlgClosed k] (q : ℕ)

local instance contactTower_noetherianSpace :
    NoetherianSpace (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_noetherianSpace

local instance contactTower_isLocallyNoetherian :
    IsLocallyNoetherian (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isLocallyNoetherian

local instance contactTower_isProper : IsProper (projectiveProductInitial (k := k)).structureMap :=
  projectiveProductInitial_structure_isProper

variable (hyp : ChainSinglePoints q (projectiveProductInitial (k := k)))
  (htrans : ChainTransversal q (projectiveProductInitial (k := k)) hyp)

include htrans in
/-- The exceptional chain of the Frobenius contact tower: the multidegree map is bijective, with no
Noetherian or finite-type hypothesis left. -/
theorem contactTower_chain_rationalTreePicard :
    Function.Bijective (multidegreeHom k (chainScheme q (projectiveProductInitial (k := k)))
      (lineIdentification (chainScheme q (projectiveProductInitial (k := k)))
        (chainCurve q (projectiveProductInitial (k := k)))
        (chainCurve_cover q (projectiveProductInitial (k := k)))
        (chainCurve_distinct q (projectiveProductInitial (k := k)) hyp))) :=
  chain_rationalTreePicard_of_tower (projectiveProductInitial (k := k)) q hyp htrans

/-- `Pic(C_1 ∪ ⋯ ∪ C_q ∪ P) ≃* ℤ^{q+1}` on the Frobenius contact tower. -/
def contactTower_chainPicardEquivFin :
    (chainScheme q (projectiveProductInitial (k := k))).Pic ≃* (Fin (q + 1) → Multiplicative ℤ) :=
  chainPicardEquivFin_of_tower (projectiveProductInitial (k := k)) q hyp htrans

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (q₀ : ℕ)
    (hyp : ChainSinglePoints q₀ (projectiveProductInitial (k := k₀)))
    (htrans : ChainTransversal q₀ (projectiveProductInitial (k := k₀)) hyp) :
    (chainScheme q₀ (projectiveProductInitial (k := k₀))).Pic ≃*
      (Fin (q₀ + 1) → Multiplicative ℤ) :=
  contactTower_chainPicardEquivFin q₀ hyp htrans

end ContactTower

end KltDP.Examples.FrobeniusStageNoetherianFiniteType
