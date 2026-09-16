import KltDP.Examples.FrobeniusStrictTransformSecondChartFrame
import KltDP.Examples.FrobeniusStrictTransformInvertible
import KltDP.Examples.FrobeniusStrictTransformStepPuncture

/-!
# The original three-open cover for one-step ideal factorization

The two original Rees charts cover the affine blowup because u,v generate its
center ideal. The original glued blowup is covered by this affine piece and the
unchanged current-center complement. The first coordinate-chart isomorphism
identifies the first Rees range with the literal successor first affine open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStrictTransformProductCover

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform FrobeniusStrictTransformInvertible
open FrobeniusStrictTransformSecondChart FrobeniusStrictTransformSecondChartFrame
open FrobeniusStrictTransformStepPuncture

variable {k : Type u} [Field k]

local instance productCoverOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

private theorem range_precompose_iso {A B X : Scheme.{u}} (e : A ≅ B) (j : B ⟶ X) :
    Set.range (e.hom ≫ j).base = Set.range j.base := by
  change Set.range (j.base ∘ e.hom.base) = _
  rw [Set.range_comp, e.hom.surjective.range_eq, Set.image_univ]

private theorem firstStageChart_range (n : ℕ) :
    Set.range (((projectiveProductInitial (k := k)).stage (n + 1)).chart).base =
      Set.range (chartι (centerIdeal (k := k)) centerU ≫
        ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup).base := by
  change Set.range (((coordinateChartIso (k := k)).hom ≫ chartι (centerIdeal (k := k)) centerU) ≫
    ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup).base = _
  rw [Category.assoc]
  exact range_precompose_iso (coordinateChartIso (k := k)) _

private theorem affine_twoChart_cover (x : scheme (centerIdeal (k := k))) :
    x ∈ Set.range (chartι (centerIdeal (k := k)) centerU).base ∨
      x ∈ Set.range (chartι (centerIdeal (k := k)) centerV).base := by
  obtain ⟨i, z, hz⟩ := (generatingAffineCover (centerIdeal (k := k)) centerGenerator
    span_centerGenerator).openCover.exists_eq x
  change (chartι centerIdeal (centerGenerator i)).base z = x at hz
  cases i with
  | false => exact Or.inl ⟨z, hz⟩
  | true => exact Or.inr ⟨z, hz⟩

/-- The literal two successor affine opens and actual current-center puncture cover the whole stage. -/
theorem strictProductStage_cover (n : ℕ)
    (x : projectiveContactStage (k := k) (n + 1)) :
    x ∈ (firstAffineOpen (n + 1)).1 ∨
      x ∈ (secondAffineOpen n).1 ∨ x ∈ nextPuncture n := by
  let A := (projectiveProductInitial (k := k)).stage n
  rcases PointBlowupGluing.pieces_cover A.chart (originPoint (k := k)) A.center_closed x with
    ⟨a, ha⟩ | ⟨c, hc⟩
  · rcases affine_twoChart_cover a with ⟨z, hz⟩ | ⟨z, hz⟩
    · left
      change x ∈ (((projectiveProductInitial (k := k)).stage (n + 1)).chart ''ᵁ ⊤)
      rw [Scheme.Hom.image_top_eq_opensRange]
      change x ∈ Set.range (((projectiveProductInitial (k := k)).stage (n + 1)).chart).base
      rw [firstStageChart_range]
      refine ⟨z, ?_⟩
      change A.nextAffineBlowup.base ((chartι (centerIdeal (k := k)) centerU).base z) = x
      exact (congrArg A.nextAffineBlowup.base hz).trans ha
    · right
      left
      change x ∈ (secondStageChart (k := k) n ''ᵁ ⊤)
      rw [Scheme.Hom.image_top_eq_opensRange]
      change x ∈ Set.range (secondStageChart (k := k) n).base
      refine ⟨z, ?_⟩
      change A.nextAffineBlowup.base ((chartι (centerIdeal (k := k)) centerV).base z) = x
      exact (congrArg A.nextAffineBlowup.base hz).trans ha
  · right
    right
    have h : x ∈ Set.range
        (PointBlowupGluing.complementι A.chart (originPoint (k := k)) A.center_closed).base :=
      ⟨c, hc⟩
    rw [PointBlowupGluing.range_complementι] at h
    exact h

/-- The actual three-open supremum, with the original current-center puncture. -/
theorem strictProductStage_opens_sup (n : ℕ) :
    (firstAffineOpen (k := k) (n + 1)).1 ⊔ (secondAffineOpen n).1 ⊔ nextPuncture n = ⊤ := by
  apply top_le_iff.mp
  intro x _
  rcases strictProductStage_cover n x with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- A three-element indexing of the literal original opens. -/
def strictProductCoverOpen (n : ℕ) : Option Bool →
    (projectiveContactStage (k := k) (n + 1)).Opens
  | none => (firstAffineOpen (n + 1)).1
  | some false => (secondAffineOpen n).1
  | some true => nextPuncture n

theorem strictProductCoverOpen_covers (n : ℕ)
    (x : projectiveContactStage (k := k) (n + 1)) :
    ∃ i, x ∈ strictProductCoverOpen n i := by
  rcases strictProductStage_cover n x with h | h | h
  · exact ⟨none, h⟩
  · exact ⟨some false, h⟩
  · exact ⟨some true, h⟩

end KltDP.Examples.FrobeniusStrictTransformProductCover
