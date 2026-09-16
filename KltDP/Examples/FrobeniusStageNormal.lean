import KltDP.Examples.FrobeniusGlobalBlowupSmooth
import KltDP.Examples.FrobeniusGraphPicardClassCharts
import KltDP.Geometry.AffineBlowupCover
import KltDP.Geometry.ProjectiveChartNormal

/-!
# Normality of the contact-tower stages

Every stage `projectiveContactStage n` of the accepted Frobenius contact tower is a normal scheme
(`IsNormalScheme`: every stalk is an integrally closed domain), for every field `k`.

The proof is chart by chart, with no smoothness or regularity input:

* the polynomial plane `Spec k[u][v]` is normal (`k[u][v]` is a unique factorisation domain, hence
  integrally closed; accepted `spec_isNormalScheme_of_isIntegrallyClosed`);
* the projective product `P¹ ×_k P¹` is covered by the four accepted polynomial charts
  `productChart i j` (`productCharts_cover`), so it is normal (`projectiveProduct_isNormalScheme`);
* the affine Rees blowup of the plane at the origin is covered by its two degree-one charts
  (`generatingAffineCover centerIdeal centerGenerator`), whose rings are the polynomial plane through
  the accepted `chartPolynomialEquiv`/`vChartPolynomialEquiv` (`affineBlowup_isNormalScheme`);
* each global stage is glued from the affine Rees blowup and the puncture of the previous stage
  (`PointBlowupGluing.pieces_cover`), and normality is a stalk property transported along open
  immersions (accepted `normal_stalk_at_image_of_isOpenImmersion`,
  `isNormalScheme_of_isOpenImmersion`).

Exports: `isNormalScheme_of_charts` (normality from a family of open immersions with normal sources
that jointly cover), `PlaneChartedScheme.stage_isNormalScheme` (any charted plane with normal
carrier has normal stages), `projectiveContactStage_isNormalScheme`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStageNormal

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusProjectivePoints FrobeniusGraphPicardClassCharts FrobeniusGlobalBlowupStages

variable {k : Type u} [Field k]

/-- Normality is a stalk property: a scheme covered by the images of open immersions from normal
schemes is normal. -/
theorem isNormalScheme_of_charts {X : Scheme.{u}} {ι : Type*} (Y : ι → Scheme.{u})
    (g : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (g i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), (g i).base y = x)
    (hnormal : ∀ i, IsNormalScheme (Y i)) : IsNormalScheme X := by
  intro x
  obtain ⟨i, y, rfl⟩ := hcover x
  exact normal_stalk_at_image_of_isOpenImmersion (g i) (hnormal i) y

/-- The polynomial plane `k[u][v]` is integrally closed (unique factorisation). -/
theorem planeRing_isIntegrallyClosed : IsIntegrallyClosed (planeRing k) := by
  infer_instance

/-- The polynomial plane is a normal scheme. -/
theorem plane_isNormalScheme : IsNormalScheme (Spec (CommRingCat.of (planeRing k))) := by
  letI : IsIntegrallyClosed (planeRing k) := planeRing_isIntegrallyClosed
  exact spec_isNormalScheme_of_isIntegrallyClosed (planeRing k)

/-- The projective product `P¹ ×_k P¹` is normal: it is covered by four polynomial planes. -/
theorem projectiveProduct_isNormalScheme : IsNormalScheme (projectiveProduct k) := by
  refine isNormalScheme_of_charts (fun _ : Fin 2 × Fin 2 => Spec (CommRingCat.of (planeRing k)))
    (fun ij => productChart (k := k) ij.1 ij.2) ?_ (fun _ => plane_isNormalScheme)
  intro x
  obtain ⟨i, j, y, hy⟩ := productCharts_cover x
  exact ⟨(i, j), y, hy⟩

/-- The first Rees chart `Spec k[u, v/u]` of the blowup of the plane at the origin is normal. -/
theorem reesUChart_isNormalScheme : IsNormalScheme (Spec (CommRingCat.of (reesChartRing k))) := by
  letI : IsDomain (reesChartRing k) :=
    MulEquiv.isDomain (planeRing k) (chartPolynomialEquiv (k := k)).toMulEquiv
  letI : IsIntegrallyClosed (planeRing k) := planeRing_isIntegrallyClosed
  letI : IsIntegrallyClosed (reesChartRing k) :=
    isIntegrallyClosed_of_ringEquiv (chartPolynomialEquiv (k := k)).symm
  exact spec_isNormalScheme_of_isIntegrallyClosed (reesChartRing k)

/-- The second Rees chart `Spec k[u/v, v]` is normal. -/
theorem reesVChart_isNormalScheme :
    IsNormalScheme (Spec (CommRingCat.of (reesVChartRing k))) := by
  letI : IsDomain (reesVChartRing k) :=
    MulEquiv.isDomain (planeRing k) (vChartPolynomialEquiv (k := k)).toMulEquiv
  letI : IsIntegrallyClosed (planeRing k) := planeRing_isIntegrallyClosed
  letI : IsIntegrallyClosed (reesVChartRing k) :=
    isIntegrallyClosed_of_ringEquiv (vChartPolynomialEquiv (k := k)).symm
  exact spec_isNormalScheme_of_isIntegrallyClosed (reesVChartRing k)

/-- The affine Rees blowup of the plane at the origin is normal: its two degree-one charts cover it
and are polynomial planes. -/
theorem affineBlowup_isNormalScheme : IsNormalScheme (scheme (centerIdeal (k := k))) := by
  refine isNormalScheme_of_charts
    (fun i : Bool => Spec (CommRingCat.of (chartRing centerIdeal (centerGenerator (k := k) i))))
    (fun i => chartι centerIdeal (centerGenerator i)) ?_ ?_
  · intro x
    obtain ⟨y, hy⟩ :=
      (generatingAffineCover centerIdeal centerGenerator (span_centerGenerator (k := k))).covers x
    exact ⟨_, y, hy⟩
  · intro i
    cases i
    · exact reesUChart_isNormalScheme
    · exact reesVChart_isNormalScheme

namespace PlaneChartedScheme

variable (A : PlaneChartedScheme k)

local instance stageNormalOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

/-- The glued next stage of a charted plane with normal carrier is normal: it is covered by the
affine Rees blowup and by the puncture of the carrier. -/
theorem nextScheme_isNormalScheme (hA : IsNormalScheme A.carrier) :
    IsNormalScheme A.nextScheme := by
  intro x
  rcases PointBlowupGluing.pieces_cover A.chart (originPoint (k := k)) A.center_closed x with
    ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact normal_stalk_at_image_of_isOpenImmersion
      (PointBlowupGluing.affineBlowupι A.chart (originPoint (k := k)) A.center_closed)
      affineBlowup_isNormalScheme a
  · exact normal_stalk_at_image_of_isOpenImmersion
      (PointBlowupGluing.complementι A.chart (originPoint (k := k)) A.center_closed)
      (isNormalScheme_of_isOpenImmersion
        (PointBlowupGluing.puncture A.chart (originPoint (k := k)) A.center_closed).ι hA) b

/-- Every stage of the tower over a charted plane with normal carrier is normal. -/
theorem stage_isNormalScheme (hA : IsNormalScheme A.carrier) :
    ∀ n : ℕ, IsNormalScheme (A.stage n).carrier
  | 0 => hA
  | n + 1 => nextScheme_isNormalScheme (A.stage n) (stage_isNormalScheme hA n)

end PlaneChartedScheme

/-- **Every stage of the Frobenius contact tower is normal**, over any field. -/
theorem projectiveContactStage_isNormalScheme (n : ℕ) :
    IsNormalScheme (projectiveContactStage (k := k) n) :=
  PlaneChartedScheme.stage_isNormalScheme projectiveProductInitial
    projectiveProduct_isNormalScheme n

end KltDP.Examples.FrobeniusStageNormal
