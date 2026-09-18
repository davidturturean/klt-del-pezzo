import KltDP.Geometry.PointBlowupChartStalkAtCenter
import KltDP.Geometry.AffineBlowupCover

/-!
# Original chart points above the actual blowup centre

The original two-piece cover excludes the puncture piece over the
centre. The original Rees affine cover then supplies a literal chart
point. Its actual prime contracts to the original centre ideal by the
original projection square and injectivity of the original open chart.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PointBlowupChartStalk

open AffineBlowup PointBlowupGluing

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
variable (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
variable (hclosed : IsClosed ({j.base q} : Set X))

/-- Every original point above the centre is represented in an actual
original Rees chart, whose prime has the proved original centre image. -/
theorem exists_original_chart_over_center (y : PointBlowupGluing.scheme j q hclosed)
    (hy : (projection j q hclosed).base y = j.base q) :
    ∃ (a : q.asIdeal) (P : PrimeSpectrum (chartRing q.asIdeal a)),
      (chartInclusion j q hclosed a).base P = y ∧
        P.asIdeal.comap (chartBaseMap q.asIdeal a) = q.asIdeal := by
  rcases pieces_cover j q hclosed y with ⟨u, rfl⟩ | ⟨b, rfl⟩
  · obtain ⟨a, P, hP⟩ := (degreeOneAffineCover q.asIdeal).openCover.exists_eq u
    change (chartι q.asIdeal a).base P = u at hP
    have hi : (chartInclusion j q hclosed a).base P = (affineBlowupι j q hclosed).base u :=
      congrArg (affineBlowupι j q hclosed).base hP
    refine ⟨a, P, hi, ?_⟩
    have hbase : j.base (PrimeSpectrum.comap (chartBaseMap q.asIdeal a) P) = j.base q := by
      calc
        _ = (projection j q hclosed).base ((chartInclusion j q hclosed a).base P) :=
          (congrArg
            (fun f : Spec (CommRingCat.of (chartRing q.asIdeal a)) ⟶ X => f.base P)
            (chartInclusion_projection j q hclosed a)).symm
        _ = (projection j q hclosed).base ((affineBlowupι j q hclosed).base u) :=
          congrArg (projection j q hclosed).base hi
        _ = j.base q := hy
    exact congrArg PrimeSpectrum.asIdeal (j.isOpenEmbedding.injective hbase)
  · have hn : b.val ≠ j.base q := b.property
    change (complementι j q hclosed ≫ projection j q hclosed).base b = j.base q at hy
    rw [complementι_projection] at hy
    exact (hn hy).elim

end KltDP.Geometry.PointBlowupChartStalk
