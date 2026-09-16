import KltDP.Geometry.PointClosureCurve
import KltDP.Geometry.PrimeCurveStalkCoordinates
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Recovering a curve from an actual height-one stalk prime

Contract a height-one prime of a structure-sheaf stalk along an actual
affine germ and take the corresponding scheme point. Its stalk has
dimension one, it specializes to the original point, and it is not the
generic point of the surface.

If this new point is nonclosed, its actual closure is a prime curve and
extending its ideal back to the original stalk recovers the given prime.
In particular this gives the full reverse correspondence at any point
whose actual stalk dimension is greater than one.

For a general point, the remaining alternative is stated explicitly:
the contracted height-one point may be globally closed. Excluding that
alternative from the finite-type surface hypotheses is a separate
dimension argument, not an assumption hidden in a curve structure.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Contract an actual stalk prime through the actual structure-sheaf germ. -/
def stalkPrimeInChart {U : X.toScheme.Opens} (x : U)
    (q : RingTheory.AffineHeightOnePrime (X.stalk x)) : PrimeSpectrum Γ(X.toScheme, U) :=
  PrimeSpectrum.comap (X.toScheme.presheaf.germ U x x.2).hom q.1

/-- The actual affine-chart point corresponding to the contracted prime. -/
def stalkPrimeChartPoint {U : X.toScheme.Opens} (hU : IsAffineOpen U) (x : U)
    (q : RingTheory.AffineHeightOnePrime (X.stalk x)) : U :=
  hU.isoSpec.inv.base (X.stalkPrimeInChart x q)

theorem stalkPrimeChartPoint_primeIdealOf {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (x : U) (q : RingTheory.AffineHeightOnePrime (X.stalk x)) :
    hU.primeIdealOf (X.stalkPrimeChartPoint hU x q) = X.stalkPrimeInChart x q := by
  have h := congrArg
    (fun f : Spec (.of Γ(X.toScheme, U)) ⟶ Spec (.of Γ(X.toScheme, U)) =>
      f.base (X.stalkPrimeInChart x q)) hU.isoSpec.inv_hom_id
  exact h

/-- Contraction preserves the actual height one. -/
theorem stalkPrimeInChart_height {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    (x : U) (q : RingTheory.AffineHeightOnePrime (X.stalk x)) :
    (X.stalkPrimeInChart x q).asIdeal.height = 1 := by
  letI : Algebra Γ(X.toScheme, U) (X.stalk x) :=
    X.toScheme.presheaf.algebra_section_stalk x
  letI : IsLocalization.AtPrime (X.stalk x) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  exact (IsLocalization.height_comap (hU.primeIdealOf x).asIdeal.primeCompl
    q.1.asIdeal).trans q.2

/-- The contracted prime lies below the original point's affine prime. -/
theorem stalkPrimeInChart_le {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    (x : U) (q : RingTheory.AffineHeightOnePrime (X.stalk x)) :
    (X.stalkPrimeInChart x q).asIdeal ≤ (hU.primeIdealOf x).asIdeal := by
  letI : Algebra Γ(X.toScheme, U) (X.stalk x) :=
    X.toScheme.presheaf.algebra_section_stalk x
  letI : IsLocalization.AtPrime (X.stalk x) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  intro a ha
  by_contra hnot
  have hunit : IsUnit (algebraMap Γ(X.toScheme, U) (X.stalk x) a) :=
    IsLocalization.map_units (X.stalk x)
      (⟨a, hnot⟩ : (hU.primeIdealOf x).asIdeal.primeCompl)
  exact q.1.isPrime.ne_top (q.1.asIdeal.eq_top_of_isUnit_mem ha hunit)

/-- The actual point corresponding to the stalk prime specializes to the
point of the original stalk. -/
theorem stalkPrimeChartPoint_specializes {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (x : U) (q : RingTheory.AffineHeightOnePrime (X.stalk x)) :
    (X.stalkPrimeChartPoint hU x q : X.toScheme) ⤳ (x : X.toScheme) := by
  have hle : X.stalkPrimeInChart x q ≤ hU.primeIdealOf x :=
    X.stalkPrimeInChart_le hU x q
  have hs := ((PrimeSpectrum.le_iff_specializes _ _).mp hle).map hU.fromSpec.continuous
  have hy := hU.fromSpec_primeIdealOf (X.stalkPrimeChartPoint hU x q)
  rw [X.stalkPrimeChartPoint_primeIdealOf hU x q] at hy
  simpa only [hy, hU.fromSpec_primeIdealOf] using hs

/-- The contracted point's original scheme stalk has dimension exactly one. -/
theorem stalkPrimeChartPoint_stalk_dimension {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (x : U) (q : RingTheory.AffineHeightOnePrime (X.stalk x)) :
    ringKrullDim (X.stalk (X.stalkPrimeChartPoint hU x q)) = 1 := by
  let y := X.stalkPrimeChartPoint hU x q
  letI : Algebra Γ(X.toScheme, U) (X.stalk y) :=
    X.toScheme.presheaf.algebra_section_stalk y
  letI : IsLocalization.AtPrime (X.stalk y) (hU.primeIdealOf y).asIdeal :=
    hU.isLocalization_stalk y
  have hp : (hU.primeIdealOf y).asIdeal.height = 1 := by
    rw [X.stalkPrimeChartPoint_primeIdealOf hU x q]
    exact X.stalkPrimeInChart_height hU x q
  simpa only [hp] using IsLocalization.AtPrime.ringKrullDim_eq_height
    (hU.primeIdealOf y).asIdeal (X.stalk y)

/-- A height-one stalk prime never contracts to the surface's generic point. -/
theorem stalkPrimeChartPoint_ne_genericPoint {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (x : U) (q : RingTheory.AffineHeightOnePrime (X.stalk x)) :
    (X.stalkPrimeChartPoint hU x q : X.toScheme) ≠ genericPoint X.toScheme := by
  intro hgeneric
  have hdim := X.stalkPrimeChartPoint_stalk_dimension hU x q
  rw [hgeneric] at hdim
  change ringKrullDim X.toScheme.functionField = 1 at hdim
  rw [ringKrullDim_eq_zero_of_field] at hdim
  norm_num at hdim

/-- If the contracted point is nonclosed, its actual closure gives a
curve through the original point whose stalk prime is exactly the input. -/
theorem exists_primeCurve_of_stalkPrimeChartPoint_nonclosed
    {U : X.toScheme.Opens} (hU : IsAffineOpen U) (x : U)
    (q : RingTheory.AffineHeightOnePrime (X.stalk x))
    (hclosed : ¬ IsClosed ({(X.stalkPrimeChartPoint hU x q : X.toScheme)} :
      Set X.toScheme)) :
    ∃ (C : X.PrimeCurve) (hx : (x : X.toScheme) ∈ C),
      C.stalkHeightOnePrime hU x hx = q := by
  let y := X.stalkPrimeChartPoint hU x q
  have hgeneric : (y : X.toScheme) ≠ genericPoint X.toScheme :=
    X.stalkPrimeChartPoint_ne_genericPoint hU x q
  let C := X.primeCurveOfNonclosedPoint y hgeneric hclosed
  have hCgeneric : C.genericPoint = y :=
    X.primeCurveOfNonclosedPoint_genericPoint y hgeneric hclosed
  have hxC : (x : X.toScheme) ∈ C :=
    (X.mem_primeCurveOfNonclosedPoint y x hgeneric hclosed).mpr
      (X.stalkPrimeChartPoint_specializes hU x q)
  refine ⟨C, hxC, ?_⟩
  letI : Algebra Γ(X.toScheme, U) (X.stalk x) :=
    X.toScheme.presheaf.algebra_section_stalk x
  letI : IsLocalization.AtPrime (X.stalk x) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  have hc : (C.stalkHeightOnePrime hU x hxC).1.asIdeal.comap
      (algebraMap Γ(X.toScheme, U) (X.stalk x)) =
      q.1.asIdeal.comap (algebraMap Γ(X.toScheme, U) (X.stalk x)) := by
    change (C.stalkHeightOnePrime hU x hxC).1.asIdeal.comap
        (X.toScheme.presheaf.germ U x x.2).hom =
      q.1.asIdeal.comap (X.toScheme.presheaf.germ U x x.2).hom
    rw [C.stalkHeightOnePrime_comap hU x hxC]
    have hpoint : (⟨C.genericPoint, C.genericPoint_mem_of_mem x hxC⟩ : U) = y :=
      Subtype.ext hCgeneric
    change (hU.primeIdealOf ⟨C.genericPoint, C.genericPoint_mem_of_mem x hxC⟩).asIdeal = _
    rw [hpoint, X.stalkPrimeChartPoint_primeIdealOf hU x q]
    rfl
  apply Subtype.ext
  apply PrimeSpectrum.ext
  calc
    (C.stalkHeightOnePrime hU x hxC).1.asIdeal =
        ((C.stalkHeightOnePrime hU x hxC).1.asIdeal.comap
          (algebraMap Γ(X.toScheme, U) (X.stalk x))).map
            (algebraMap Γ(X.toScheme, U) (X.stalk x)) :=
      (IsLocalization.map_comap (hU.primeIdealOf x).asIdeal.primeCompl
        (X.stalk x) _).symm
    _ = (q.1.asIdeal.comap (algebraMap Γ(X.toScheme, U) (X.stalk x))).map
        (algebraMap Γ(X.toScheme, U) (X.stalk x)) :=
      congrArg (Ideal.map (algebraMap Γ(X.toScheme, U) (X.stalk x))) hc
    _ = q.1.asIdeal := IsLocalization.map_comap
      (hU.primeIdealOf x).asIdeal.primeCompl (X.stalk x) _

/-- The only remaining alternative in recovering a curve is that the
contracted height-one point is globally closed. -/
theorem stalkPrimeChartPoint_closed_or_exists_primeCurve
    {U : X.toScheme.Opens} (hU : IsAffineOpen U) (x : U)
    (q : RingTheory.AffineHeightOnePrime (X.stalk x)) :
    IsClosed ({(X.stalkPrimeChartPoint hU x q : X.toScheme)} : Set X.toScheme) ∨
      ∃ (C : X.PrimeCurve) (hx : (x : X.toScheme) ∈ C),
        C.stalkHeightOnePrime hU x hx = q := by
  by_cases hclosed : IsClosed
      ({(X.stalkPrimeChartPoint hU x q : X.toScheme)} : Set X.toScheme)
  · exact Or.inl hclosed
  · exact Or.inr (X.exists_primeCurve_of_stalkPrimeChartPoint_nonclosed hU x q hclosed)

/-- At a point of stalk dimension greater than one, every actual
height-one stalk prime comes from an actual curve through that point. -/
theorem stalkHeightOnePrime_surjective_of_one_lt_dimension
    {U : X.toScheme.Opens} (hU : IsAffineOpen U) (x : U)
    (hdim : 1 < ringKrullDim (X.stalk x)) :
    Function.Surjective (fun C : {C : X.PrimeCurve // (x : X.toScheme) ∈ C} =>
      C.1.stalkHeightOnePrime hU x C.2) := by
  intro q
  have hne : (X.stalkPrimeChartPoint hU x q : X.toScheme) ≠ (x : X.toScheme) := by
    intro heq
    have hy := X.stalkPrimeChartPoint_stalk_dimension hU x q
    rw [heq] at hy
    exact hdim.ne hy.symm
  have hclosed : ¬ IsClosed
      ({(X.stalkPrimeChartPoint hU x q : X.toScheme)} : Set X.toScheme) := by
    intro hc
    have hm := (X.stalkPrimeChartPoint_specializes hU x q).mem_closure
    rw [hc.closure_eq] at hm
    exact hne (Set.mem_singleton_iff.mp hm).symm
  obtain ⟨C, hxC, hC⟩ :=
    X.exists_primeCurve_of_stalkPrimeChartPoint_nonclosed hU x q hclosed
  exact ⟨⟨C, hxC⟩, hC⟩

end KltDP.Geometry.NormalProjectiveSurface
