import KltDP.Geometry.ProjectiveSpaceNormal
import KltDP.Geometry.HomogeneousAwayLift

/-!
# The coordinate charts `D(z_i)` of `projectiveSpace k n` and their overlaps

For every coordinate `i : Fin (n+1)` the accepted `Proj` chart `Spec (coordinateChartRing k n i) ⟶
projectiveSpace k n` (pinned `Proj.awayι` at `X i`): an open immersion with range `D(z_i)`, over `k`
(`coordinateChartMorphism_over_base`, the general-`i` form of the accepted `P¹` lemma
`chartImmersion_structureMap`), assembled into the open cover `coordinateChartCover` (universe-lifted
index, as the pinned gluing API requires). Pairwise overlaps `D(z_i) ∩ D(z_j)` are
`Spec (coordinateOverlapRing k n i j) = Spec (A_{(z_i z_j)})` (pinned `Proj.pullbackAwayιIso`), with
the two projections the spectra of the pinned `awayMap`s (`toOverlapLeft`, `toOverlapRight`), and
both chart maps restricted to the overlap are the chart map of `z_i z_j`
(`SpecMap_toOverlapLeft_chart`, `SpecMap_toOverlapRight_chart`).

The chart ring `A_{(z_i)}` is identified with `affineRing k n` through the accepted
`firstChartEquivCoordinateChart` and `coordinateRingEquiv` (`coordinateChartAffineEquiv`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

theorem coordinate_mem (i : Fin (n + 1)) :
    (MvPolynomial.X i : homogeneousRing k n) ∈ grading k n 1 :=
  MvPolynomial.isHomogeneous_X k i

/-- The `Proj` chart of the coordinate `z_i`. -/
def coordinateChartMorphism (i : Fin (n + 1)) :
    Spec (CommRingCat.of (coordinateChartRing k n i)) ⟶ projectiveSpace k n :=
  Proj.awayι (grading k n) (MvPolynomial.X i) (coordinate_mem k n i) Nat.one_pos

instance coordinateChartMorphism_isOpenImmersion (i : Fin (n + 1)) :
    IsOpenImmersion (coordinateChartMorphism k n i) := by
  unfold coordinateChartMorphism
  infer_instance

theorem coordinateChartMorphism_opensRange (i : Fin (n + 1)) :
    (coordinateChartMorphism k n i).opensRange =
      Proj.basicOpen (grading k n) (MvPolynomial.X i) :=
  Proj.opensRange_awayι (grading k n) (MvPolynomial.X i) (coordinate_mem k n i) Nat.one_pos

/-- The chart of `z₀` is the accepted `chartMorphism`. -/
theorem coordinateChartMorphism_zero : coordinateChartMorphism k n 0 = chartMorphism k n := rfl

/-- The base constants in the chart ring of `z_i`. -/
def coordinateChartConstants (i : Fin (n + 1)) : k →+* coordinateChartRing k n i :=
  (HomogeneousLocalization.fromZeroRingHom (grading k n)
    (Submonoid.powers (MvPolynomial.X i : homogeneousRing k n))).comp
    (projectiveSpaceConstants k n)

/-- Every coordinate chart is over `k`. -/
theorem coordinateChartMorphism_over_base (i : Fin (n + 1)) :
    coordinateChartMorphism k n i ≫ projectiveSpaceToSpec k n =
      Spec.map (CommRingCat.ofHom (coordinateChartConstants k n i)) := by
  unfold coordinateChartMorphism projectiveSpaceToSpec
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The chart ring of `z_i` is the polynomial ring in `n` variables (accepted coordinate swap and
dehomogenization). -/
def coordinateChartAffineEquiv (i : Fin (n + 1)) :
    coordinateChartRing k n i ≃+* affineRing k n :=
  (firstChartEquivCoordinateChart k n i).symm.trans (coordinateRingEquiv k n)

/-- The coordinate charts as an open cover with universe-lifted index. -/
def coordinateChartCover : Scheme.OpenCover.{u} (projectiveSpace k n) where
  J := ULift.{u} (Fin (n + 1))
  obj i := Spec (CommRingCat.of (coordinateChartRing k n i.down))
  map i := coordinateChartMorphism k n i.down
  f x := ⟨(standardAffineCover k n).f x⟩
  covers x := (standardAffineCover k n).covers x

@[simp] theorem coordinateChartCover_map (i : ULift.{u} (Fin (n + 1))) :
    (coordinateChartCover k n).map i = coordinateChartMorphism k n i.down := rfl

/-- The coordinate ring of the overlap `D(z_i) ∩ D(z_j)`. -/
abbrev coordinateOverlapRing (i j : Fin (n + 1)) :=
  HomogeneousLocalization.Away (grading k n)
    ((MvPolynomial.X i : homogeneousRing k n) * MvPolynomial.X j)

theorem coordinate_mul_mem (i j : Fin (n + 1)) :
    (MvPolynomial.X i : homogeneousRing k n) * MvPolynomial.X j ∈ grading k n (1 + 1) :=
  SetLike.mul_mem_graded (coordinate_mem k n i) (coordinate_mem k n j)

/-- The `Proj` chart of the product `z_i z_j`. -/
def coordinateOverlapMorphism (i j : Fin (n + 1)) :
    Spec (CommRingCat.of (coordinateOverlapRing k n i j)) ⟶ projectiveSpace k n :=
  Proj.awayι (grading k n) _ (coordinate_mul_mem k n i j) (by decide)

/-- Restriction from the chart of `z_i` to the overlap with the chart of `z_j`. -/
def toOverlapLeft (i j : Fin (n + 1)) :
    coordinateChartRing k n i →+* coordinateOverlapRing k n i j :=
  HomogeneousLocalization.awayMap (grading k n) (coordinate_mem k n j) rfl

/-- Restriction from the chart of `z_j` to the overlap with the chart of `z_i`. -/
def toOverlapRight (i j : Fin (n + 1)) :
    coordinateChartRing k n j →+* coordinateOverlapRing k n i j :=
  HomogeneousLocalization.awayMap (grading k n) (coordinate_mem k n i) (mul_comm _ _)

/-- The overlap of two coordinate charts is the chart of the product coordinate. -/
def coordinateOverlapIso (i j : Fin (n + 1)) :
    pullback (coordinateChartMorphism k n i) (coordinateChartMorphism k n j) ≅
      Spec (CommRingCat.of (coordinateOverlapRing k n i j)) :=
  Proj.pullbackAwayιIso (grading k n) (coordinate_mem k n i) Nat.one_pos
    (coordinate_mem k n j) Nat.one_pos rfl

@[reassoc]
theorem coordinateOverlapIso_inv_fst (i j : Fin (n + 1)) :
    (coordinateOverlapIso k n i j).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (toOverlapLeft k n i j)) :=
  Proj.pullbackAwayιIso_inv_fst (grading k n) (coordinate_mem k n i) Nat.one_pos
    (coordinate_mem k n j) Nat.one_pos rfl

@[reassoc]
theorem coordinateOverlapIso_inv_snd (i j : Fin (n + 1)) :
    (coordinateOverlapIso k n i j).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (toOverlapRight k n i j)) :=
  Proj.pullbackAwayιIso_inv_snd (grading k n) (coordinate_mem k n i) Nat.one_pos
    (coordinate_mem k n j) Nat.one_pos rfl

/-- The chart of `z_i`, restricted to the overlap, is the chart of `z_i z_j`. -/
@[reassoc]
theorem SpecMap_toOverlapLeft_chart (i j : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom (toOverlapLeft k n i j)) ≫ coordinateChartMorphism k n i =
      coordinateOverlapMorphism k n i j :=
  Proj.SpecMap_awayMap_awayι (grading k n) (coordinate_mem k n i) Nat.one_pos
    (coordinate_mem k n j) rfl

/-- The chart of `z_j`, restricted to the overlap, is the chart of `z_i z_j`. -/
@[reassoc]
theorem SpecMap_toOverlapRight_chart (i j : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom (toOverlapRight k n i j)) ≫ coordinateChartMorphism k n j =
      coordinateOverlapMorphism k n i j :=
  Proj.SpecMap_awayMap_awayι (grading k n) (coordinate_mem k n j) Nat.one_pos
    (coordinate_mem k n i) (mul_comm _ _)

/-- The two restrictions to the overlap agree after the chart maps (the pullback square). -/
theorem overlap_condition (i j : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom (toOverlapLeft k n i j)) ≫ coordinateChartMorphism k n i =
      Spec.map (CommRingCat.ofHom (toOverlapRight k n i j)) ≫ coordinateChartMorphism k n j := by
  rw [SpecMap_toOverlapLeft_chart, SpecMap_toOverlapRight_chart]

end KltDP.Geometry.ProjectiveChart
