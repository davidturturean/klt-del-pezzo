import KltDP.Geometry.KltMinimalResolutionAutomaticGeometry
import KltDP.Geometry.KltExceptionalOrthogonalPositive
import KltDP.Geometry.KltResolutionPicardRank
import KltDP.Geometry.KltResolutionNoetherRelation
import KltDP.Geometry.KltResolutionPicardCohomologyInvariants
import KltDP.Geometry.CanonicalWeilBirationalRepresentative
import KltDP.Geometry.RationalWeilIntersectionFamily
import KltDP.Geometry.MinimalResolutionExteriorDiscrepancy
import KltDP.Geometry.MinimalResolutionDiscrepancy
import KltDP.Geometry.KltOriginalDiscrepancyBound
import KltDP.Geometry.ActualExceptionalGraphMatrix
import KltDP.Geometry.ActualExceptionalStieltjes
import KltDP.Geometry.CompatibleRationalAdjunctionDegree
import KltDP.Geometry.MinimalExceptionalCanonicalDegree
import KltDP.Geometry.IntersectionPairingSymmetry
import KltDP.Geometry.DelPezzoType
import KltDP.Geometry.SevenPointHighCanonicalSquare

/-!
# The resolution datum `(S, D, L)` of a rank-one klt del Pezzo surface

Manuscript `source/manuscript.tex`, Conventions (lines 302–316): for a minimal
resolution `π : S → X` of a klt del Pezzo surface of Picard number one, the
triple `D = Exc(π)_red`, `L = π^*(-K_X)`, `v = L²` is the *resolution datum*,
and `K_S + Σ λ_i D_i = π^*K_X = -L` defines the discrepancy coefficients.

`ResolutionDatum` stores exactly the hypotheses of the main theorem: an actual
normal projective surface `X` with `IsKltDelPezzo X` and `X.picardRank = 1`, an
actual minimal resolution `π : S ⟶ X`. Nothing else is stored; every derived
object below is *constructed* from these (compatible canonical divisors are
chosen with `Classical.choose` from the accepted existence theorems), and every
property is a theorem of the compiled union.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Manuscript

/-- The hypotheses of the main theorem, packaged: an actual rank-one klt del Pezzo
surface `X` and an actual minimal resolution `π : S → X`. -/
structure ResolutionDatum (k : Type u) [Field k] [IsAlgClosed k] where
  S : NormalProjectiveSurface k
  X : NormalProjectiveSurface k
  π : S.toScheme ⟶ X.toScheme
  hmin : IsMinimalResolution S X π
  hDP : IsKltDelPezzo X
  hrank : X.picardRank = 1

namespace ResolutionDatum

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

/-- Regularity of every point of the resolution surface. -/
abbrev hreg : ∀ s : R.S.Point, RegularPoint R.S.toScheme s := R.hmin.regular

/-- The exceptional prime curves: the vertices of the exceptional dual graph. -/
abbrev Vertices := ActualExceptionalIncidence.Vertices R.π

/-- The exceptional dual graph (edges = nonempty intersections). -/
abbrev graph : SimpleGraph R.Vertices := ActualExceptionalIncidence.graph R.π

instance instFintypeVertices : Fintype R.Vertices :=
  R.hmin.toIsResolution.exceptionalCurves_finite_of_actualMap.fintype

instance instIsProper : IsProper R.π := R.hmin.toIsResolution.isProper

instance instSmooth : IsSmoothOfRelativeDimension 2 R.S.structureMorphism :=
  R.S.isSmoothOfRelativeDimension_two_of_regularPoints R.hreg

/-- Birationality of the resolution in the scheme-level form. -/
def hbir : IsBirationalScheme R.π :=
  (isBirational_iff_isBirationalScheme R.π).mp R.hmin.birational

instance instGenericPointPreserving : GenericPointPreserving R.π := ⟨R.hbir.map_genericPoint⟩

/-- The del Pezzo hypothesis unpacked: an actual canonical Weil divisor of `X` with the
klt property whose negative is `ℚ`-ample. -/
theorem exists_canonical :
    ∃ KX : R.X.WeilDivisor, IsKltWithCanonicalDivisor R.X KX ∧
      R.X.QAmple (-rationalizeWeilDivisor R.X KX) :=
  (isLogDelPezzoPair_zero_iff R.X).mp R.hDP

/-- A chosen klt canonical Weil divisor of `X`. -/
def KX : R.X.WeilDivisor := Classical.choose R.exists_canonical

theorem KX_klt : IsKltWithCanonicalDivisor R.X R.KX :=
  (Classical.choose_spec R.exists_canonical).1

theorem KX_qAmple : R.X.QAmple (-rationalizeWeilDivisor R.X R.KX) :=
  (Classical.choose_spec R.exists_canonical).2

theorem hklt : IsKlt R.X := ⟨R.KX, R.KX_klt⟩

theorem KX_qCartier : R.X.QCartier (rationalizeWeilDivisor R.X R.KX) := R.KX_klt.2.1

/-- A compatible canonical Cartier divisor on `S`: its divisor sheaf is the canonical
sheaf and its pushforward is the chosen `K_X`. -/
theorem exists_KS :
    ∃ KS : CartierDivisor R.S.toScheme,
      Nonempty (cartierDivisorModule R.S.toScheme KS ≅
        SmoothCanonicalExteriorComparison.relativeDifferentialExterior R.S.structureMorphism 2) ∧
      BirationalWeilPushforward.pushforward R.π R.hbir (R.S.cartierToWeilHom KS) = R.KX :=
  IsCanonicalWeilDivisor.exists_compatible_canonical_cartier R.S R.X R.π R.hmin.over_base
    R.hbir R.KX R.KX_klt.1

/-- The chosen compatible canonical Cartier divisor `K_S`. -/
def KS : CartierDivisor R.S.toScheme := Classical.choose R.exists_KS

theorem KS_canonical :
    Nonempty (cartierDivisorModule R.S.toScheme R.KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior R.S.structureMorphism 2) :=
  (Classical.choose_spec R.exists_KS).1

theorem KS_push :
    BirationalWeilPushforward.pushforward R.π R.hbir (R.S.cartierToWeilHom R.KS) = R.KX :=
  (Classical.choose_spec R.exists_KS).2

/-- The chosen canonical isomorphism (an explicit witness). -/
def eKS : cartierDivisorModule R.S.toScheme R.KS ≅
    SmoothCanonicalExteriorComparison.relativeDifferentialExterior R.S.structureMorphism 2 :=
  Classical.choice R.KS_canonical

/-- The pullback `π^*K_X` as a rational Weil divisor on `S`. -/
def pullbackKX : R.S.RationalWeilDivisor :=
  QCartierPullback.pullback R.π (rationalizeWeilDivisor R.X R.KX) R.KX_qCartier

/-- `L = π^*(-K_X)` as a rational Weil divisor on `S`. -/
def Lweil : R.S.RationalWeilDivisor := -R.pullbackKX

/-- The discrepancy divisor `K_S - π^*K_X = K_S + L` (rational Weil divisor on `S`). -/
def Δ : R.S.RationalWeilDivisor := R.S.rationalCartierToWeilHom R.KS - R.pullbackKX

theorem KS_add_Lweil : R.S.rationalCartierToWeilHom R.KS + R.Lweil = R.Δ := by
  simp only [Lweil, Δ, sub_eq_add_neg]

/-- Exceptional curves are rational (`≅ P¹`). -/
theorem exceptional_rational (C : R.S.PrimeCurve) (hC : IsExceptionalCurve R.π C) :
    ∃ e : C.toScheme ≅ projectiveSpace k 1, e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec :=
  R.hmin.toIsResolution.exceptional_projectiveLine_iso_of_klt R.hklt C hC

/-- Discrepancy coefficients are nonpositive (minimality). -/
theorem Δ_nonpos (C : R.S.PrimeCurve) : R.Δ C ≤ 0 :=
  MinimalResolutionDiscrepancy.coefficient_nonpos R.S R.X R.π R.hmin R.KS R.eKS R.KX
    R.KX_qCartier R.exceptional_rational R.KS_push C

/-- Discrepancy coefficients are greater than `-1` (klt). -/
theorem Δ_gt_neg_one (C : R.S.PrimeCurve) : -1 < R.Δ C :=
  KltOriginalDiscrepancyBound.coefficient_gt_neg_one R.S R.X R.π R.hbir R.hmin.over_base
    R.KS R.eKS R.KX R.KX_klt R.KS_push C

/-- The discrepancy coefficient `λ_i ≥ 0` of an exceptional curve (the manuscript's `λ_i`). -/
def lam (i : R.Vertices) : ℚ := -R.Δ i.val

theorem lam_nonneg (i : R.Vertices) : 0 ≤ R.lam i := by
  have := R.Δ_nonpos i.val
  simp only [lam]; linarith

theorem lam_lt_one (i : R.Vertices) : R.lam i < 1 := by
  have := R.Δ_gt_neg_one i.val
  simp only [lam]; linarith

/-- The intersection matrix `(D_i · D_j)` of the exceptional curves (rational entries). -/
def M : Matrix R.Vertices R.Vertices ℚ :=
  NullCurveIntersectionMatrix.intersectionMatrix R.S R.hreg (fun i : R.Vertices => i.val)

/-- The weights `b_i = -D_i²`. -/
def w (i : R.Vertices) : ℚ := -R.M i i

/-- The negative intersection matrix `A = -(D_i · D_j)` (positive definite). -/
def A : Matrix R.Vertices R.Vertices ℚ := -R.M

/-- The canonical-degree vector `q_i = b_i - 2 = K_S · D_i`. -/
def q (i : R.Vertices) : ℚ := R.w i - 2

theorem A_posDef : R.A.PosDef :=
  ActualExceptionalStieltjes.negativeIntersectionMatrix_posDef R.π R.hmin.over_base R.hbir
    R.hreg (fun i : R.Vertices => i.val) Subtype.val_injective (fun E => E.property)

theorem two_le_w (i : R.Vertices) : 2 ≤ R.w i := by
  obtain ⟨e, he⟩ := R.exceptional_rational i.val i.property
  have hneg := R.hmin.rational_exceptional_selfIntersection_le_neg_two i.val i.property e he
  change (2 : ℚ) ≤ -(R.S.intersectionPairing R.hreg
    (R.S.primeCurveCartier R.hreg i.val) (R.S.primeCurveCartier R.hreg i.val) : ℚ)
  rw [R.S.intersectionPairing_primeCurve R.hreg]
  exact_mod_cast (by omega : (2 : ℤ) ≤ -(i.val).selfIntersectionNumber R.hreg)

theorem Δ_gt_neg_one' (i : R.Vertices) : -1 < R.Δ i.val := R.Δ_gt_neg_one i.val
theorem Δ_nonpos' (i : R.Vertices) : R.Δ i.val ≤ 0 := R.Δ_nonpos i.val

/-- The row equations `(D_i · D_j) Δ_j = b_i - 2` for the discrepancy divisor. -/
theorem M_mulVec_Δ : R.M *ᵥ (fun j : R.Vertices => R.Δ j.val) = fun i => R.w i - 2 := by
  funext i
  have hri := RationalWeilIntersection.intersectionMatrix_mulVec_compatible_difference
    R.hreg R.π R.hbir R.hmin.over_base R.KS R.KX R.KX_qCartier R.KS_push
    (fun i : R.Vertices => i.val) Subtype.val_injective (fun E => E.property)
    (fun E hE => ⟨⟨E, hE⟩, rfl⟩) i
  obtain ⟨e, he⟩ := R.exceptional_rational i.val i.property
  have hadj := CompatibleRationalAdjunctionDegree.canonical_intersection_eq
    R.S R.hreg R.KS R.eKS i.val e he
  change (NullCurveIntersectionMatrix.intersectionMatrix R.S R.hreg
      (fun i : R.Vertices => i.val) *ᵥ (fun j : R.Vertices =>
        (R.S.rationalCartierToWeilHom R.KS - QCartierPullback.pullback R.π
          (rationalizeWeilDivisor R.X R.KX) R.KX_qCartier) j.val)) i =
    -NullCurveIntersectionMatrix.intersectionMatrix R.S R.hreg
      (fun i : R.Vertices => i.val) i i - 2
  rw [hri]
  change ((i.val).intersectionNumber R.KS : ℚ) =
    -(R.S.intersectionPairing R.hreg
      (R.S.primeCurveCartier R.hreg i.val) (R.S.primeCurveCartier R.hreg i.val) : ℚ) - 2
  rw [R.S.intersectionPairing_primeCurve R.hreg]
  exact_mod_cast hadj

/-- The discrepancy equation `A λ = q`. -/
theorem A_mulVec_lam : R.A *ᵥ R.lam = R.q := by
  have h := R.M_mulVec_Δ
  have hlam : R.lam = -(fun j : R.Vertices => R.Δ j.val) := rfl
  funext i
  have hi := congrFun h i
  simp only [A, q, hlam, Matrix.neg_mulVec, Matrix.mulVec_neg, Pi.neg_apply, neg_neg]
  exact hi

/-- Distinct exceptional curves have nonnegative intersection number (they are distinct
prime curves), so the off-diagonal entries of `M` are nonnegative. -/
theorem M_offDiag_nonneg (i j : R.Vertices) (hij : i ≠ j) : 0 ≤ R.M i j := by
  have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  change (0 : ℚ) ≤ (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
    (R.S.primeCurveCartier R.hreg j.val) : ℚ)
  exact_mod_cast KltDP.Geometry.PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg R.S R.hreg i.val j.val hne

theorem A_offDiag_nonpos (i j : R.Vertices) (hij : i ≠ j) : R.A i j ≤ 0 := by
  have := R.M_offDiag_nonneg i j hij
  simp only [A, Matrix.neg_apply]; linarith

theorem A_diag (i : R.Vertices) : R.A i i = R.w i := rfl

/-- `A` is the weight matrix of the exceptional dual graph: diagonal `b_i`, entries `-1` on
edges, `0` otherwise (for any decidability instances). -/
theorem A_eq_graphWeightMatrix [DecidableEq R.Vertices] [DecidableRel R.graph.Adj] :
    R.A = KltDP.LinearAlgebra.graphWeightMatrix R.graph R.w := by
  haveI : DecidableRel (curveIncidenceGraph fun i : R.Vertices => i.val).Adj := Classical.decRel _
  have h := ActualExceptionalGraphMatrix.negativeIntersectionMatrix_eq_graphWeightMatrix
    R.π R.hmin.over_base R.hbir R.hreg (fun i : R.Vertices => i.val) Subtype.val_injective
    (fun E => E.property) (fun j => R.Δ j.val) R.Δ_gt_neg_one' R.Δ_nonpos' R.M_mulVec_Δ
  convert h using 2

end ResolutionDatum

end KltDP.Manuscript
