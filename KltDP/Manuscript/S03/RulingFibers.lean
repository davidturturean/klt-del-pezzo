import KltDP.Manuscript.S03.PrimitiveSquareZero
import KltDP.Geometry.ArithmeticCurveAdjunction
import KltDP.Geometry.GenusZeroCurveProjectiveLineIso
import KltDP.Geometry.NumericalIsotropicNonnegative
import KltDP.Geometry.NullCurveNumericalSpan
import KltDP.Geometry.PrimeCurvePairingSupport
import KltDP.Geometry.MinimalResolutionCount
import KltDP.Geometry.PrimeCurveCodimension
import KltDP.Geometry.KltSquareZeroPencilStein
import KltDP.Geometry.CurveIncidenceGraph
import KltDP.Geometry.NullCurveIntersectionMatrix
import KltDP.Geometry.SurfaceNumericalFinitenessProved
import KltDP.Geometry.AmpleCurveRestrictionPositive

/-!
# Manuscript Lemma 3.2: the fibres of a primitive rational ruling

Source: `source/manuscript.tex`, lines 714–753, `lem:ruling-fibers`, for the pencil
`g : S ⟶ P¹` of Lemma 3.1 (`PrimitiveSquareZero.lean`) on the resolution surface of a
resolution datum `R`, with fibre class `F` (`F² = 0`, `K_S · F = -2`, hence primitive).

Vocabulary. `InFiber g t C` says that the prime curve `C` lies in the fibre over `t`
(`C ⊆ g⁻¹(t)`). `IsFiberDivisor F g t E` records the three properties of the scheme-theoretic
fibre divisor `E = g^*(t)` established in `exists_closedFiberDivisor`: `O(E) ≅ O(F)` in
`Pic S`, `E` is effective, and its Weil support is the point-set fibre. The multiplicity
`μ_C` of a component is the Weil coefficient `R.S.cartierToWeilHom E C`.

Results (clauses (i)–(ii) of the lemma, TeX 731–738):

* `fiber_isConnected`: every fibre is connected (Stein factorisation of the union);
* `coeff_pos_of_inFiber` / `inFiber_of_coeff_ne_zero`: `C ⊆ g⁻¹(t)` iff `μ_C > 0`;
* `fiber_intersection_eq`, `fiber_canonical_sum`: the fibre intersection equation
  `F · C = Σ μ_{C'} (C · C')` and the adjunction sum `Σ μ_C (K_S · C) = -2`;
* `irreducibleFiber_component`: an irreducible fibre is reduced (`E = C`, by primitivity) and
  its component is a smooth rational curve with `C² = 0`, `K_S · C = -2` (arithmetic genus
  zero, adjunction);
* `selfIntersection_neg_of_reducible`: every component of a reducible fibre has `C² < 0`
  (isotropic Hodge lemma against a meeting component supplied by connectedness);
* `isMinusOneCurve_of_reducible_of_negative_canonical`,
  `exists_minusOneCurve_of_reducible`: a component of a reducible fibre with `K_S · C < 0` is a
  `(-1)`-curve, and every reducible fibre contains one (from the adjunction sum).

Clause (iv), the count `ρ(S) = 2 + Σ_t (n_t - 1)`, is proved as the **lower bound**
`2 + Σ_{t ∈ T} (n_t - 1) ≤ ρ(S)` for every finite set `T` of closed points
(`picardRank_lower_bound`, `rulingFibers_picardRank_lower_bound`): the classes `[F]`, an ample
class and the components of the fibres over `T` minus one component per fibre are linearly
independent in `N¹(S)_ℚ`. The key input is Zariski's lemma in matrix form
(`kernel_eq_smul_of_connected`, `exists_smul_multiplicity_of_mulVec_eq_zero`): on a connected
fibre the only relations `Σ y_C [C] ⊥ every component` are the multiples of the multiplicity
vector `(μ_C)`. As a corollary only finitely many fibres are reducible, at most `ρ(S) - 2`
(`reducibleFibers_finite`). The reverse inequality (the equality, via the factorisation to a
Hirzebruch surface) and the SNC-tree structure of the reduced fibres (clause (iii)) are not
proved here.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript Matrix

universe u v

namespace KltDP.Manuscript.S03

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance projectiveLineIntegral' : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- `C ⊆ g⁻¹(t)`: the prime curve `C` is a component of the fibre of `g` over `t`. -/
abbrev InFiber {R : ResolutionDatum k} (g : R.S.toScheme ⟶ projectiveSpace k 1)
    (t : projectiveSpace k 1) (C : R.S.PrimeCurve) : Prop :=
  ∀ x ∈ (C : Set R.S.toScheme), g.base x = t

/-- `E` is the fibre divisor of the pencil over `t`: the three properties of the scheme-theoretic
fibre `g^*(t)` proved in `exists_closedFiberDivisor` — its Picard class is the fibre class `F`,
it is effective, and its geometric Weil support is the point-set fibre `g⁻¹(t)`. -/
structure IsFiberDivisor {R : ResolutionDatum k} (F : CartierDivisor R.S.toScheme)
    (g : R.S.toScheme ⟶ projectiveSpace k 1) (t : projectiveSpace k 1)
    (E : CartierDivisor R.S.toScheme) : Prop where
  class_eq : cartierPicardClass R.S.toScheme E = cartierPicardClass R.S.toScheme F
  effective : EffectiveDivisor (R.S.cartierToWeilHom E)
  support_eq : divisorSupport (R.S.cartierToWeilHom E) = g.base ⁻¹' {t}

variable (R : ResolutionDatum k) (p : ℕ) [CharP k p] (hp : 0 < p)
  (F : CartierDivisor R.S.toScheme)
  (hFF : R.S.intersectionPairing R.hreg F F = 0)
  (hKF : R.S.intersectionPairing R.hreg R.KS F = -2)
  (g : R.S.toScheme ⟶ projectiveSpace k 1)
  (hg : g ≫ projectiveSpaceToSpec k 1 = R.S.structureMorphism)
  (e : (pullbackInvertibleSheaf g (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
    cartierDivisorModule R.S.toScheme F)

/-! ### Fibre divisors and their components -/

include e in
/-- Every closed fibre has a fibre divisor (`exists_closedFiberDivisor`). -/
theorem exists_isFiberDivisor [IsProper g] [Surjective g] (t : projectiveSpace k 1)
    (ht : IsClosed ({t} : Set (projectiveSpace k 1))) :
    ∃ E : CartierDivisor R.S.toScheme, IsFiberDivisor F g t E := by
  obtain ⟨E, -, -, hcls, heff, hsupp, -⟩ := exists_closedFiberDivisor R F g e t ht
  exact ⟨E, hcls, heff, hsupp⟩

include hp hFF hKF hg e in
/-- **Fibres are connected** (TeX 707–712, Stein factorisation): the point-set fibre over every
point of `P¹` is connected and nonempty. -/
theorem fiber_isConnected [IsProper g] [Surjective g] (t : projectiveSpace k 1) :
    IsConnected (g.base ⁻¹' {t}) := by
  obtain ⟨-, hconn⟩ := KltSquareZeroPencilStein.structureSheaf_iso_and_geometrically_connected
    R.π R.hmin R.hDP R.hrank p hp R.KS R.eKS F hFF hKF g hg e
  exact GeometricConnectedFiberTopology.isConnected_preimage_singleton g hconn t

/-- A prime curve with nonzero multiplicity in the fibre divisor lies in the fibre. -/
theorem inFiber_of_coeff_ne_zero {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) (C : R.S.PrimeCurve) (h : R.S.cartierToWeilHom E C ≠ 0) :
    InFiber g t C := by
  intro x hx
  have hmem := primeCurve_subset_divisorSupport (R.S.cartierToWeilHom E) h hx
  rw [hE.support_eq] at hmem
  exact hmem

/-- A prime curve in the fibre has positive multiplicity in the fibre divisor: it is one of the
finitely many curves of the Weil support (irreducibility of `C`). -/
theorem coeff_pos_of_inFiber {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) (C : R.S.PrimeCurve) (hC : InFiber g t C) :
    0 < R.S.cartierToWeilHom E C := by
  classical
  let T : Finset (Set R.S.toScheme) :=
    (R.S.cartierToWeilHom E).support.image (fun C' : R.S.PrimeCurve => (C' : Set R.S.toScheme))
  have hclosed : ∀ z ∈ T, IsClosed z := by
    intro z hz
    obtain ⟨C', -, rfl⟩ := Finset.mem_image.mp hz
    exact C'.isClosed
  have hsub : (C : Set R.S.toScheme) ⊆ ⋃₀ (T : Set (Set R.S.toScheme)) := by
    intro x hx
    have hxΦ : x ∈ g.base ⁻¹' {t} := hC x hx
    rw [← hE.support_eq, mem_divisorSupport] at hxΦ
    obtain ⟨C', hC', hxC'⟩ := hxΦ
    exact ⟨(C' : Set R.S.toScheme),
      Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨C', Finsupp.mem_support_iff.mpr hC', rfl⟩), hxC'⟩
  obtain ⟨z, hzT, hCz⟩ := (isIrreducible_iff_sUnion_isClosed.mp C.isIrreducible) T hclosed hsub
  obtain ⟨C', hC'supp, rfl⟩ := Finset.mem_image.mp hzT
  have heq : C = C' :=
    PrimeCurve.ext (C.coe_eq_of_subset_irreducibleCloseds C'.1 hCz C'.ne_univ)
  rw [heq]
  exact lt_of_le_of_ne (hE.effective C') (Ne.symm (Finsupp.mem_support_iff.mp hC'supp))

/-- `C ⊆ g⁻¹(t)` if and only if the multiplicity `μ_C` is positive. -/
theorem inFiber_iff_coeff_pos {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) (C : R.S.PrimeCurve) :
    InFiber g t C ↔ 0 < R.S.cartierToWeilHom E C :=
  ⟨coeff_pos_of_inFiber R F g hE C, fun h => inFiber_of_coeff_ne_zero R F g hE C (ne_of_gt h)⟩

/-- **The fibre intersection equation**: `F · C = Σ_{C'} μ_{C'} (C · C')` for every prime curve
`C`, the sum running over the components of the fibre divisor. -/
theorem fiber_intersection_eq {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) (C : R.S.PrimeCurve) :
    C.intersectionNumber F = (R.S.cartierToWeilHom E).sum
      fun C' a => a * C.intersectionNumber (R.S.primeCurveCartier R.hreg C') := by
  rw [C.intersectionNumber_eq_of_cartierPicardClass_eq F E hE.class_eq.symm]
  exact R.S.intersectionNumber_eq_weil_sum R.hreg C E

include hKF in
/-- **Adjunction against the fibre** (TeX 735–736): `-2 = K_S · F = Σ_C μ_C (K_S · C)`. -/
theorem fiber_canonical_sum {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) :
    ((R.S.cartierToWeilHom E).sum fun C a => a * C.intersectionNumber R.KS) = -2 := by
  rw [← R.S.intersectionPairing_eq_weil_sum_right R.hreg E R.KS,
    R.S.intersectionPairing_symm R.hreg,
    R.S.intersectionPairing_eq_of_class_eq_right R.hreg R.KS E F hE.class_eq, hKF]

include hKF in
/-- Every fibre contains a component of negative canonical degree (TeX 736–737). -/
theorem exists_negative_canonical_component {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E) :
    ∃ C : R.S.PrimeCurve, InFiber g t C ∧ C.intersectionNumber R.KS < 0 := by
  by_contra hnone
  push_neg at hnone
  have hsum := fiber_canonical_sum R F hKF g hE
  have hnonneg : 0 ≤ (R.S.cartierToWeilHom E).sum
      fun C a => a * C.intersectionNumber R.KS := by
    unfold Finsupp.sum
    apply Finset.sum_nonneg
    intro C hC
    exact mul_nonneg (hE.effective C)
      (hnone C (inFiber_of_coeff_ne_zero R F g hE C (Finsupp.mem_support_iff.mp hC)))
  linarith

/-! ### Irreducible fibres are reduced smooth rational curves -/

include hFF hKF in
/-- **Primitivity makes an irreducible fibre reduced** (TeX 732–733): if `C` is the only
component of the fibre over `t`, then the fibre divisor is `E = C` (`μ_C = 1`). -/
theorem fiberDivisor_eq_primeCurveCartier_of_irreducible {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (C : R.S.PrimeCurve) (hC : InFiber g t C) (hirr : ∀ C', InFiber g t C' → C' = C) :
    E = R.S.primeCurveCartier R.hreg C ∧ R.S.cartierToWeilHom E = Finsupp.single C 1 := by
  classical
  have hμpos : 0 < R.S.cartierToWeilHom E C := coeff_pos_of_inFiber R F g hE C hC
  have hweil : R.S.cartierToWeilHom E = Finsupp.single C (R.S.cartierToWeilHom E C) := by
    ext C'
    rw [Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · by_contra hne
      exact h (hirr C' (inFiber_of_coeff_ne_zero R F g hE C' hne)).symm
  have hcart : E = (R.S.cartierToWeilHom E C) • R.S.primeCurveCartier R.hreg C := by
    apply (R.S.regularCartierWeilEquiv R.hreg).injective
    rw [map_zsmul, R.S.regularCartierWeilEquiv_apply, R.S.regularCartierWeilEquiv_apply,
      R.S.cartierToWeilHom_primeCurveCartier, Finsupp.smul_single', mul_one]
    exact hweil
  have hone : R.S.cartierToWeilHom E C = 1 := by
    by_contra hne
    have h1 : 1 < R.S.cartierToWeilHom E C := by omega
    apply primitiveSquareZero_primitive R F hFF hKF _ h1
      (cartierPicardHom R.S.toScheme (R.S.primeCurveCartier R.hreg C))
    rw [← map_zsmul, ← hcart]
    exact congrArg Additive.ofMul hE.class_eq
  rw [hone] at hcart hweil
  rw [one_smul] at hcart
  exact ⟨hcart, hweil⟩

include hFF hKF in
/-- **Irreducible fibres** (TeX 732–734): if `C` is the only component of the fibre over `t`,
then the fibre is reduced (`g^*(t) = C`), `F · C = 0`, `C² = 0`, `K_S · C = -2`, `C` has
arithmetic genus zero and is a smooth rational curve (`C ≅ P¹` over `k`). -/
theorem irreducibleFiber_component {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (C : R.S.PrimeCurve) (hC : InFiber g t C) (hirr : ∀ C', InFiber g t C' → C' = C) :
    R.S.cartierToWeilHom E = Finsupp.single C 1 ∧
      C.intersectionNumber F = 0 ∧
      C.selfIntersectionNumber R.hreg = 0 ∧
      C.intersectionNumber R.KS = -2 ∧
      CurveCanonical.genus C.toSpec = 0 ∧
      ∃ e : C.toScheme ≅ projectiveSpace k 1, e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec := by
  obtain ⟨hEC, hweil⟩ :=
    fiberDivisor_eq_primeCurveCartier_of_irreducible R F hFF hKF g hE C hC hirr
  have hclass : cartierPicardClass R.S.toScheme (R.S.primeCurveCartier R.hreg C) =
      cartierPicardClass R.S.toScheme F := by
    rw [← hEC]
    exact hE.class_eq
  have hCF : C.intersectionNumber F = 0 := by
    rw [← R.S.intersectionPairing_primeCurve R.hreg F C,
      R.S.intersectionPairing_eq_of_class_eq_right R.hreg F _ F hclass, hFF]
  have hself : C.selfIntersectionNumber R.hreg = 0 := by
    change C.intersectionNumber (R.S.primeCurveCartier R.hreg C) = 0
    rw [C.intersectionNumber_eq_of_cartierPicardClass_eq _ F hclass]
    exact hCF
  have hK : C.intersectionNumber R.KS = -2 := by
    rw [← R.S.intersectionPairing_primeCurve R.hreg R.KS C,
      R.S.intersectionPairing_eq_of_class_eq_right R.hreg R.KS _ F hclass, hKF]
  have hgenus : CurveCanonical.genus C.toSpec = 0 := by
    have hrow := R.S.arithmetic_canonical_row R.hreg R.KS R.eKS C
    rw [hK, hself] at hrow
    omega
  letI : IsProper C.toSpec := C.toSpec_isProper
  exact ⟨hweil, hCF, hself, hK, hgenus,
    GenusZeroCurveProjectiveLineIso.exists_iso C.toSpec C.dimension_one_toScheme hgenus⟩

/-! ### Reducible fibres: negative components and `(-1)`-curves -/

/-- In a connected reducible fibre every component `C` meets another component: with
`U = ⋃_{C'' ≠ C} C''`, the closed cover `g⁻¹(t) = C ∪ U` of the connected fibre cannot be
disjoint. -/
theorem exists_meeting_component {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) (hconn : IsConnected (g.base ⁻¹' {t}))
    (C : R.S.PrimeCurve) (hC : InFiber g t C)
    (C' : R.S.PrimeCurve) (hC' : InFiber g t C') (hne : C' ≠ C) :
    ∃ C'' : R.S.PrimeCurve, InFiber g t C'' ∧ C'' ≠ C ∧
      ((C : Set R.S.toScheme) ∩ C'').Nonempty := by
  classical
  by_contra hnone
  push_neg at hnone
  let T : Finset (Set R.S.toScheme) :=
    ((R.S.cartierToWeilHom E).support.erase C).image
      (fun C'' : R.S.PrimeCurve => (C'' : Set R.S.toScheme))
  let U : Set R.S.toScheme := ⋃₀ (T : Set (Set R.S.toScheme))
  have hT : ∀ z ∈ T, IsClosed z := by
    intro z hz
    obtain ⟨C'', -, rfl⟩ := Finset.mem_image.mp hz
    exact C''.isClosed
  have hU : IsClosed U := by
    have hb := Set.Finite.isClosed_biUnion T.finite_toSet (fun z hz => hT z hz)
    rwa [← Set.sUnion_eq_biUnion] at hb
  have hcover : g.base ⁻¹' {t} ⊆ (C : Set R.S.toScheme) ∪ U := by
    intro x hx
    rw [← hE.support_eq, mem_divisorSupport] at hx
    obtain ⟨C'', hC'', hxC''⟩ := hx
    by_cases h : C'' = C
    · left
      rw [← h]
      exact hxC''
    · right
      exact ⟨(C'' : Set R.S.toScheme), Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨C'', Finset.mem_erase.mpr ⟨h, Finsupp.mem_support_iff.mpr hC''⟩, rfl⟩), hxC''⟩
  have hdisj : g.base ⁻¹' {t} ∩ ((C : Set R.S.toScheme) ∩ U) = ∅ := by
    ext x
    refine ⟨?_, fun h => h.elim⟩
    rintro ⟨-, hxC, hxU⟩
    obtain ⟨z, hzT, hxz⟩ := Set.mem_sUnion.mp hxU
    obtain ⟨C'', hC''mem, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hzT)
    obtain ⟨hC''ne, hC''supp⟩ := Finset.mem_erase.mp hC''mem
    have hin : InFiber g t C'' :=
      inFiber_of_coeff_ne_zero R F g hE C'' (Finsupp.mem_support_iff.mp hC''supp)
    have hempty := hnone C'' hin hC''ne
    have hx' : x ∈ (C : Set R.S.toScheme) ∩ C'' := ⟨hxC, hxz⟩
    rw [hempty] at hx'
    exact hx'
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn.isPreconnected
    (C : Set R.S.toScheme) U C.isClosed hU hcover hdisj with hsubC | hsubU
  · have hC'sub : (C' : Set R.S.toScheme) ⊆ C := fun x hx => hsubC (hC' x hx)
    exact hne (PrimeCurve.ext (C'.coe_eq_of_subset_irreducibleCloseds C.1 hC'sub C.ne_univ))
  · have hCsub : (C : Set R.S.toScheme) ⊆ U := fun x hx => hsubU (hC x hx)
    obtain ⟨z, hzT, hCz⟩ := (isIrreducible_iff_sUnion_isClosed.mp C.isIrreducible) T hT hCsub
    obtain ⟨C'', hC''mem, rfl⟩ := Finset.mem_image.mp hzT
    exact (Finset.mem_erase.mp hC''mem).1
      (PrimeCurve.ext (C.coe_eq_of_subset_irreducibleCloseds C''.1 hCz C''.ne_univ)).symm

include hFF hKF hg e in
/-- **Components of reducible fibres have negative square** (TeX 734–735): if the connected
fibre over `t` contains two distinct components, every component `C` satisfies `C² < 0`.
(If `C² ≥ 0`, the isotropic Hodge lemma makes `[C]` proportional to `[F]`, which is orthogonal
to every vertical curve, contradicting `C · C'' > 0` for a meeting component `C''`.) -/
theorem selfIntersection_neg_of_reducible {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (hconn : IsConnected (g.base ⁻¹' {t}))
    (C : R.S.PrimeCurve) (hC : InFiber g t C)
    (C' : R.S.PrimeCurve) (hC' : InFiber g t C') (hne : C' ≠ C) :
    C.selfIntersectionNumber R.hreg < 0 := by
  obtain ⟨C'', hC'', hne'', x, hxC, hxC''⟩ :=
    exists_meeting_component R F g hE hconn C hC C' hC' hne
  by_contra hnonneg
  push_neg at hnonneg
  have hne0 : NefNullCurveNegativeSquare.cartierClass R.S F ≠ 0 := by
    intro h0
    have hpair := NefNullCurveNegativeSquare.cartierClass_pairing R.S R.hreg R.KS F
    rw [h0, map_zero, hKF] at hpair
    norm_num at hpair
  have hFF' : R.S.numericalIntersectionBilinForm R.hreg
      (NefNullCurveNegativeSquare.cartierClass R.S F)
      (NefNullCurveNegativeSquare.cartierClass R.S F) = 0 := by
    rw [NefNullCurveNegativeSquare.cartierClass_pairing, hFF, Int.cast_zero]
  have hCC : 0 ≤ R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C) := by
    rw [DisjointNegativeCurvesRank.curveClass_self]
    exact_mod_cast hnonneg
  have hFC : R.S.numericalIntersectionBilinForm R.hreg
      (NefNullCurveNegativeSquare.cartierClass R.S F)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C) = 0 := by
    rw [NullCurveNumericalSpan.cartierClass_curveClass,
      intersectionNumber_eq_zero_of_vertical R F g hg e C t hC, Int.cast_zero]
  have hFC'' : R.S.numericalIntersectionBilinForm R.hreg
      (NefNullCurveNegativeSquare.cartierClass R.S F)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C'') = 0 := by
    rw [NullCurveNumericalSpan.cartierClass_curveClass,
      intersectionNumber_eq_zero_of_vertical R F g hg e C'' t hC'', Int.cast_zero]
  obtain ⟨a, ha⟩ := NumericalIsotropicHodge.exists_smul_eq_of_nonneg R.S R.hreg
    (NefNullCurveNegativeSquare.cartierClass R.S F)
    (DisjointNegativeCurvesRank.curveClass R.S R.hreg C) hne0 hFF' hCC hFC
  have hmeet : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C'') ≠ 0 := by
    rw [DisjointNegativeCurvesRank.curveClass_pairing]
    intro h
    have h' : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg C)
        (R.S.primeCurveCartier R.hreg C'') = 0 := by exact_mod_cast h
    exact (Set.not_disjoint_iff.mpr ⟨x, hxC, hxC''⟩)
      ((PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
        R.S R.hreg C C'' hne''.symm).mp h')
  apply hmeet
  rw [ha, LinearMap.BilinForm.smul_left, hFC'', mul_zero]

include hFF hKF hg e in
/-- A vertical curve of nonnegative square is a whole (irreducible) fibre. -/
theorem irreducible_of_selfIntersection_nonneg {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (hconn : IsConnected (g.base ⁻¹' {t}))
    (C : R.S.PrimeCurve) (hC : InFiber g t C) (hsq : 0 ≤ C.selfIntersectionNumber R.hreg) :
    ∀ C', InFiber g t C' → C' = C := by
  intro C' hC'
  by_contra hne
  exact absurd hsq (not_le.mpr
    (selfIntersection_neg_of_reducible R F hFF hKF g hg e hE hconn C hC C' hC' hne))

include hFF hKF hg e in
/-- **Adjunction on a reducible fibre** (TeX 736–738): a component `C` of a reducible fibre with
`K_S · C < 0` is a smooth rational `(-1)`-curve, and then `K_S · C = -1`. -/
theorem isMinusOneCurve_of_reducible_of_negative_canonical {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (hconn : IsConnected (g.base ⁻¹' {t}))
    (C : R.S.PrimeCurve) (hC : InFiber g t C)
    (C' : R.S.PrimeCurve) (hC' : InFiber g t C') (hne : C' ≠ C)
    (hneg : C.intersectionNumber R.KS < 0) :
    IsMinusOneCurve R.hreg C ∧ C.intersectionNumber R.KS = -1 := by
  have hsq := selfIntersection_neg_of_reducible R F hFF hKF g hg e hE hconn C hC C' hC' hne
  have hrow := R.S.arithmetic_canonical_row R.hreg R.KS R.eKS C
  have hgenus : CurveCanonical.genus C.toSpec = 0 := by omega
  have hself : C.selfIntersectionNumber R.hreg = -1 := by omega
  letI : IsProper C.toSpec := C.toSpec_isProper
  exact ⟨⟨GenusZeroCurveProjectiveLineIso.exists_iso C.toSpec C.dimension_one_toScheme hgenus,
    hself⟩, by omega⟩

include hFF hKF hg e in
/-- **Every reducible fibre contains a vertical `(-1)`-curve** (TeX 735–738). -/
theorem exists_minusOneCurve_of_reducible {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (hconn : IsConnected (g.base ⁻¹' {t}))
    (C : R.S.PrimeCurve) (hC : InFiber g t C)
    (C' : R.S.PrimeCurve) (hC' : InFiber g t C') (hne : C' ≠ C) :
    ∃ C₀ : R.S.PrimeCurve, InFiber g t C₀ ∧ IsMinusOneCurve R.hreg C₀ ∧
      C₀.intersectionNumber R.KS = -1 := by
  obtain ⟨C₀, hC₀, hneg⟩ := exists_negative_canonical_component R F hKF g hE
  by_cases h : C₀ = C
  · subst h
    obtain ⟨hm, hK⟩ := isMinusOneCurve_of_reducible_of_negative_canonical
      R F hFF hKF g hg e hE hconn C₀ hC₀ C' hC' hne hneg
    exact ⟨C₀, hC₀, hm, hK⟩
  · obtain ⟨hm, hK⟩ := isMinusOneCurve_of_reducible_of_negative_canonical
      R F hFF hKF g hg e hE hconn C₀ hC₀ C hC (fun h' => h h'.symm)
      hneg
    exact ⟨C₀, hC₀, hm, hK⟩

/-! ### The same, with connectedness supplied by the datum -/

include hp hFF hKF hg e in
/-- Lemma 3.2 (i), reducible case, in the datum: components of reducible fibres have negative
square. -/
theorem rulingFibers_selfIntersection_neg [IsProper g] [Surjective g] (t : projectiveSpace k 1)
    (E : CartierDivisor R.S.toScheme) (hE : IsFiberDivisor F g t E)
    (C : R.S.PrimeCurve) (hC : InFiber g t C)
    (C' : R.S.PrimeCurve) (hC' : InFiber g t C') (hne : C' ≠ C) :
    C.selfIntersectionNumber R.hreg < 0 :=
  selfIntersection_neg_of_reducible R F hFF hKF g hg e hE
    (fiber_isConnected R p hp F hFF hKF g hg e t) C hC C' hC' hne

include hp hFF hKF hg e in
/-- Lemma 3.2 (ii) in the datum: every reducible fibre contains a vertical `(-1)`-curve. -/
theorem rulingFibers_exists_minusOneCurve [IsProper g] [Surjective g] (t : projectiveSpace k 1)
    (E : CartierDivisor R.S.toScheme) (hE : IsFiberDivisor F g t E)
    (C : R.S.PrimeCurve) (hC : InFiber g t C)
    (C' : R.S.PrimeCurve) (hC' : InFiber g t C') (hne : C' ≠ C) :
    ∃ C₀ : R.S.PrimeCurve, InFiber g t C₀ ∧ IsMinusOneCurve R.hreg C₀ ∧
      C₀.intersectionNumber R.KS = -1 :=
  exists_minusOneCurve_of_reducible R F hFF hKF g hg e hE
    (fiber_isConnected R p hp F hFF hKF g hg e t) C hC C' hC' hne


/-! ### Zariski's lemma and the count formula (lower bound) -/

/-- **Zariski's kernel lemma (matrix form)**: if `M` has nonnegative off-diagonal entries,
positive on the edges of a connected graph `G`, and `μ > 0` is a null vector of `M`, then every
null vector of `M` is a multiple of `μ` (maximum principle for `y_i / μ_i` along `G`). -/
theorem kernel_eq_smul_of_connected {ι : Type v} [Fintype ι]
    (G : SimpleGraph ι) (hconn : G.Connected)
    (M : Matrix ι ι ℚ) (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hadj : ∀ i j, G.Adj i j → 0 < M i j)
    (μ : ι → ℚ) (hμ : ∀ i, 0 < μ i) (hMμ : M *ᵥ μ = 0)
    (y : ι → ℚ) (hy : M *ᵥ y = 0) : ∃ r : ℚ, y = r • μ := by
  classical
  haveI : Nonempty ι := hconn.nonempty
  obtain ⟨i₀, -, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun i => y i / μ i) Finset.univ_nonempty
  set r : ℚ := y i₀ / μ i₀ with hr
  have hstep : ∀ i, y i / μ i = r → ∀ j, G.Adj i j → y j / μ j = r := by
    intro i hi j hij
    have hyi : ∑ l, M i l * y l = 0 := by
      have h := congrFun hy i
      simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using h
    have hμi : ∑ l, M i l * μ l = 0 := by
      have h := congrFun hMμ i
      simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using h
    have hterm : ∀ l, M i l * (μ l * (y l / μ l - r)) = M i l * y l - r * (M i l * μ l) := by
      intro l
      have hμl : μ l ≠ 0 := (hμ l).ne'
      rw [mul_sub, mul_div_cancel₀ _ hμl]
      ring
    have hsum : ∑ l, M i l * (μ l * (y l / μ l - r)) = 0 := by
      simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hyi, hμi, mul_zero, sub_zero]
    have hnonpos : ∀ l ∈ Finset.univ, M i l * (μ l * (y l / μ l - r)) ≤ 0 := by
      intro l _
      by_cases hli : l = i
      · subst hli
        rw [hi, sub_self, mul_zero, mul_zero]
      · apply mul_nonpos_of_nonneg_of_nonpos (hoff i l (Ne.symm hli))
        apply mul_nonpos_of_nonneg_of_nonpos (hμ l).le
        exact sub_nonpos.mpr (hmax l (Finset.mem_univ l))
    have hzero := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hsum j (Finset.mem_univ j)
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (hadj i j hij).ne'
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (hμ j).ne'
      · exact sub_eq_zero.mp h'
  have hwalk : ∀ {u w : ι} (p : G.Walk u w), y u / μ u = r → y w / μ w = r := by
    intro u w p
    induction p with
    | nil => exact id
    | cons hadj' _ ih => exact fun hu => ih (hstep _ hu _ hadj')
  refine ⟨r, funext fun j => ?_⟩
  obtain ⟨p⟩ := hconn.preconnected i₀ j
  have hj := hwalk p rfl
  rw [Pi.smul_apply, smul_eq_mul]
  exact (div_eq_iff (hμ j).ne').mp hj


/-! ### Fibre components as a finite family -/

/-- A closed fibre has finitely many components. -/
theorem finite_inFiber [Surjective g] (t : projectiveSpace k 1)
    (ht : IsClosed ({t} : Set (projectiveSpace k 1))) :
    Finite {C : R.S.PrimeCurve // InFiber g t C} := by
  haveI : Nontrivial (projectiveSpace k 1) :=
    KltDP.Examples.FrobeniusExceptionalChainPicard.projectiveLine_nontrivial
  have hZ : IsClosed (g.base ⁻¹' {t}) := ht.preimage g.base.hom.continuous
  have hne : g.base ⁻¹' {t} ≠ Set.univ :=
    ConnectedPointFiberComponents.pointFiber_ne_univ R.S g t
  have hfin := PrimeCurve.finite_setOf_subset hZ hne
  exact hfin.to_subtype

/-- The components of the fibre are the curves of the support of its fibre divisor. -/
theorem inFiber_iff_mem_support {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) (C : R.S.PrimeCurve) :
    InFiber g t C ↔ C ∈ (R.S.cartierToWeilHom E).support := by
  rw [Finsupp.mem_support_iff, inFiber_iff_coeff_pos R F g hE C]
  exact ⟨ne_of_gt, fun h => lt_of_le_of_ne (hE.effective C) (Ne.symm h)⟩

/-- Every closed fibre contains a component. -/
theorem exists_inFiber [Surjective g] {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E) :
    ∃ C : R.S.PrimeCurve, InFiber g t C := by
  obtain ⟨x, hx⟩ := g.surjective t
  have hx' : x ∈ divisorSupport (R.S.cartierToWeilHom E) := by
    rw [hE.support_eq]
    exact hx
  rw [mem_divisorSupport] at hx'
  obtain ⟨C, hC, -⟩ := hx'
  exact ⟨C, inFiber_of_coeff_ne_zero R F g hE C hC⟩

/-- The point-set fibre is the union of its components. -/
theorem iUnion_inFiber_eq {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) :
    (⋃ C : {C : R.S.PrimeCurve // InFiber g t C}, (C.1 : Set R.S.toScheme)) =
      g.base ⁻¹' {t} := by
  ext x
  constructor
  · intro hx
    obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
    exact C.2 x hxC
  · intro hx
    have hx' : x ∈ divisorSupport (R.S.cartierToWeilHom E) := by
      rw [hE.support_eq]
      exact hx
    rw [mem_divisorSupport] at hx'
    obtain ⟨C, hC, hxC⟩ := hx'
    exact Set.mem_iUnion.mpr ⟨⟨C, inFiber_of_coeff_ne_zero R F g hE C hC⟩, hxC⟩

/-- The incidence graph of the components of a connected fibre is connected. -/
theorem fiberGraph_connected {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) (hconn : IsConnected (g.base ⁻¹' {t}))
    [Finite {C : R.S.PrimeCurve // InFiber g t C}] :
    (curveIncidenceGraph (fun C : {C : R.S.PrimeCurve // InFiber g t C} => C.1)).Connected :=
  curveIncidenceGraph_connected_of_fiber (fun C : {C : R.S.PrimeCurve // InFiber g t C} => C.1)
    g t (iUnion_inFiber_eq R F g hE) hconn

include hg e in
/-- The multiplicity vector is a null vector of the fibre intersection matrix:
`Σ_j (C_i · C_j) μ_j = C_i · F = 0`. -/
theorem intersectionMatrix_mulVec_multiplicity {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    [Fintype {C : R.S.PrimeCurve // InFiber g t C}] :
    NullCurveIntersectionMatrix.intersectionMatrix R.S R.hreg
        (fun C : {C : R.S.PrimeCurve // InFiber g t C} => C.1) *ᵥ
      (fun C : {C : R.S.PrimeCurve // InFiber g t C} => (R.S.cartierToWeilHom E C.1 : ℚ)) = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  have hsum : i.1.intersectionNumber E = ∑ j : {C : R.S.PrimeCurve // InFiber g t C},
      R.S.cartierToWeilHom E j.1 * i.1.intersectionNumber (R.S.primeCurveCartier R.hreg j.1) := by
    rw [R.S.intersectionNumber_eq_weil_sum R.hreg i.1 E]
    unfold Finsupp.sum
    rw [Finset.sum_subtype (R.S.cartierToWeilHom E).support
      (fun C => (inFiber_iff_mem_support R F g hE C).symm)]
    rfl
  have hzero : i.1.intersectionNumber E = 0 := by
    rw [i.1.intersectionNumber_eq_of_cartierPicardClass_eq E F hE.class_eq]
    exact intersectionNumber_eq_zero_of_vertical R F g hg e i.1 t i.2
  have hcast : (∑ j : {C : R.S.PrimeCurve // InFiber g t C},
      NullCurveIntersectionMatrix.intersectionMatrix R.S R.hreg
        (fun C : {C : R.S.PrimeCurve // InFiber g t C} => C.1) i j *
        (R.S.cartierToWeilHom E j.1 : ℚ)) =
      ((∑ j : {C : R.S.PrimeCurve // InFiber g t C}, R.S.cartierToWeilHom E j.1 *
        i.1.intersectionNumber (R.S.primeCurveCartier R.hreg j.1) : ℤ) : ℚ) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    change ((R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.1)
      (R.S.primeCurveCartier R.hreg j.1) : ℤ) : ℚ) * _ = _
    rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber, mul_comm]
  rw [hcast, ← hsum, hzero, Int.cast_zero]

include hg e in
/-- **Zariski's lemma for the fibre**: a coefficient vector on the components of a connected fibre
whose numerical combination is orthogonal to every component is proportional to the
multiplicity vector. -/
theorem exists_smul_multiplicity_of_mulVec_eq_zero {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (hconn : IsConnected (g.base ⁻¹' {t}))
    [Fintype {C : R.S.PrimeCurve // InFiber g t C}]
    (y : {C : R.S.PrimeCurve // InFiber g t C} → ℚ)
    (hy : NullCurveIntersectionMatrix.intersectionMatrix R.S R.hreg
      (fun C : {C : R.S.PrimeCurve // InFiber g t C} => C.1) *ᵥ y = 0) :
    ∃ r : ℚ, y = r • fun C : {C : R.S.PrimeCurve // InFiber g t C} =>
      (R.S.cartierToWeilHom E C.1 : ℚ) := by
  classical
  have hG := fiberGraph_connected R F g hE hconn
  refine kernel_eq_smul_of_connected
    (curveIncidenceGraph (fun C : {C : R.S.PrimeCurve // InFiber g t C} => C.1)) hG
    (NullCurveIntersectionMatrix.intersectionMatrix R.S R.hreg
      (fun C : {C : R.S.PrimeCurve // InFiber g t C} => C.1)) ?_ ?_ _ ?_
    (intersectionMatrix_mulVec_multiplicity R F g hg e hE) y hy
  · intro i j hij
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    show (0 : ℚ) ≤ ((R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.1)
      (R.S.primeCurveCartier R.hreg j.1) : ℤ) : ℚ)
    exact_mod_cast
      PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg R.S R.hreg i.1 j.1 hne
  · intro i j hij
    have hne : i.1 ≠ j.1 := fun h => hij.1 (Subtype.ext h)
    have hnonneg :=
      PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg R.S R.hreg i.1 j.1 hne
    have hne0 : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.1)
        (R.S.primeCurveCartier R.hreg j.1) ≠ 0 := by
      intro h0
      exact (Set.not_disjoint_iff.mpr hij.2)
        ((PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
          R.S R.hreg i.1 j.1 hne).mp h0)
    show (0 : ℚ) < ((R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.1)
      (R.S.primeCurveCartier R.hreg j.1) : ℤ) : ℚ)
    exact_mod_cast lt_of_le_of_ne hnonneg (Ne.symm hne0)
  · intro C
    exact_mod_cast coeff_pos_of_inFiber R F g hE C.1 C.2

/-- Components of different fibres are numerically orthogonal (they are disjoint). -/
theorem curveClass_pairing_eq_zero_of_inFiber_ne {t t' : projectiveSpace k 1} (htt' : t ≠ t')
    (C C' : R.S.PrimeCurve) (hC : InFiber g t C) (hC' : InFiber g t' C') :
    R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C') = 0 := by
  apply DisjointNegativeCurvesRank.curveClass_pairing_eq_zero_of_disjoint
  rw [Set.disjoint_left]
  intro x hx hx'
  exact htt' ((hC x hx).symm.trans (hC' x hx'))

/-- The fibre class pairs positively with an ample class. -/
theorem pairing_ample_pos [Surjective g] {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (A : CartierDivisor R.S.toScheme)
    (hA : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf R.S.toScheme A)) :
    0 < R.S.numericalIntersectionBilinForm R.hreg
      (NefNullCurveNegativeSquare.cartierClass R.S F)
      (NefNullCurveNegativeSquare.cartierClass R.S A) := by
  rw [NefNullCurveNegativeSquare.cartierClass_pairing]
  have h1 : R.S.intersectionPairing R.hreg F A = R.S.intersectionPairing R.hreg E A := by
    rw [R.S.intersectionPairing_symm R.hreg F A,
      R.S.intersectionPairing_eq_of_class_eq_right R.hreg A F E hE.class_eq.symm,
      R.S.intersectionPairing_symm R.hreg]
  rw [h1, R.S.intersectionPairing_eq_weil_sum_right R.hreg E A]
  unfold Finsupp.sum
  have hpos : ∀ C ∈ (R.S.cartierToWeilHom E).support,
      0 < R.S.cartierToWeilHom E C * C.intersectionNumber A := by
    intro C hC
    apply mul_pos
    · exact lt_of_le_of_ne (hE.effective C) (Ne.symm (Finsupp.mem_support_iff.mp hC))
    · rw [C.intersectionNumber_eq_restrictionDegree]
      exact AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple R.S _ hA C
  obtain ⟨C, hC⟩ := exists_inFiber R F g hE
  have hne : (R.S.cartierToWeilHom E).support.Nonempty :=
    ⟨C, (inFiber_iff_mem_support R F g hE C).mp hC⟩
  exact_mod_cast Finset.sum_pos hpos hne


/-! ### The lower bound `2 + Σ_t (n_t - 1) ≤ ρ(S)` -/

include hFF hKF hg e in
/-- **Lemma 3.2 (iv), lower bound**: for every finite set `T` of closed points of `P¹`,
`2 + Σ_{t ∈ T} (n_t - 1) ≤ ρ(S)`, where `n_t` is the number of components of the fibre over
`t`. The classes `[F]`, an ample class `[A]`, and the classes of all components of the fibres
over `T` except one per fibre are linearly independent in `N¹(S)_ℚ` (Zariski's lemma). -/
theorem picardRank_lower_bound [IsProper g] [Surjective g]
    (hconn : ∀ t : projectiveSpace k 1, IsConnected (g.base ⁻¹' {t}))
    (T : Finset (projectiveSpace k 1))
    (hT : ∀ t ∈ T, IsClosed ({t} : Set (projectiveSpace k 1))) :
    2 + ∑ t ∈ T, (Nat.card {C : R.S.PrimeCurve // InFiber g t C} - 1) ≤ R.S.picardRank := by
  classical
  -- a closed point of `P¹` with its fibre divisor, and an ample class
  letI : JacobsonSpace (projectiveSpace k 1) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceToSpec k 1)
  obtain ⟨t₁, -, ht₁⟩ := nonempty_inter_closedPoints
    (show (Set.univ : Set (projectiveSpace k 1)).Nonempty from
      ⟨genericPoint (projectiveSpace k 1), Set.mem_univ _⟩)
    isOpen_univ.isLocallyClosed
  obtain ⟨E₁, hE₁⟩ := exists_isFiberDivisor R F g e t₁ ht₁
  obtain ⟨A, hA⟩ := R.S.exists_isAmple_cartier
  have hFA := pairing_ample_pos R F g hE₁ A hA
  have hF0 : NefNullCurveNegativeSquare.cartierClass R.S F ≠ 0 := by
    intro h0
    have hpair := NefNullCurveNegativeSquare.cartierClass_pairing R.S R.hreg R.KS F
    rw [h0, map_zero, hKF] at hpair
    norm_num at hpair
  have hFF' : R.S.numericalIntersectionBilinForm R.hreg
      (NefNullCurveNegativeSquare.cartierClass R.S F)
      (NefNullCurveNegativeSquare.cartierClass R.S F) = 0 := by
    rw [NefNullCurveNegativeSquare.cartierClass_pairing, hFF, Int.cast_zero]
  have hFC : ∀ (C : R.S.PrimeCurve) (t : projectiveSpace k 1), InFiber g t C →
      R.S.numericalIntersectionBilinForm R.hreg (NefNullCurveNegativeSquare.cartierClass R.S F)
        (DisjointNegativeCurvesRank.curveClass R.S R.hreg C) = 0 := by
    intro C t hC
    rw [NullCurveNumericalSpan.cartierClass_curveClass,
      intersectionNumber_eq_zero_of_vertical R F g hg e C t hC, Int.cast_zero]
  -- fibre divisors, finiteness and a chosen component for every `t ∈ T`
  have hEex : ∀ t : T, ∃ E, IsFiberDivisor F g t.1 E :=
    fun t => exists_isFiberDivisor R F g e t.1 (hT t.1 t.2)
  choose E hE using hEex
  haveI hfin : ∀ t : T, Finite {C : R.S.PrimeCurve // InFiber g t.1 C} :=
    fun t => finite_inFiber R g t.1 (hT t.1 t.2)
  letI instF : ∀ t : T, Fintype {C : R.S.PrimeCurve // InFiber g t.1 C} :=
    fun t => Fintype.ofFinite _
  have hC₀ex : ∀ t : T, ∃ C : R.S.PrimeCurve, InFiber g t.1 C := fun t => exists_inFiber R F g (hE t)
  choose C₀ hC₀ using hC₀ex
  have hC₀mem : ∀ t : T, C₀ t ∈ (R.S.cartierToWeilHom (E t)).support :=
    fun t => (inFiber_iff_mem_support R F g (hE t) (C₀ t)).mp (hC₀ t)
  -- the index type and the family
  let J' : T → Type u := fun t => ↥((R.S.cartierToWeilHom (E t)).support.erase (C₀ t))
  have hvert : ∀ (t : T) (C : J' t), InFiber g t.1 C.1 := fun t C =>
    inFiber_of_coeff_ne_zero R F g (hE t) C.1
      (Finsupp.mem_support_iff.mp (Finset.mem_of_mem_erase C.2))
  let v : Option (Option (Σ t : T, J' t)) → R.S.NumericalClassGroup := fun i =>
    match i with
    | none => NefNullCurveNegativeSquare.cartierClass R.S F
    | some none => NefNullCurveNegativeSquare.cartierClass R.S A
    | some (some ⟨_, C⟩) => DisjointNegativeCurvesRank.curveClass R.S R.hreg C.1
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fintype.sum_option, Fintype.sum_option, Fintype.sum_sigma] at hc
    change c none • NefNullCurveNegativeSquare.cartierClass R.S F +
      (c (some none) • NefNullCurveNegativeSquare.cartierClass R.S A +
        ∑ t : T, ∑ C : J' t, c (some (some ⟨t, C⟩)) •
          DisjointNegativeCurvesRank.curveClass R.S R.hreg C.1) = 0 at hc
    -- (1) the ample coefficient vanishes: pair with `[F]`
    have h1 : c (some none) = 0 := by
      have h := congrArg (fun d => R.S.numericalIntersectionBilinForm R.hreg
        (NefNullCurveNegativeSquare.cartierClass R.S F) d) hc
      simp only [map_add, map_sum, map_smul, smul_eq_mul, map_zero, hFF', mul_zero, zero_add] at h
      have hsum0 : ∑ t : T, ∑ C : J' t, c (some (some ⟨t, C⟩)) *
          R.S.numericalIntersectionBilinForm R.hreg
            (NefNullCurveNegativeSquare.cartierClass R.S F)
            (DisjointNegativeCurvesRank.curveClass R.S R.hreg C.1) = 0 :=
        Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun C _ => by
          rw [hFC C.1 t.1 (hvert t C), mul_zero]
      rw [hsum0, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_right hFA.ne'
    -- (2) the vertical coefficients vanish: Zariski's lemma fibre by fibre
    have h2 : ∀ (t₀ : T) (C : J' t₀), c (some (some ⟨t₀, C⟩)) = 0 := by
      intro t₀ C
      have hpair : ∀ C' : {C : R.S.PrimeCurve // InFiber g t₀.1 C},
          ∑ C : J' t₀, c (some (some ⟨t₀, C⟩)) *
            R.S.numericalIntersectionBilinForm R.hreg
              (DisjointNegativeCurvesRank.curveClass R.S R.hreg C.1)
              (DisjointNegativeCurvesRank.curveClass R.S R.hreg C'.1) = 0 := by
        intro C'
        have h := congrArg (fun d => R.S.numericalIntersectionBilinForm R.hreg d
          (DisjointNegativeCurvesRank.curveClass R.S R.hreg C'.1)) hc
        simp only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, map_smul,
          LinearMap.smul_apply, smul_eq_mul, map_zero, LinearMap.zero_apply] at h
        rw [hFC C'.1 t₀.1 C'.2, mul_zero, zero_add, h1, zero_mul, zero_add,
          Finset.sum_eq_single t₀] at h
        · exact h
        · intro t _ htne
          exact Finset.sum_eq_zero fun C _ => by
            rw [curveClass_pairing_eq_zero_of_inFiber_ne R g
              (fun h' => htne (Subtype.ext h')) C.1 C'.1 (hvert t C) C'.2, mul_zero]
        · intro h'
          exact absurd (Finset.mem_univ t₀) h'
      -- the coefficient vector on all components of the fibre over `t₀`
      let f : R.S.PrimeCurve → ℚ := fun D =>
        if h : D ∈ (R.S.cartierToWeilHom (E t₀)).support.erase (C₀ t₀) then
          c (some (some ⟨t₀, ⟨D, h⟩⟩)) else 0
      let y : {C : R.S.PrimeCurve // InFiber g t₀.1 C} → ℚ := fun D => f D.1
      have hy : NullCurveIntersectionMatrix.intersectionMatrix R.S R.hreg
          (fun C : {C : R.S.PrimeCurve // InFiber g t₀.1 C} => C.1) *ᵥ y = 0 := by
        funext C'
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
        have hterm : ∀ D : {C : R.S.PrimeCurve // InFiber g t₀.1 C},
            NullCurveIntersectionMatrix.intersectionMatrix R.S R.hreg
              (fun C : {C : R.S.PrimeCurve // InFiber g t₀.1 C} => C.1) C' D * y D =
            f D.1 * R.S.numericalIntersectionBilinForm R.hreg
              (DisjointNegativeCurvesRank.curveClass R.S R.hreg D.1)
              (DisjointNegativeCurvesRank.curveClass R.S R.hreg C'.1) := by
          intro D
          change ((R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg C'.1)
            (R.S.primeCurveCartier R.hreg D.1) : ℤ) : ℚ) * f D.1 = _
          rw [← DisjointNegativeCurvesRank.curveClass_pairing,
            LinearMap.BilinForm.IsSymm.eq (R.S.numericalIntersectionBilinForm_isSymm R.hreg),
            mul_comm]
        simp only [hterm]
        rw [← Finset.sum_subtype (R.S.cartierToWeilHom (E t₀)).support
          (fun D => (inFiber_iff_mem_support R F g (hE t₀) D).symm)
          (fun D => f D * R.S.numericalIntersectionBilinForm R.hreg
            (DisjointNegativeCurvesRank.curveClass R.S R.hreg D)
            (DisjointNegativeCurvesRank.curveClass R.S R.hreg C'.1)),
          ← Finset.sum_erase (R.S.cartierToWeilHom (E t₀)).support (a := C₀ t₀)
            (by simp only [f, dif_neg (Finset.not_mem_erase (C₀ t₀) _), zero_mul]),
          ← Finset.sum_coe_sort]
        rw [← hpair C']
        refine Finset.sum_congr rfl fun D _ => ?_
        simp only [f, dif_pos D.2]
      obtain ⟨r, hr⟩ := exists_smul_multiplicity_of_mulVec_eq_zero R F g hg e (hE t₀)
        (hconn t₀.1) y hy
      have hr0 : r = 0 := by
        have h0 := congrFun hr ⟨C₀ t₀, hC₀ t₀⟩
        simp only [y, f, dif_neg (Finset.not_mem_erase (C₀ t₀) _), Pi.smul_apply,
          smul_eq_mul] at h0
        have hpos : (0 : ℚ) < (R.S.cartierToWeilHom (E t₀) (C₀ t₀) : ℚ) := by
          exact_mod_cast coeff_pos_of_inFiber R F g (hE t₀) (C₀ t₀) (hC₀ t₀)
        rcases mul_eq_zero.mp h0.symm with h' | h'
        · exact h'
        · exact absurd h' hpos.ne'
      have hyC := congrFun hr ⟨C.1, hvert t₀ C⟩
      rw [hr0, zero_smul, Pi.zero_apply] at hyC
      simpa only [y, f, dif_pos C.2] using hyC
    -- (3) the fibre-class coefficient vanishes
    have h3 : c none = 0 := by
      have hzero : ∑ t : T, ∑ C : J' t, c (some (some ⟨t, C⟩)) •
          DisjointNegativeCurvesRank.curveClass R.S R.hreg C.1 = 0 :=
        Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun C _ => by rw [h2 t C, zero_smul]
      rw [h1, zero_smul, hzero, add_zero, add_zero] at hc
      exact (smul_eq_zero.mp hc).resolve_right hF0
    intro i
    rcases i with _ | _ | ⟨t, C⟩
    · exact h3
    · exact h1
    · exact h2 t C
  -- counting
  haveI : Module.Finite ℚ R.S.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalClassGroup_finite R.S R.hreg
  have hcard := hli.fintype_card_le_finrank
  have hcount : Fintype.card (Option (Option (Σ t : T, J' t))) =
      2 + ∑ t ∈ T, (Nat.card {C : R.S.PrimeCurve // InFiber g t C} - 1) := by
    rw [Fintype.card_option, Fintype.card_option, Fintype.card_sigma, ← Finset.sum_coe_sort T]
    have hsub : ∀ t : T, Fintype.card (J' t) =
        Nat.card {C : R.S.PrimeCurve // InFiber g t.1 C} - 1 := by
      intro t
      rw [Nat.card_eq_fintype_card, Fintype.card_of_subtype (R.S.cartierToWeilHom (E t)).support
        (fun C => (inFiber_iff_mem_support R F g (hE t) C).symm)]
      show Fintype.card ↥((R.S.cartierToWeilHom (E t)).support.erase (C₀ t)) = _
      rw [Fintype.card_coe, Finset.card_erase_of_mem (hC₀mem t)]
    simp only [hsub]
    omega
  change 2 + ∑ t ∈ T, (Nat.card {C : R.S.PrimeCurve // InFiber g t C} - 1) ≤
    Module.finrank ℚ R.S.NumericalClassGroup
  rw [← hcount]
  exact hcard


include hFF hKF hg e in
/-- **Only finitely many fibres are reducible**, and at most `ρ(S) - 2` of them: every finite
set of reducible closed fibres has at most `ρ(S) - 2` elements by the lower bound. -/
theorem reducibleFibers_finite [IsProper g] [Surjective g]
    (hconn : ∀ t : projectiveSpace k 1, IsConnected (g.base ⁻¹' {t})) :
    {t : projectiveSpace k 1 | IsClosed ({t} : Set (projectiveSpace k 1)) ∧
      ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C'}.Finite ∧
    ∀ T : Finset (projectiveSpace k 1),
      (∀ t ∈ T, IsClosed ({t} : Set (projectiveSpace k 1)) ∧
        ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C') →
      T.card + 2 ≤ R.S.picardRank := by
  classical
  have hbound : ∀ T : Finset (projectiveSpace k 1),
      (∀ t ∈ T, IsClosed ({t} : Set (projectiveSpace k 1)) ∧
        ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C') →
      T.card + 2 ≤ R.S.picardRank := by
    intro T hTred
    have hT : ∀ t ∈ T, IsClosed ({t} : Set (projectiveSpace k 1)) := fun t ht => (hTred t ht).1
    have hlow := picardRank_lower_bound R F hFF hKF g hg e hconn T hT
    have hge : ∀ t ∈ T, 1 ≤ Nat.card {C : R.S.PrimeCurve // InFiber g t C} - 1 := by
      intro t ht
      obtain ⟨C, C', hC, hC', hne⟩ := (hTred t ht).2
      haveI := finite_inFiber R g t (hT t ht)
      haveI : Nontrivial {C : R.S.PrimeCurve // InFiber g t C} :=
        ⟨⟨⟨C, hC⟩, ⟨C', hC'⟩, fun h => hne (congrArg Subtype.val h)⟩⟩
      have h2 : 1 < Nat.card {C : R.S.PrimeCurve // InFiber g t C} :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    have hsum : T.card ≤ ∑ t ∈ T, (Nat.card {C : R.S.PrimeCurve // InFiber g t C} - 1) := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum hge
    omega
  refine ⟨Set.not_infinite.mp fun hinf => ?_, hbound⟩
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq (R.S.picardRank)
  have := hbound T (fun t ht => hTsub ht)
  omega


/-! ### The count formula in the datum -/

include hp hFF hKF hg e in
/-- Lemma 3.2 (iv), lower bound, in the datum: `2 + Σ_{t ∈ T} (n_t - 1) ≤ ρ(S)` for every finite
set `T` of closed points of `P¹`. -/
theorem rulingFibers_picardRank_lower_bound [IsProper g] [Surjective g]
    (T : Finset (projectiveSpace k 1))
    (hT : ∀ t ∈ T, IsClosed ({t} : Set (projectiveSpace k 1))) :
    2 + ∑ t ∈ T, (Nat.card {C : R.S.PrimeCurve // InFiber g t C} - 1) ≤ R.S.picardRank :=
  picardRank_lower_bound R F hFF hKF g hg e (fun t => fiber_isConnected R p hp F hFF hKF g hg e t)
    T hT

include hp hFF hKF hg e in
/-- In the datum: the reducible fibres are finite in number, at most `ρ(S) - 2`. -/
theorem rulingFibers_reducibleFibers_finite [IsProper g] [Surjective g] :
    {t : projectiveSpace k 1 | IsClosed ({t} : Set (projectiveSpace k 1)) ∧
      ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C'}.Finite ∧
    ∀ T : Finset (projectiveSpace k 1),
      (∀ t ∈ T, IsClosed ({t} : Set (projectiveSpace k 1)) ∧
        ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C') →
      T.card + 2 ≤ R.S.picardRank :=
  reducibleFibers_finite R F hFF hKF g hg e (fun t => fiber_isConnected R p hp F hFF hKF g hg e t)

end KltDP.Manuscript.S03

#print axioms KltDP.Manuscript.S03.exists_isFiberDivisor
#print axioms KltDP.Manuscript.S03.fiber_isConnected
#print axioms KltDP.Manuscript.S03.inFiber_iff_coeff_pos
#print axioms KltDP.Manuscript.S03.fiber_intersection_eq
#print axioms KltDP.Manuscript.S03.fiber_canonical_sum
#print axioms KltDP.Manuscript.S03.exists_negative_canonical_component
#print axioms KltDP.Manuscript.S03.fiberDivisor_eq_primeCurveCartier_of_irreducible
#print axioms KltDP.Manuscript.S03.irreducibleFiber_component
#print axioms KltDP.Manuscript.S03.exists_meeting_component
#print axioms KltDP.Manuscript.S03.selfIntersection_neg_of_reducible
#print axioms KltDP.Manuscript.S03.irreducible_of_selfIntersection_nonneg
#print axioms KltDP.Manuscript.S03.isMinusOneCurve_of_reducible_of_negative_canonical
#print axioms KltDP.Manuscript.S03.exists_minusOneCurve_of_reducible
#print axioms KltDP.Manuscript.S03.rulingFibers_selfIntersection_neg
#print axioms KltDP.Manuscript.S03.rulingFibers_exists_minusOneCurve
#print axioms KltDP.Manuscript.S03.kernel_eq_smul_of_connected
#print axioms KltDP.Manuscript.S03.finite_inFiber
#print axioms KltDP.Manuscript.S03.fiberGraph_connected
#print axioms KltDP.Manuscript.S03.intersectionMatrix_mulVec_multiplicity
#print axioms KltDP.Manuscript.S03.exists_smul_multiplicity_of_mulVec_eq_zero
#print axioms KltDP.Manuscript.S03.pairing_ample_pos
#print axioms KltDP.Manuscript.S03.picardRank_lower_bound
#print axioms KltDP.Manuscript.S03.reducibleFibers_finite
#print axioms KltDP.Manuscript.S03.rulingFibers_picardRank_lower_bound
#print axioms KltDP.Manuscript.S03.rulingFibers_reducibleFibers_finite
