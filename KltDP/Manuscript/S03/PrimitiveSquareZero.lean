import KltDP.Manuscript.Datum.AnticanonicalClass
import KltDP.Geometry.KltResolutionPencilNormalProjective
import KltDP.Geometry.SquareZeroPicardPrimitive
import KltDP.Geometry.SquareZeroCompleteSectionDimensionEulerOne
import KltDP.Geometry.ProjectiveLineClosedPointCartier
import KltDP.Geometry.CartierPullbackClosedFiber
import KltDP.Geometry.DominantCartierPullbackModule
import KltDP.Geometry.DominantCartierRegularPullback
import KltDP.Geometry.ProjectiveLineDegreeZeroImage
import KltDP.Geometry.ProjectiveLineActualDegreeOne
import KltDP.Geometry.ProjectiveLineDegreeExponent
import KltDP.Geometry.PrimeCurvePointFiberFactorization
import KltDP.Geometry.PrimeCurveInclusionLift
import KltDP.Geometry.QuadraticOriginalGenericPoint
import KltDP.Geometry.RegularCartierIdealSupport
import KltDP.Geometry.GeometricConnectedFiberTopology

/-!
# Manuscript Lemma 3.1: a nef divisor of square zero and canonical degree `-2`

Source: `source/manuscript.tex`, lines 666–712, `lem:primitive-square-zero`, for the
resolution datum `(S, D, L)` of a rank-one klt del Pezzo surface (`ResolutionDatum`).

For a nef Cartier divisor `F` on `S` with `F² = 0` and `K_S · F = -2`:

* `primitiveSquareZero_ruling`: `|F|` is a basepoint-free pencil `g : S → P¹` over `k`,
  proper, surjective, flat, with `g_* O_S = O_{P¹}` (Stein), `g^* O(1) ≅ O(F)`, geometrically
  connected fibres, and generic fibre an integral normal projective regular curve of genus
  zero (`χ = 1`, `h⁰ = 1`, `h¹ = 0`) over `k(P¹)`;
* `primitiveSquareZero_primitive`: the class of `F` in `Pic S` is primitive (the manuscript's
  literal definition: not an integer multiple `d • G` with `d > 1`), and `Pic S` is torsion-free;
* `primitiveSquareZero_hZero`: `h⁰(S, O(F)) = 2` and `h¹(S, O(F)) = 0`;
* for the pencil: the fibre class is nef (`intersectionNumber_nonneg`), `F · C = 0` exactly
  when `C` is vertical, i.e. contained in a fibre (`intersectionNumber_eq_zero_iff_vertical`),
  and every closed fibre `g⁻¹(t)` is the zero scheme of an effective Cartier divisor `E_t`
  with regular equations whose Picard class is that of `F` and whose Weil support is the
  point-set fibre (`exists_closedFiberDivisor`).

Smoothness of the generic fibre (the "rational ruling" clause) is not asserted here; see
`RulingFibers.lean`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SmoothCanonicalExteriorComparison
open KltDP.Manuscript

universe u

namespace KltDP.Manuscript.S03

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)
  (p : ℕ) [CharP k p] (hp : 0 < p)

local instance projectiveLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-! ### The pencil -/

include hp in
/-- **Lemma 3.1, ruling clause** (TeX 675–711): a nef Cartier divisor `F` with `F² = 0` and
`K_S · F = -2` defines a pencil `g : S ⟶ P¹` over `k` which is proper, surjective, dominant,
flat, Stein (`g^♯ : O_{P¹} → g_* O_S` is an isomorphism), with `g^* O(1) ≅ O(F)`, connected
fibres after every field-valued base change, and whose generic fibre `C` over `K = k(P¹)`
(of characteristic `p`) is integral, normal, projective, proper, regular, one-dimensional,
with `χ(O_C) = 1`, `h⁰(O_C) = 1`, `H¹(O_C) = 0`, and `K = H⁰(C, O_C)`. -/
theorem primitiveSquareZero_ruling (F : CartierDivisor R.S.toScheme)
    (hF : Positivity.IsNef R.S.structureMorphism (cartierDivisorInvertibleSheaf R.S.toScheme F))
    (hFF : R.S.intersectionPairing R.hreg F F = 0)
    (hKF : R.S.intersectionPairing R.hreg R.KS F = -2) :
    ∃ g : R.S.toScheme ⟶ projectiveSpace k 1,
      g ≫ projectiveSpaceToSpec k 1 = R.S.structureMorphism ∧
      IsProper g ∧ Surjective g ∧ IsDominant g ∧ Flat g ∧ IsIso g.c ∧
      Nonempty ((pullbackInvertibleSheaf g
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
          cartierDivisorModule R.S.toScheme F) ∧
      (∀ (l : Type u) [Field l] (q : Spec (CommRingCat.of l) ⟶ projectiveSpace k 1),
        ConnectedSpace (pullback g q : Scheme.{u})) ∧
      (let C := g.fiber (genericPoint (projectiveSpace k 1))
       let f := g.fiberToSpecResidueField (genericPoint (projectiveSpace k 1))
       let M := SheafOfModules.unit C.ringCatSheaf
       CharP ((projectiveSpace k 1).residueField (genericPoint (projectiveSpace k 1))) p ∧
         IsIntegral C ∧ IsNormalScheme C ∧ IsProjectiveOverField f ∧ IsProper f ∧
         (∀ x : C, RegularPoint C x) ∧ topologicalKrullDim C = 1 ∧
         eulerCharacteristic f M = 1 ∧ cohomologyDimension f M 0 = 1 ∧
         cohomologyDimension f M 1 = 0 ∧ Subsingleton (H M 1) ∧
         IsIso ((Scheme.ΓSpecIso ((projectiveSpace k 1).residueField
           (genericPoint (projectiveSpace k 1)))).inv ≫ f.appTop) ∧
         Function.Bijective (baseFieldToGlobalSections f)) :=
  R.hmin.exists_connectedPencil_normalProjectiveGenusZero_of_kltDelPezzo R.hDP R.hrank p hp
    R.KS R.eKS F hF hFF hKF

/-! ### Primitivity and the section space -/

/-- **Lemma 3.1, primitivity** (TeX 683–686): the class of `F` in `Pic S` is not an integer
multiple `d • G` with `d > 1` (the parity `G² - K·G ∈ 2ℤ` of Riemann–Roch). -/
theorem primitiveSquareZero_primitive (F : CartierDivisor R.S.toScheme)
    (hFF : R.S.intersectionPairing R.hreg F F = 0)
    (hKF : R.S.intersectionPairing R.hreg R.KS F = -2) :
    ∀ d : ℤ, 1 < d → ∀ G : Additive R.S.toScheme.Pic,
      d • G ≠ cartierPicardHom R.S.toScheme F :=
  R.S.squareZero_picard_not_divisible R.hreg R.KS R.eKS F hFF hKF

include p hp in
/-- The Picard group of the resolution surface is torsion-free (so primitivity in `Pic S`
is primitivity in the free Picard lattice of the manuscript). -/
theorem picardTorsionFree : R.S.PicardTorsionFree :=
  (R.hmin.picard_and_structure_invariants_of_kltDelPezzo R.hDP R.hrank p hp).2.1

/-- The same primitivity for Cartier representatives: `O(F) ≇ O(d • G)` for `d > 1`. -/
theorem primitiveSquareZero_primitive_cartier (F : CartierDivisor R.S.toScheme)
    (hFF : R.S.intersectionPairing R.hreg F F = 0)
    (hKF : R.S.intersectionPairing R.hreg R.KS F = -2)
    (d : ℤ) (hd : 1 < d) (G : CartierDivisor R.S.toScheme) :
    cartierPicardClass R.S.toScheme (d • G) ≠ cartierPicardClass R.S.toScheme F := by
  intro h
  apply primitiveSquareZero_primitive R F hFF hKF d hd (cartierPicardHom R.S.toScheme G)
  rw [← map_zsmul]
  exact Additive.toMul.injective h

include p hp in
/-- **Lemma 3.1, `h⁰(F) = 2`** (TeX 705–706): the complete linear system `|F|` is a pencil,
and `h¹(O(F)) = 0`. -/
theorem primitiveSquareZero_hZero (F : CartierDivisor R.S.toScheme)
    (hF : Positivity.IsNef R.S.structureMorphism (cartierDivisorInvertibleSheaf R.S.toScheme F))
    (hFF : R.S.intersectionPairing R.hreg F F = 0)
    (hKF : R.S.intersectionPairing R.hreg R.KS F = -2) :
    cohomologyDimension R.S.structureMorphism (cartierDivisorModule R.S.toScheme F) 0 = 2 ∧
      cohomologyDimension R.S.structureMorphism (cartierDivisorModule R.S.toScheme F) 1 = 0 :=
  R.S.squareZero_hZero_eq_two_and_hOne_eq_zero_of_euler_one R.hreg R.KS R.eKS
    (R.hmin.picard_and_structure_invariants_of_kltDelPezzo R.hDP R.hrank p hp).2.2.1
    F hF hFF hKF

/-! ### The fibre class: nefness, verticality and the closed fibres -/

section Ruling

variable (F : CartierDivisor R.S.toScheme)
  (g : R.S.toScheme ⟶ projectiveSpace k 1)
  (hg : g ≫ projectiveSpaceToSpec k 1 = R.S.structureMorphism)
  (e : (pullbackInvertibleSheaf g (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
    cartierDivisorModule R.S.toScheme F)

/-- The fibre class is nef: `F · C ≥ 0` for every prime curve (`F` nef). -/
theorem intersectionNumber_nonneg
    (hF : Positivity.IsNef R.S.structureMorphism (cartierDivisorInvertibleSheaf R.S.toScheme F))
    (C : R.S.PrimeCurve) : 0 ≤ C.intersectionNumber F :=
  (Positivity.isNef_iff_forall_primeCurve R.S _).mp hF C

include hg e in
/-- A prime curve contained in a fibre of the pencil is orthogonal to the fibre class:
`F · C = 0` for `C` vertical (`O(F) = g^* O(1)` restricted to a curve mapping to a point). -/
theorem intersectionNumber_eq_zero_of_vertical (C : R.S.PrimeCurve)
    (t : projectiveSpace k 1) (hC : ∀ x ∈ (C : Set R.S.toScheme), g.base x = t) :
    C.intersectionNumber F = 0 := by
  obtain ⟨q, hfac, -, -⟩ := PrimeCurvePointFiberFactorization.exists_factor_of_constant
    R.S C (projectiveSpaceToSpec k 1) g hg t hC
  have h0 := PrimeCurveInclusionLift.restrictionDegree_pullback_eq_zero C C.inclusion
    C.range_inclusion.symm g C.toSpec q hfac (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)
  rw [C.intersectionNumber_eq_restrictionDegree, ← h0]
  exact (C.restrictionDegree_eq_of_iso e).symm

include hg e in
/-- A prime curve with `F · C = 0` is vertical: it lies in a closed fibre of the pencil
(the pullback of `O(1)` has degree zero on `C`, so `g|_C` is constant). -/
theorem exists_vertical_of_intersectionNumber_eq_zero (C : R.S.PrimeCurve)
    (h : C.intersectionNumber F = 0) :
    ∃ t : projectiveSpace k 1, IsClosed ({t} : Set (projectiveSpace k 1)) ∧
      ∀ x ∈ (C : Set R.S.toScheme), g.base x = t := by
  letI : IsProper C.toSpec := C.toSpec_isProper
  obtain ⟨em⟩ := ProjectiveLineActualDegreeOne.exists_iso_of_degree_one k
    (RationalTreePicard.monomialLineBundle k 1) (ProjectiveLineDegree.degree_monomial_one k)
  have hdeg : eulerCharacteristic C.toSpec (pullbackInvertibleSheaf (C.inclusion ≫ g)
      (RationalTreePicard.monomialLineBundle k 1)).obj -
      eulerCharacteristic C.toSpec (SheafOfModules.unit C.toScheme.ringCatSheaf) = 0 := by
    change C.lineDegree (pullbackInvertibleSheaf (C.inclusion ≫ g)
      (RationalTreePicard.monomialLineBundle k 1)) = 0
    rw [C.lineDegree_eq_of_iso
      (L := pullbackInvertibleSheaf (C.inclusion ≫ g) (RationalTreePicard.monomialLineBundle k 1))
      (M := pullbackInvertibleSheaf (C.inclusion ≫ g) (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1))
      ((schemeModulePullback (C.inclusion ≫ g)).mapIso em),
      ← C.restrictionDegree_pullback g (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1),
      C.restrictionDegree_eq_of_iso
        (L := pullbackInvertibleSheaf g (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1))
        (M := cartierDivisorInvertibleSheaf R.S.toScheme F) e]
    exact h
  have hbase : (C.inclusion ≫ g) ≫ projectiveSpaceToSpec k 1 = C.toSpec := by
    rw [Category.assoc, hg]
    rfl
  obtain ⟨t, ht, hrange⟩ := ProjectiveLineDegreeZeroImage.exists_closed_point_range_eq_singleton
    C.toSpec C.dimension_one_toScheme.le (C.inclusion ≫ g) hdeg hbase
  refine ⟨t, ht, ?_⟩
  intro x hx
  rw [← C.range_inclusion] at hx
  obtain ⟨y, rfl⟩ := hx
  have hy : (C.inclusion ≫ g).base y ∈ Set.range (C.inclusion ≫ g).base := ⟨y, rfl⟩
  rw [hrange, Set.mem_singleton_iff] at hy
  simpa only [Scheme.comp_base_apply] using hy

include hg e in
/-- **Verticality criterion**: `F · C = 0` if and only if `C` is contained in a fibre of `g`. -/
theorem intersectionNumber_eq_zero_iff_vertical (C : R.S.PrimeCurve) :
    C.intersectionNumber F = 0 ↔
      ∃ t : projectiveSpace k 1, ∀ x ∈ (C : Set R.S.toScheme), g.base x = t := by
  constructor
  · intro h
    obtain ⟨t, -, ht⟩ := exists_vertical_of_intersectionNumber_eq_zero R F g hg e C h
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact intersectionNumber_eq_zero_of_vertical R F g hg e C t ht

include hg e in
/-- A curve not orthogonal to the fibre class is horizontal: it is not contained in any fibre. -/
theorem not_vertical_of_intersectionNumber_pos (C : R.S.PrimeCurve)
    (h : 0 < C.intersectionNumber F) (t : projectiveSpace k 1) :
    ¬ ∀ x ∈ (C : Set R.S.toScheme), g.base x = t := by
  intro hC
  have := intersectionNumber_eq_zero_of_vertical R F g hg e C t hC
  omega

variable [IsProper g] [Surjective g]

include e in
/-- **Closed fibres are Cartier divisors of class `F`** (TeX 700–706): for every closed
point `t ∈ P¹`, the scheme-theoretic fibre `g⁻¹(t)` is the zero scheme of an effective Cartier
divisor `E_t` with regular equations (the pullback of the point divisor), `O(E_t) ≅ O(F)`,
its Weil divisor is effective with geometric support the point-set fibre, and the ideal sheaf
of the closed immersion `g⁻¹(t) → S` is exactly the divisor ideal of `E_t`. -/
theorem exists_closedFiberDivisor (t : projectiveSpace k 1)
    (ht : IsClosed ({t} : Set (projectiveSpace k 1))) :
    ∃ (E : CartierDivisor R.S.toScheme) (hE : HasRegularCartierEquations R.S.toScheme E),
      Nonempty (cartierDivisorModule R.S.toScheme E ≅ cartierDivisorModule R.S.toScheme F) ∧
      cartierPicardClass R.S.toScheme E = cartierPicardClass R.S.toScheme F ∧
      EffectiveDivisor (R.S.cartierToWeilHom E) ∧
      divisorSupport (R.S.cartierToWeilHom E) = g.base ⁻¹' {t} ∧
      effectiveCartierIdealDataOfRegularEquations R.S.toScheme E hE =
        (pullback.fst g (closedPointSection (projectiveSpaceToSpec k 1) t ht)).ker := by
  haveI : GenericPointPreserving g := genericPointPreserving_of_surjective g g.surjective
  obtain ⟨D, hD, hci, hi, hI, ⟨eD⟩⟩ :=
    ProjectiveLineClosedPointCartier.exists_cartierDivisor k t ht
  let i := closedPointSection (projectiveSpaceToSpec k 1) t ht
  letI : IsClosedImmersion i := hci
  let E := pullbackDivisor g D hD
  let hE : HasRegularCartierEquations R.S.toScheme E := pullbackDivisor_hasRegularEquations g D hD
  have hp : DominantCartierPullback.pullbackHom g D = E :=
    DominantCartierPullback.pullbackHom_eq_pullbackDivisor g D hD
  let eE : cartierDivisorModule R.S.toScheme E ≅ cartierDivisorModule R.S.toScheme F :=
    eqToIso (congrArg (cartierDivisorModule R.S.toScheme) hp.symm) ≪≫
      (DominantCartierPullback.modulePullbackIso g D).symm ≪≫
      (schemeModulePullback g).mapIso eD ≪≫ e
  have hker : pullbackIdealData g D hD = (pullback.fst g i).ker :=
    CartierPullbackClosedFiber.ideal_eq_fiber_ker g D hD i hI.symm
  have heff : EffectiveDivisor (R.S.cartierToWeilHom E) :=
    R.S.effective_cartierToWeilHom_of_regularEquations E hE
  refine ⟨E, hE, ⟨eE⟩, cartierPicardClass_eq_of_iso R.S.toScheme E F eE, heff, ?_, hker⟩
  letI := R.S.stalks_uniqueFactorizationMonoid_of_regular R.hreg
  have hsupp := R.S.regularCartierIdealData_support E heff
  dsimp only at hsupp
  rw [← hsupp, ← Scheme.IdealSheafData.range_gluedTo]
  have hfst : (pullbackIdealData g D hD).gluedTo =
      (CartierPullbackClosedFiber.iso g D hD i hI.symm).hom ≫ pullback.fst g i :=
    (CartierPullbackClosedFiber.iso_hom_fst g D hD i hI.symm).symm
  change Set.range (pullbackIdealData g D hD).gluedTo.base = _
  rw [hfst, Scheme.comp_base, TopCat.coe_comp, Set.range_comp,
    (CartierPullbackClosedFiber.iso g D hD i hI.symm).hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst, range_fieldMorphism, fieldMorphismPoint_closedPointSection]

end Ruling

end KltDP.Manuscript.S03

#print axioms KltDP.Manuscript.S03.primitiveSquareZero_ruling
#print axioms KltDP.Manuscript.S03.primitiveSquareZero_primitive
#print axioms KltDP.Manuscript.S03.picardTorsionFree
#print axioms KltDP.Manuscript.S03.primitiveSquareZero_primitive_cartier
#print axioms KltDP.Manuscript.S03.primitiveSquareZero_hZero
#print axioms KltDP.Manuscript.S03.intersectionNumber_nonneg
#print axioms KltDP.Manuscript.S03.intersectionNumber_eq_zero_of_vertical
#print axioms KltDP.Manuscript.S03.exists_vertical_of_intersectionNumber_eq_zero
#print axioms KltDP.Manuscript.S03.intersectionNumber_eq_zero_iff_vertical
#print axioms KltDP.Manuscript.S03.exists_closedFiberDivisor
