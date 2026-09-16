import KltDP.Geometry.SelectedPrimeCurveCartierUnion
import KltDP.Geometry.QuadraticSectionImageIntegral

/-!
# Original Cartier ideals on the canonical quadratic atlas

The existing canonical section of O(D), together with an original
square-root isomorphism, constructs the existing finite flat quadratic
atlas. Its affine branch ideal equals the affine component of the
original Cartier ideal: the latter is the genuine section image, and
the nonzero canonical section gives the already proved equality between
that image and the literal quadratic coefficient ideal.

The derived ideal equality identifies each actual Cartier quotient
gluing chart with the actual branch quotient scheme. Both the original
quotient map and the composite to the original base scheme are retained.
For an actual finite selection of prime curves with an integral Picard
half-class, all Cartier, line-bundle, equation and ideal inputs are
derived by the preceding construction. Thus the selected union itself
has these original quadratic branch charts.

This is an affine chart identification. Compatibility of the resulting
chart family with an independently constructed global branch gluing,
and branch/cover smoothness, are not asserted. No new gluing foundation,
supplied ideal equality, or desired scheme isomorphism is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

open QuadraticCover

attribute [local instance] Types.instFunLike Types.instConcreteCategory

-- Prove the original quotient triangle over abstract ideals before
-- substituting the concrete Cartier ideal and quadratic atlas coefficient.
private theorem cartierBranch_spec_quotEquivOfEq_hom_mk
    {R : Type u} [CommRing R] {I J : Ideal R} (h : I = J) :
    (Scheme.Spec.mapIso ((Ideal.quotEquivOfEq h).symm.toCommRingCatIso.op)).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  apply congrArg (fun f : R →+* (R ⧸ I) => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro r
  change (Ideal.quotEquivOfEq h).symm (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r
  rw [Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk]

variable (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]

local instance : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

variable (D : CartierDivisor X) (hD : HasRegularCartierEquations X D)
  (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X D)

/-- The existing quadratic atlas of the original canonical Cartier section. -/
def effectiveCartierQuadraticAtlas :
    QuadraticCoverAtlas.Data X (AffineOpenRefinement.Index X L.localTrivializations.X) :=
  InvertibleQuadraticAtlas.fromSquareRoot X L (cartierDivisorModule X D) e
    (effectiveCartierSection X D hD)

/-- The actual original Cartier ideal on an existing affine chart is
the ideal of that same quadratic atlas's original branch coefficient. -/
theorem effectiveCartierIdealData_eq_quadraticBranchIdeal
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    let A := effectiveCartierQuadraticAtlas X D hD L e
    (effectiveCartierIdealData X D hD L e).ideal ⟨A.opens i, A.affine i⟩ =
      branchIdeal (A.sections i) := by
  dsimp only
  rw [effectiveCartierIdealData_ideal_image]
  exact InvertibleQuadraticAtlas.sectionImageIdeal_eq_branchIdeal_of_nonzero
    X (cartierDivisorModule X D) (effectiveCartierSection X D hD) L e
      (effectiveCartierSection_ne_zero X D hD) i

/-- Equality of the original ideals gives the actual quotient-ring equivalence. -/
def effectiveCartierBranchQuotientEquiv
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    let A := effectiveCartierQuadraticAtlas X D hD L e
    (Γ(X, A.opens i) ⧸ (effectiveCartierIdealData X D hD L e).ideal
      ⟨A.opens i, A.affine i⟩) ≃+* (Γ(X, A.opens i) ⧸ branchIdeal (A.sections i)) :=
  Ideal.quotEquivOfEq (effectiveCartierIdealData_eq_quadraticBranchIdeal X D hD L e i)

/-- The actual original Cartier gluing chart is the original quadratic branch chart. -/
def effectiveCartierBranchChartIso
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    let A := effectiveCartierQuadraticAtlas X D hD L e
    (effectiveCartierIdealData X D hD L e).glueDataObj ⟨A.opens i, A.affine i⟩ ≅
      branchScheme (A.sections i) :=
  Scheme.Spec.mapIso
    (effectiveCartierBranchQuotientEquiv X D hD L e i).symm.toCommRingCatIso.op

/-- The chart isomorphism commutes with the original quotient inclusion
into the spectrum of the original affine section ring. -/
@[reassoc]
theorem effectiveCartierBranchChartIso_hom_toSpec
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    let A := effectiveCartierQuadraticAtlas X D hD L e
    (effectiveCartierBranchChartIso X D hD L e i).hom ≫ branchι (A.sections i) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((effectiveCartierIdealData X D hD L e).ideal ⟨A.opens i, A.affine i⟩))) := by
  exact cartierBranch_spec_quotEquivOfEq_hom_mk
    (effectiveCartierIdealData_eq_quadraticBranchIdeal X D hD L e i)

/-- Postcomposition retains the actual original Cartier gluing map and
its inclusion into the original surface, not just an abstract affine iso. -/
@[reassoc]
theorem effectiveCartierBranchChartIso_hom_toBase
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    let A := effectiveCartierQuadraticAtlas X D hD L e
    let I := effectiveCartierIdealData X D hD L e
    (effectiveCartierBranchChartIso X D hD L e i).hom ≫
        branchι (A.sections i) ≫ (A.affine i).fromSpec =
      I.glueData.ι ⟨A.opens i, A.affine i⟩ ≫ I.gluedTo := by
  dsimp only
  rw [Scheme.IdealSheafData.ι_gluedTo, Scheme.IdealSheafData.glueDataObjι_ι,
    ← Category.assoc]
  exact congrArg (fun f => f ≫
    ((effectiveCartierQuadraticAtlas X D hD L e).affine i).fromSpec)
    (effectiveCartierBranchChartIso_hom_toSpec X D hD L e i)

end Geometry

namespace Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
variable [∀ x : S.toScheme, UniqueFactorizationMonoid (S.stalk x)]

local instance : S.toScheme.IsSeparated := surfaceSeparated S

local instance : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- The original finite curve union with an integral Picard half-class
is the branch ideal on every chart of its constructed finite flat cover.
The actual chart isomorphisms commute with the original union inclusion. -/
theorem selectedPrimeCurve_quadraticBranchCharts
    (N : Finset S.PrimeCurve) (m : Additive S.toScheme.Pic)
    (heven : S.weilClassPicardEquiv (S.weilClassMap (S.selectedPrimeWeil N)) =
      (2 : ℕ) • m) :
    let E := S.selectedPrimeCartier N
    ∃ (L : InvertibleSheaf S.toScheme)
      (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E),
      L.toPic = m.toMul ∧
      let A := effectiveCartierQuadraticAtlas S.toScheme E
        (S.hasRegularCartierEquations_of_effective_weil E (S.selectedPrimeCartier_effective N)) L e
      let J := Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N)
      IsFinite A.morphism ∧ AlgebraicGeometry.Flat A.morphism ∧
        ∀ i, J.ideal ⟨A.opens i, A.affine i⟩ = _root_.KltDP.Geometry.QuadraticCover.branchIdeal (A.sections i) ∧
          ∃ f : J.glueDataObj ⟨A.opens i, A.affine i⟩ ≅ _root_.KltDP.Geometry.QuadraticCover.branchScheme (A.sections i),
            f.hom ≫ _root_.KltDP.Geometry.QuadraticCover.branchι (A.sections i) ≫ (A.affine i).fromSpec =
              J.glueData.ι ⟨A.opens i, A.affine i⟩ ≫ J.gluedTo := by
  dsimp only
  obtain ⟨L, e, hL, hIJ, _, _, _⟩ := S.selectedPrimeCurve_reducedUnion_of_even_picard N m heven
  let E := S.selectedPrimeCartier N
  let hE := S.hasRegularCartierEquations_of_effective_weil E (S.selectedPrimeCartier_effective N)
  let A := effectiveCartierQuadraticAtlas S.toScheme E hE L e
  let I := effectiveCartierIdealData S.toScheme E hE L e
  let J := Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N)
  have hIJ' : I = J := hIJ
  have hfin := InvertibleQuadraticAtlas.fromSquareRoot_finite_flat S.toScheme L
    (cartierDivisorModule S.toScheme E) e (effectiveCartierSection S.toScheme E hE)
  have hcharts (i : AffineOpenRefinement.Index S.toScheme L.localTrivializations.X) :
      I.ideal ⟨A.opens i, A.affine i⟩ = _root_.KltDP.Geometry.QuadraticCover.branchIdeal (A.sections i) :=
    effectiveCartierIdealData_eq_quadraticBranchIdeal S.toScheme E hE L e i
  have hisos (i : AffineOpenRefinement.Index S.toScheme L.localTrivializations.X) :
      ∃ f : I.glueDataObj ⟨A.opens i, A.affine i⟩ ≅ _root_.KltDP.Geometry.QuadraticCover.branchScheme (A.sections i),
        f.hom ≫ _root_.KltDP.Geometry.QuadraticCover.branchι (A.sections i) ≫ (A.affine i).fromSpec =
          I.glueData.ι ⟨A.opens i, A.affine i⟩ ≫ I.gluedTo :=
    ⟨effectiveCartierBranchChartIso S.toScheme E hE L e i,
      effectiveCartierBranchChartIso_hom_toBase S.toScheme E hE L e i⟩
  rw [hIJ'] at hcharts hisos
  exact ⟨L, e, hL, hfin.1, hfin.2, fun i => ⟨hcharts i, hisos i⟩⟩

end Geometry.NormalProjectiveSurface
end KltDP
