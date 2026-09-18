import KltDP.Geometry.CompatibleCanonicalDifferenceSupport
import KltDP.Geometry.ExceptionalQCartierIntersection
import KltDP.Geometry.MinimalCompatibleCanonicalDegree
import KltDP.Geometry.ActualExceptionalStieltjes

/-!
# Nonpositive discrepancies of an actual minimal resolution

The literal compatible canonical difference supplies its own finite support.
Its primes are contracted by the original map, and its original intersection
degrees equal the source canonical degrees. Actual rational exceptional
curves on the minimal resolution give nonnegative degrees. The proved
Stieltjes theorem for the original exceptional matrix then gives the signs.

Rationality is supplied by actual projective-line isomorphisms over the field;
general rationality of klt exceptional curves is a separate obligation.
The negative-matrix argument retains the selected isolated Hodge dependency.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory Matrix
universe u

namespace KltDP.Geometry.MinimalResolutionDiscrepancy

open NormalProjectiveSurface BirationalWeilPushforward

private theorem coefficient_nonpos_of_degrees
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π]
    (hbir : IsBirationalScheme π)
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
    (KS : CartierDivisor S.toScheme) (KX : X.WeilDivisor)
    (hK : X.QCartier (rationalizeWeilDivisor X KX))
    (hpush : pushforward π hbir (S.cartierToWeilHom KS) = KX)
    (hdegree : ∀ C : S.PrimeCurve, IsExceptionalCurve π C →
      0 ≤ C.intersectionNumber KS) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    ∀ C : S.PrimeCurve,
      (S.rationalCartierToWeilHom KS -
        QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hK) C ≤ 0 := by
  classical
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let Δ : S.RationalWeilDivisor := S.rationalCartierToWeilHom KS -
    QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hK
  have hsupport : (Δ.support : Set S.PrimeCurve) ⊆ {C | IsExceptionalCurve π C} :=
    difference_support_subset_exceptional π hbir KS KX hK hpush
  have hrows : ∀ i : Δ.support, 0 ≤
      (NullCurveIntersectionMatrix.intersectionMatrix S hregular
        (fun E : Δ.support => E.val) *ᵥ (fun E : Δ.support => Δ E.val)) i := by
    intro i
    rw [RationalWeilIntersection.intersectionMatrix_mulVec_support]
    change 0 ≤ RationalWeilIntersection.degreeLinearMap S hregular i.val
      (S.rationalCartierToWeilHom KS -
        QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hK)
    rw [RationalWeilIntersection.degreeLinearMap_difference hregular π hπ
      KS (rationalizeWeilDivisor X KX) hK i.val (hsupport i.property)]
    exact_mod_cast hdegree i.val (hsupport i.property)
  have hn := ActualExceptionalStieltjes.coeff_nonpositive_of_nonnegative_intersections
    π hπ hbir hregular (fun E : Δ.support => E.val) Subtype.val_injective
    (fun E => hsupport E.property) (fun E : Δ.support => Δ E.val) hrows
  change ∀ C : S.PrimeCurve, Δ C ≤ 0
  intro C
  by_cases hC : C ∈ Δ.support
  · exact hn ⟨C, hC⟩
  · exact le_of_eq (Finsupp.not_mem_support_iff.mp hC)

/-- Every original prime coefficient of the compatible canonical difference
is nonpositive on an actual minimal resolution with rational exceptional
primes. No support, discrepancy equation, sign or matrix property is assumed. -/
theorem coefficient_nonpos
    {k : Type u} [Field k] [IsAlgClosed k]
    (S X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    (π : S.toScheme ⟶ X.toScheme) (hmin : IsMinimalResolution S X π)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (KX : X.WeilDivisor) (hK : X.QCartier (rationalizeWeilDivisor X KX))
    (hrational : ∀ C : S.PrimeCurve, IsExceptionalCurve π C →
      ∃ e : C.toScheme ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec) :
    letI : IsProper π := hmin.toIsResolution.isProper
    let hbir : IsBirationalScheme π :=
      (isBirational_iff_isBirationalScheme π).mp hmin.birational
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    pushforward π hbir (S.cartierToWeilHom KS) = KX →
    ∀ C : S.PrimeCurve,
      (S.rationalCartierToWeilHom KS -
        QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hK) C ≤ 0 := by
  letI : IsProper π := hmin.toIsResolution.isProper
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hmin.birational
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  change pushforward π hbir (S.cartierToWeilHom KS) = KX →
    ∀ C : S.PrimeCurve,
      (S.rationalCartierToWeilHom KS -
        QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hK) C ≤ 0
  intro hpush
  apply coefficient_nonpos_of_degrees π hbir hmin.over_base hmin.regular KS KX hK hpush
  intro C hC
  obtain ⟨e, he⟩ := hrational C hC
  exact hmin.canonical_degree_nonneg_of_rational_exceptional KS eKS C hC e he

end KltDP.Geometry.MinimalResolutionDiscrepancy

#check @KltDP.Geometry.MinimalResolutionDiscrepancy.coefficient_nonpos
#print axioms KltDP.Geometry.MinimalResolutionDiscrepancy.coefficient_nonpos
