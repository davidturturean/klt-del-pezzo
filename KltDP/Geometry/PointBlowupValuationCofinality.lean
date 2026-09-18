import KltDP.Geometry.CommonProperModelValuationPrime
import KltDP.Geometry.BirationalModelAffineNeighborhoodCompletion
import KltDP.Geometry.OpenImmersionValuationPoint

/-!
# Point-blowup detection of valuation primes on arbitrary birational models

An original finite-type integral birational model need not be proper.
Its original valuation point has an affine neighborhood in the constructed
proper integral completion. The original open stalk isomorphisms preserve
the valuation and local dimension. Common domination and prime detection
then produce an actual prime on point blowups of the given smooth model.

All maps to the original surface and the original point equation remain
in the conclusion. No completion, resolution, divisor realization, or
canonical-discrepancy compatibility is supplied as an assumption.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry

attribute [local instance] integralSchemeStalk_isDomain

/-- Every original codimension-one valuation point on an integral
finite-type birational model is detected after actual point blowups of
the given smooth model, through a completion of its original neighborhood. -/
theorem exists_pointBlowup_detection_of_valuation_point
    {k : Type u} [Field k] [IsAlgClosed k]
    (T X : NormalProjectiveSurface k) [IsSmooth T.structureMorphism]
    {V : Scheme.{u}} [IsIntegral V]
    (t : T.toScheme ⟶ X.toScheme) (v : V ⟶ X.toScheme)
    [LocallyOfFiniteType (v ≫ X.structureMorphism)]
    (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)
    (htk : t ≫ X.structureMorphism = T.structureMorphism)
    (x : CodimensionOnePoint V) [ValuationRing (V.presheaf.stalk x.val)] :
    ∃ (U : V.Opens) (_ : IsAffineOpen U) (hx : x.val ∈ U)
        (Z : Scheme.{u}) (j : U.toScheme ⟶ Z) (p : Z ⟶ X.toScheme)
        (hZ : IsIntegral Z),
      letI := hZ
      ∃ (S : NormalProjectiveSurface k) (b : S.toScheme ⟶ T.toScheme)
          (q : S.toScheme ⟶ Z) (D : S.PrimeCurve),
        IsOpenImmersion j ∧ IsProper p ∧ IsBirationalScheme p ∧
        j ≫ p = U.ι ≫ v ∧ IsResolution S T b ∧ IsSmooth S.structureMorphism ∧
        IsPointBlowupSequence S T b ∧ IsBirationalScheme q ∧ IsProper q ∧
        q ≫ (p ≫ X.structureMorphism) = S.structureMorphism ∧
        q ≫ p = b ≫ t ∧ q.base D.genericPoint = j.base ⟨x.val, hx⟩ ∧
        IsIso (q.stalkMap D.genericPoint) ∧
        q.base '' (D : Set S.toScheme) = closure ({j.base ⟨x.val, hx⟩} : Set Z) := by
  letI : IsProper X.structureMorphism := X.projective.isProper
  letI : IsSeparated X.structureMorphism := inferInstance
  obtain ⟨U, hU, hx, n, Z, j, i, hZ, h⟩ :=
    BirationalModelAffineNeighborhoodCompletion.exists_completion_near_point
      X.structureMorphism v hv x.val
  letI := hZ
  obtain ⟨hgeneric, hj, hi, hproperp, hbirp, hjp, hpoint, hclosure⟩ := h
  letI : IsOpenImmersion j := hj
  letI : Nonempty U.toScheme := ⟨⟨x.val, hx⟩⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let p := i ≫ pullback.snd (projectiveSpaceToSpec k n) X.structureMorphism
  letI : IsProper p := hproperp
  let xU : CodimensionOnePoint U.toScheme :=
    (codimensionOnePointOpenEquiv U).symm ⟨x, hx⟩
  letI : ValuationRing (U.toScheme.presheaf.stalk xU.val) :=
    (OpenImmersionValuationPoint.stalk_valuationRing_iff U.ι xU.val).mp
      (by change ValuationRing (V.presheaf.stalk x.val); infer_instance)
  let xZ : CodimensionOnePoint Z := OpenImmersionValuationPoint.mapPoint j xU
  letI : ValuationRing (Z.presheaf.stalk xZ.val) :=
    (OpenImmersionValuationPoint.stalk_valuationRing_iff j xU.val).mpr inferInstance
  obtain ⟨S, b, q, D, hbR, hsmooth, hseq, hbirq, hproperq,
    hqk, hfac, hD, hstalk, himage⟩ :=
    exists_pointBlowup_prime_above_proper_valuation_point T X t p ht hbirp htk xZ
  exact ⟨U, hU, hx, Z, j, p, hZ, S, b, q, D,
    hj, hproperp, hbirp, hjp, hbR, hsmooth, hseq, hbirq, hproperq,
    hqk, hfac, hD, hstalk, himage⟩

end KltDP.Geometry

#check @KltDP.Geometry.exists_pointBlowup_detection_of_valuation_point
#print axioms KltDP.Geometry.exists_pointBlowup_detection_of_valuation_point
