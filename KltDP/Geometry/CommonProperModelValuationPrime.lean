import KltDP.Geometry.CommonSmoothProperModel
import KltDP.Geometry.ProperBirationalValuationPrime

/-!
# Detect a proper model's valuation prime after actual point blowups

The target model is any proper integral birational model of the original
surface. The point has its original one-dimensional valuation stalk.
The existing common domination gives actual point blowups of the given
smooth surface, and the valuation-point theorem detects the original point
by an actual prime on that common smooth projective source.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

attribute [local instance] integralSchemeStalk_isDomain

/-- Every original codimension-one valuation point on an arbitrary proper
integral model is detected on point blowups of the given smooth model. -/
theorem exists_pointBlowup_prime_above_proper_valuation_point
    {k : Type u} [Field k] [IsAlgClosed k]
    (T X : NormalProjectiveSurface k) [IsSmooth T.structureMorphism]
    {V : Scheme.{u}} [IsIntegral V]
    (t : T.toScheme ⟶ X.toScheme) (v : V ⟶ X.toScheme) [IsProper v]
    (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)
    (htk : t ≫ X.structureMorphism = T.structureMorphism)
    (x : CodimensionOnePoint V) [ValuationRing (V.presheaf.stalk x.val)] :
    ∃ (S : NormalProjectiveSurface k) (b : S.toScheme ⟶ T.toScheme)
        (q : S.toScheme ⟶ V) (D : S.PrimeCurve),
      IsResolution S T b ∧ IsSmooth S.structureMorphism ∧
      IsPointBlowupSequence S T b ∧ IsBirationalScheme q ∧ IsProper q ∧
      q ≫ (v ≫ X.structureMorphism) = S.structureMorphism ∧
      q ≫ v = b ≫ t ∧ q.base D.genericPoint = x.val ∧
      IsIso (q.stalkMap D.genericPoint) ∧
      q.base '' (D : Set S.toScheme) = closure ({x.val} : Set V) := by
  obtain ⟨S, b, q, hbR, hsmooth, hseq, hbirq, hproperq,
    hqk, haway, hiso, hfac, j, hjb, hjq⟩ :=
    exists_common_smooth_projective_domination T X t v ht hv htk
  letI : IsProper q := hproperq
  obtain ⟨D, hD, hstalk, himage⟩ :=
    ProperBirationalValuationPrime.exists_prime_above_valuation_point S q hbirq x
  exact ⟨S, b, q, D, hbR, hsmooth, hseq, hbirq, hproperq,
    hqk, hfac, hD, hstalk, himage⟩

end KltDP.Geometry

#check @KltDP.Geometry.exists_pointBlowup_prime_above_proper_valuation_point
#print axioms KltDP.Geometry.exists_pointBlowup_prime_above_proper_valuation_point
