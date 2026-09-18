import KltDP.Geometry.CommonResolutionFromSmoothModel
import KltDP.Geometry.BirationalPrimeCorrespondence

/-!
# Detect an original model's prime on a point-blowup common resolution

The prime on the given projective normal birational model lifts to an actual
prime on the common smooth resolution obtained by blowing up the given smooth
model. The original morphism identifies their generic-point stalks, and maps
the entire lifted curve onto the given curve. This is the geometric detection
step; no discrepancy coefficient or klt assertion is assumed or concluded.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- Every prime on an original projective normal birational model is detected
on a point-blowup sequence from the given smooth model, through the original
proper birational comparison and its actual isomorphism of generic stalks. -/
theorem exists_pointBlowup_common_resolution_prime
    {k : Type u} [Field k] [IsAlgClosed k]
    (T V X : NormalProjectiveSurface k) [IsSmooth T.structureMorphism]
    (t : T.toScheme ⟶ X.toScheme) (v : V.toScheme ⟶ X.toScheme)
    (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)
    (htk : t ≫ X.structureMorphism = T.structureMorphism)
    (hvk : v ≫ X.structureMorphism = V.structureMorphism) (C : V.PrimeCurve) :
    ∃ (S : NormalProjectiveSurface k) (b : S.toScheme ⟶ T.toScheme)
        (q : S.toScheme ⟶ V.toScheme) (D : S.PrimeCurve),
      IsResolution S T b ∧ IsResolution S V q ∧ IsSmooth S.structureMorphism ∧
      IsPointBlowupSequence S T b ∧ q ≫ v = b ≫ t ∧
      q.base D.genericPoint = C.genericPoint ∧ IsIso (q.stalkMap D.genericPoint) ∧
      q.base '' (D : Set S.toScheme) = (C : Set V.toScheme) := by
  obtain ⟨S, b, q, hbR, hqR, hsmooth, hseq, haway, hiso, hfac, j, hjb, hjq⟩ :=
    exists_common_resolution_of_smooth_model T V X t v ht hv htk hvk
  letI : IsProper q := hqR.isProper
  have hbirq : IsBirationalScheme q :=
    (isBirational_iff_isBirationalScheme q).mp hqR.birational
  let D : S.PrimeCurve := BirationalPrimeCorrespondence.abovePrimeCurve q hbirq C
  exact ⟨S, b, q, D, hbR, hqR, hsmooth, hseq, hfac,
    BirationalPrimeCorrespondence.abovePrimeCurve_map_genericPoint q hbirq C,
    BirationalPrimeCorrespondence.abovePrimeCurve_stalkMap_isIso q hbirq C,
    BirationalPrimeCorrespondence.abovePrimeCurve_image q hbirq C⟩

end KltDP.Geometry

#check @KltDP.Geometry.exists_pointBlowup_common_resolution_prime
#print axioms KltDP.Geometry.exists_pointBlowup_common_resolution_prime
