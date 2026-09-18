import KltDP.Geometry.CanonicalWeilBirationalRepresentative
import KltDP.Geometry.KltOriginalDiscrepancyBound
import KltDP.Geometry.RationalWeilIntersectionFamily
import KltDP.Geometry.ActualExceptionalStieltjes
import KltDP.Geometry.ArithmeticCurveAdjunction
import KltDP.LinearAlgebra.ExceptionalGenusZero

/-!
# Arithmetic genus zero for the original exceptional curves

The actual klt surface supplies a compatible canonical representative and
strictly klt discrepancies on the original resolution. Arithmetic adjunction
gives the canonical rows even for singular exceptional curves. The literal
integral exceptional matrix is negative definite with nonnegative off-diagonal
entries, so the proved Schur induction forces every arithmetic genus to vanish.

No rationality, exceptional-curve smoothness, discrepancy upper bound,
minimality, matrix equation, or genus premise is supplied. A genuine resolution
and smooth source remain inputs. This retains the existing isolated surface
Riemann--Roch and Hodge dependencies; it does not assert a projective-line
isomorphism or construct a resolution.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory Matrix
universe u

namespace KltDP.Geometry

open NormalProjectiveSurface

/-- Every actual contracted prime on a smooth resolution of the original
klt surface has arithmetic genus zero, without minimality or rationality inputs. -/
theorem IsResolution.exceptional_arithmetic_genus_zero_of_klt
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {π : S.toScheme ⟶ X.toScheme} (hres : IsResolution S X π)
    (hklt : IsKlt X) :
    ∀ C : S.PrimeCurve, IsExceptionalCurve π C → CurveCanonical.genus C.toSpec = 0 := by
  classical
  letI : IsProper π := hres.isProper
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hres.birational
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let I := {C : S.PrimeCurve // IsExceptionalCurve π C}
  letI : Fintype I := (exceptionalCurves_finite_of_proper_birational π hbir).fintype
  let C : I → S.PrimeCurve := Subtype.val
  let M := NullCurveIntersectionMatrix.intersectionMatrix S hres.regular C
  let g : I → ℕ := fun i => CurveCanonical.genus (C i).toSpec
  obtain ⟨KX, hKX⟩ := hklt
  obtain ⟨KS, ⟨eKS⟩, hpush⟩ :=
    IsCanonicalWeilDivisor.exists_compatible_canonical_cartier
      S X π hres.over_base hbir KX hKX.1
  let Δ : S.RationalWeilDivisor := S.rationalCartierToWeilHom KS -
    QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hKX.2.1
  let d : I → ℚ := fun i => Δ (C i)
  have hlower (i : I) : -1 < d i :=
    KltOriginalDiscrepancyBound.coefficient_gt_neg_one S X π hbir hres.over_base
      KS eKS KX hKX hpush (C i)
  have hrow : M *ᵥ d = fun i => 2 * (g i : ℚ) - 2 - M i i := by
    funext i
    have hri := RationalWeilIntersection.intersectionMatrix_mulVec_compatible_difference
      hres.regular π hbir hres.over_base KS KX hKX.2.1 hpush
      C Subtype.val_injective (fun E => E.property)
      (fun E hE => ⟨⟨E, hE⟩, rfl⟩) i
    change (NullCurveIntersectionMatrix.intersectionMatrix S hres.regular C *ᵥ d) i =
      2 * (CurveCanonical.genus (C i).toSpec : ℚ) - 2 -
        NullCurveIntersectionMatrix.intersectionMatrix S hres.regular C i i
    rw [hri]
    change ((C i).intersectionNumber KS : ℚ) =
      2 * (CurveCanonical.genus (C i).toSpec : ℚ) - 2 -
        (S.intersectionPairing hres.regular
          (S.primeCurveCartier hres.regular (C i))
          (S.primeCurveCartier hres.regular (C i)) : ℚ)
    rw [S.intersectionPairing_primeCurve hres.regular]
    exact_mod_cast S.arithmetic_canonical_degree hres.regular KS eKS (C i)
  have hpos : (-M).PosDef :=
    ActualExceptionalStieltjes.negativeIntersectionMatrix_posDef
      π hres.over_base hbir hres.regular C Subtype.val_injective (fun E => E.property)
  have hintegral (i j : I) : ∃ z : ℤ, M i j = z :=
    ⟨S.intersectionPairing hres.regular
      (S.primeCurveCartier hres.regular (C i))
      (S.primeCurveCartier hres.regular (C j)), rfl⟩
  have hoff (i j : I) (hij : i ≠ j) : 0 ≤ M i j := by
    have h := ActualExceptionalStieltjes.negativeIntersectionMatrix_offDiagonal
      hres.regular C Subtype.val_injective i j hij
    exact neg_nonpos.mp h
  have hzero := KltDP.LinearAlgebra.ExceptionalGenusZero.genus_zero
    M hpos hintegral hoff g d hlower hrow
  intro E hE
  exact hzero ⟨E, hE⟩

end KltDP.Geometry

#check @KltDP.Geometry.IsResolution.exceptional_arithmetic_genus_zero_of_klt
#print axioms KltDP.Geometry.IsResolution.exceptional_arithmetic_genus_zero_of_klt
