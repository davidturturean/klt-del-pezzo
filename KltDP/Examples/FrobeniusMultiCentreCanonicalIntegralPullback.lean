import KltDP.Examples.FrobeniusMultiCentreCanonicalIntegralRelation
import KltDP.Examples.FrobeniusMultiCentreContractingNef
import KltDP.Geometry.InvertibleSheafSectionPowers
import KltDP.Geometry.SchemeKernelIdealIsoTransport

/-!
# Multiplication and original pullback substitution in the source canonical relation

An actual isomorphism between the pullback of a target line and the m-th
power of the original contracting line gives the class m M. Substitute
that equality in the multiplied original source relation. These statements
remain in the source Picard group; no target canonical or divisor-pushforward
claim is made. The identities hold for every natural m, hence for the
positive m provided by the original contraction witness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalIntegralPullback

open KltDP.Geometry
open FrobeniusMultiCentreSurface FrobeniusMultiCentreCanonicalOpenComparison
open FrobeniusMultiCentreGraphCartierStrict FrobeniusMultiCentreFiberGlobalClass
open FrobeniusMultiCentreContractingClass FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreCanonicalIntegralRelation
open InvertibleSheafSectionPowers SchemeKernelIdealIsoTransport

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)

/-- Multiply the actual integral source relation by the natural exponent.
Integer coefficients retain all signs and the exponent m. -/
theorem canonical_integral_relation_mul (m : ℕ) :
    let p : ℤ := (q + 1 : ℕ)
    let r : ℤ := (n : ℤ) - 2
    let s : ℤ := p * r
    let d : ℤ := 2 - (p - 2) * r
    ((m : ℤ) * s) • multiCanonicalClass (q + 1) n a ha +
      ((m : ℤ) * (s - 2)) •
        (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) +
      ((m : ℤ) * (r * (p - 2))) •
        (∑ i : Fin n, -Additive.ofMul (fiberKernelLine q n a ha i).toPic) +
      ((m : ℤ) * d) • contractingClass q n a ha = 0 := by
  have h := congrArg
    (fun x : Additive (multiSurface (q + 1) n a).Pic => (m : ℤ) • x)
    (canonical_integral_relation q n a ha)
  simpa only [smul_add, smul_smul, smul_zero] using h

variable (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))
    {Y : Scheme.{u}} (π : multiSurface (q + 1) n a ⟶ Y)
    (A : InvertibleSheaf Y) (m : ℕ)
    (e : (pullbackInvertibleSheaf π A).obj ≅
      (power (contractingLine q n a ha hproj) m).obj)

include hproj e in
/-- The actual pullback-line isomorphism gives m times the original class M.
No equality of Picard classes is supplied as a premise. -/
theorem pullback_class_eq_smul :
    (schemePicardPullbackHom π).toAdditive (Additive.ofMul A.toPic) =
      (m : ℤ) • contractingClass q n a ha := by
  change Additive.ofMul (schemePicardPullbackHom π A.toPic) = _
  rw [schemePicardPullbackHom_toPic,
    toPic_eq_of_iso (pullbackInvertibleSheaf π A)
      (power (contractingLine q n a ha hproj) m) e, power_toPic,
    _root_.ofMul_pow]
  simpa only [natCast_zsmul] using
    congrArg (fun c : Additive (multiSurface (q + 1) n a).Pic => m • c)
      (contractingLine_class q n a ha hproj)

include hproj e in
/-- Replace m M by the class of the original pulled-back target line.
The coefficient of K is m p(n-2), while the coefficient of the target line
is d. Subsequent descent therefore retains the quotient -t/m. -/
theorem canonical_integral_relation_of_pullback_power :
    let p : ℤ := (q + 1 : ℕ)
    let r : ℤ := (n : ℤ) - 2
    let s : ℤ := p * r
    let d : ℤ := 2 - (p - 2) * r
    ((m : ℤ) * s) • multiCanonicalClass (q + 1) n a ha +
      ((m : ℤ) * (s - 2)) •
        (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) +
      ((m : ℤ) * (r * (p - 2))) •
        (∑ i : Fin n, -Additive.ofMul (fiberKernelLine q n a ha i).toPic) +
      d • (schemePicardPullbackHom π).toAdditive (Additive.ofMul A.toPic) = 0 := by
  dsimp only
  rw [pullback_class_eq_smul q n a ha hproj π A m e, smul_smul]
  simpa only [mul_comm] using canonical_integral_relation_mul q n a ha m

end KltDP.Examples.FrobeniusMultiCentreCanonicalIntegralPullback
