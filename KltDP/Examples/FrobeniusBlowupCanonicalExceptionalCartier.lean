import KltDP.Examples.FrobeniusBlowupCanonicalPicard
import KltDP.Geometry.AffineBlowupIntegral
import KltDP.Geometry.EffectiveCartierOfInvertibleIdeal

/-!
# The canonical Picard formula with the original exceptional Cartier divisor

Integrality follows from the original nonzero center ideal. Its already
proved regular Rees equations construct the actual exceptional Cartier
divisor, with ideal data equal to the original exceptional ideal. The
accepted ideal-line sign comparison turns the differential factorization
into K_new = pullback K_old + E in the original Picard group.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusBlowupCanonicalExceptionalCartier

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open KltDP.Geometry.SmoothSurfaceKaehlerAtlas
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupCanonicalPicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

private theorem originalCenter_ne_bot : centerIdeal (k := k) ≠ ⊥ := by
  intro h
  have hu : uCoord (k := k) ∈ centerIdeal := (centerU (k := k)).property
  rw [h, Ideal.mem_bot] at hu
  exact uCoord_ne_zero hu

local instance originalBlowupIntegral : IsIntegral (scheme (centerIdeal (k := k))) :=
  scheme_isIntegral centerIdeal (originalCenter_ne_bot (k := k))

/-- The actual exceptional Cartier divisor is constructed from the original exceptional ideal. -/
def originalExceptionalCartier : CartierDivisor (scheme (centerIdeal (k := k))) :=
  cartierDivisorOfIdeal (scheme centerIdeal) (exceptionalIdeal centerIdeal)
    (exceptionalIdeal_locallyPrincipalRegular centerIdeal)

/-- The original Rees equations are regular equations for this same Cartier divisor. -/
theorem originalExceptionalCartier_regular :
    HasRegularCartierEquations (scheme (centerIdeal (k := k)))
      (originalExceptionalCartier (k := k)) :=
  cartierDivisorOfIdeal_hasRegularEquations (scheme centerIdeal) (exceptionalIdeal centerIdeal)
    (exceptionalIdeal_locallyPrincipalRegular centerIdeal)

/-- Its actual ideal data are exactly the original exceptional ideal data. -/
theorem originalExceptionalCartier_idealData :
    effectiveCartierIdealDataOfRegularEquations (scheme (centerIdeal (k := k)))
        (originalExceptionalCartier (k := k)) (originalExceptionalCartier_regular (k := k)) =
      exceptionalIdeal centerIdeal :=
  cartierDivisorOfIdeal_idealData (scheme centerIdeal) (exceptionalIdeal centerIdeal)
    (exceptionalIdeal_locallyPrincipalRegular centerIdeal)

/-- The original effective exceptional divisor has the negative ideal-line Picard class. -/
theorem originalExceptionalCartier_picard :
    cartierPicardHom (scheme (centerIdeal (k := k))) (originalExceptionalCartier (k := k)) =
      -Additive.ofMul (exceptionalIdealLine (centerIdeal (k := k))).toPic :=
  cartierDivisorOfIdeal_picard (scheme centerIdeal) (exceptionalIdeal centerIdeal)
    (exceptionalIdeal_locallyPrincipalRegular centerIdeal)

/-- The actual one-step canonical formula, with its original exceptional Cartier divisor. -/
theorem canonicalSheafPicard_formula_exceptional :
    Additive.ofMul (canonicalSheafOfSmoothSurface (blowupStructure (k := k))).toPic =
      Additive.ofMul (schemePicardPullbackHom (toSpec centerIdeal)
        (canonicalSheafOfSmoothSurface (planeStructure (k := k))).toPic) +
        cartierPicardHom (scheme (centerIdeal (k := k))) (originalExceptionalCartier (k := k)) := by
  rw [originalExceptionalCartier_picard, ← sub_eq_add_neg]
  exact canonicalSheafPicard_formula (k := k)

end KltDP.Examples.FrobeniusBlowupCanonicalExceptionalCartier
