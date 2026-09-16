import KltDP.Geometry.AffineBlowupExceptional
import KltDP.Geometry.GluedIdealInvertible

/-!
# The actual exceptional ideal and conormal are invertible

For every ideal of every commutative ring, the actual Rees blowup has
the already constructed exceptional closed scheme. The regular
equations of its original extended ideal were proved from the Rees
charts. They now imply that its actual global kernel ideal and conormal
module sheaves are locally free of rank one.

There is no domain, nonzero-ideal, invertibility, or projective-twist
identification assumption. Empty blowups or empty exceptional loci are
allowed. Comparison with O(1), the dual normal bundle, and intersection
numbers remains a separate theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineBlowup

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The actual global exceptional ideal module is locally free of rank
one, using the regular equations already derived from the Rees algebra. -/
theorem exceptionalIdealModule_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := (scheme I).ringCatSheaf)
      (exceptionalIdealModule I) :=
  gluedKernel_isInvertible (exceptionalIdeal I)
    (exceptionalIdeal_locallyPrincipalRegular I)

/-- The actual global exceptional conormal is locally free of rank one
on the actual exceptional closed scheme. -/
theorem exceptionalConormalSheaf_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := (exceptionalScheme I).ringCatSheaf)
      (exceptionalConormalSheaf I) :=
  gluedConormal_isInvertible (exceptionalIdeal I)
    (exceptionalIdeal_locallyPrincipalRegular I)

/-- The exceptional ideal as an actual invertible sheaf on the blowup. -/
def exceptionalIdealLine : InvertibleSheaf (scheme I) :=
  ⟨exceptionalIdealModule I, exceptionalIdealModule_isInvertible I⟩

/-- The conormal as an actual invertible sheaf on the exceptional scheme. -/
def exceptionalConormalLine : InvertibleSheaf (exceptionalScheme I) :=
  ⟨exceptionalConormalSheaf I, exceptionalConormalSheaf_isInvertible I⟩

end KltDP.Geometry.AffineBlowup
