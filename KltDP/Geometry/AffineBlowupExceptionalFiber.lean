import KltDP.Geometry.ExtendedIdealFiber
import KltDP.Geometry.AffineBlowupExceptional

/-!
# The global exceptional scheme is the literal center fiber

The exceptional scheme already used for the global kernel and conormal
sheaves is the gluing of quotient charts of the actual extended center.
The general extended-ideal comparison identifies it with the actual
categorical center fiber. Its morphism into the blowup is preserved.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineBlowup

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The actual exceptional closed scheme and the actual categorical
center fiber are isomorphic through their original quotient charts. -/
def exceptionalFiberIso : exceptionalScheme I ≅ centerFiber I :=
  ExtendedIdealFiber.iso I (toSpec I)

/-- The isomorphism preserves the actual exceptional inclusion. -/
@[simp] theorem exceptionalFiberIso_hom_ι :
    (exceptionalFiberIso I).hom ≫ centerFiberι I = exceptionalι I :=
  ExtendedIdealFiber.iso_hom_ι I (toSpec I)

/-- The inverse preserves the actual fiber projection. -/
@[simp] theorem exceptionalFiberIso_inv_ι :
    (exceptionalFiberIso I).inv ≫ exceptionalι I = centerFiberι I :=
  ExtendedIdealFiber.iso_inv_ι I (toSpec I)

end KltDP.Geometry.AffineBlowup
