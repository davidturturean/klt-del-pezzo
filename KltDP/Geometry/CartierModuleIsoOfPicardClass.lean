import KltDP.Geometry.CartierPicardHom

/-! Equality of the original Cartier Picard classes gives an actual
isomorphism of the original divisor modules. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- The existing sheaf-isomorphism quotient recovers an actual module
isomorphism from equality of original Cartier Picard classes. -/
theorem cartierModuleIso_of_picardHom_eq (D E : CartierDivisor X)
    (h : cartierPicardHom X D = cartierPicardHom X E) :
    Nonempty (cartierDivisorModule X D ≅ cartierDivisorModule X E) := by
  letI := Scheme.Modules.monoidalCategory X
  have hclass : (cartierPicardClass X D : Skeleton X.Modules) =
      (cartierPicardClass X E : Skeleton X.Modules) :=
    congrArg (fun c : Additive X.Pic => (c.toMul : Skeleton X.Modules)) h
  rw [cartierPicardClass_val, cartierPicardClass_val] at hclass
  exact Quotient.exact hclass

end KltDP.Geometry
