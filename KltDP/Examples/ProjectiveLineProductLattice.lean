import KltDP.Examples.ProjectiveLineProductPicardCoordinates
import KltDP.Geometry.RationalPicardIntersection
import KltDP.Geometry.NumericalSpaceRank

/-!
# The original product Picard lattice is unimodular

The existing ruling equivalence and original intersection values identify
the integral Picard pairing of P1 x P1 with the hyperbolic plane. The dual
bijection below is the one in the original PicardUnimodular definition.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
universe u

namespace KltDP.Examples.ProjectiveLineProductLattice

open KltDP.Geometry KltDP.Geometry.PrimeCurveClassPairing
open FrobeniusProjectivePoints FrobeniusStageZeroProjective
open FrobeniusGraphPicardClassFiberClasses FrobeniusRulingClassPairing
open FrobeniusRulingPairingValues ProjectiveLineProductPicardGeneration

variable {k : Type u} [Field k] [IsAlgClosed k]

private abbrev originalForm : LinearMap.BilinForm ℤ (Additive (projectiveProduct k).Pic) :=
  (projectiveProductSurface (k := k)).integralPicardIntersectionBilinForm baseRegular

private theorem originalForm_eq (p q : Additive (projectiveProduct k).Pic) :
    originalForm p q = basePairing p q :=
  (projectiveProductSurface (k := k)).integralPicardIntersectionBilinForm_apply baseRegular p q

/-- The coordinates are those of the existing original ruling Picard equivalence. -/
theorem pairing_coordinates (x y : ℤ × ℤ) :
    basePairing (rulingPicardEquiv (k := k) x) (rulingPicardEquiv y) =
      x.1 * y.2 + x.2 * y.1 := by
  have h11 : originalForm (firstFiberClass (k := k)) firstFiberClass = 0 :=
    (originalForm_eq _ _).trans basePairing_first_self_zero
  have h12 : originalForm (firstFiberClass (k := k)) secondFiberClass = 1 :=
    (originalForm_eq _ _).trans basePairing_first_second_one
  have h21 : originalForm (secondFiberClass (k := k)) firstFiberClass = 1 :=
    (originalForm_eq _ _).trans basePairing_second_first_one
  have h22 : originalForm (secondFiberClass (k := k)) secondFiberClass = 0 :=
    (originalForm_eq _ _).trans basePairing_second_self_zero
  rw [← originalForm_eq]
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rw [rulingPicardEquiv_apply, rulingPicardEquiv_apply]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply,
    zsmul_eq_mul, h11, h12, h21, h22]
  ring
  change c * b + a * d = a * d + b * c
  ring

private theorem dual_bijective {A : Type*} [AddCommGroup A]
    (B : LinearMap.BilinForm ℤ A) (e : ℤ × ℤ ≃+ A)
    (hB : ∀ x y, B (e x) (e y) = x.1 * y.2 + x.2 * y.1) :
    Function.Bijective (fun a => (B a).toAddMonoidHom) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    apply congrArg e
    apply Prod.ext
    · have h := congrArg (fun f : A →+ ℤ => f (e (0, 1))) hab
      change B (e x) (e (0, 1)) = B (e y) (e (0, 1)) at h
      simpa only [hB, mul_one, mul_zero, add_zero] using h
    · have h := congrArg (fun f : A →+ ℤ => f (e (1, 0))) hab
      change B (e x) (e (1, 0)) = B (e y) (e (1, 0)) at h
      simpa only [hB, mul_one, mul_zero, zero_add] using h
  · intro f
    refine ⟨e (f (e (0, 1)), f (e (1, 0))), ?_⟩
    apply AddMonoidHom.ext
    intro a
    obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective a
    change B (e _) (e (x, y)) = f (e (x, y))
    rw [hB]
    change f (e (0, 1)) * y + f (e (1, 0)) * x = f (e (x, y))
    have hxy : (x, y) = x • (1, 0) + y • (0, 1) := by
      ext <;> simp [zsmul_eq_mul]
    rw [hxy, map_add, map_zsmul, map_zsmul, map_add, map_zsmul, map_zsmul]
    simp only [zsmul_eq_mul]
    ring
    change f (e (0, 1)) * y + f (e (1, 0)) * x =
      f (e (0, 1)) * y + f (e (1, 0)) * x
    rfl

/-- Unimodularity of the actual integral Picard intersection pairing. -/
theorem picardUnimodular :
    (projectiveProductSurface (k := k)).PicardUnimodular baseRegular := by
  have h := dual_bijective (originalForm (k := k)) rulingPicardEquiv
    (fun x y => (originalForm_eq _ _).trans (pairing_coordinates x y))
  change Function.Bijective _
  convert h using 1
  funext p
  apply AddMonoidHom.ext
  intro q
  exact (originalForm_eq p q).symm

end KltDP.Examples.ProjectiveLineProductLattice

#check @KltDP.Examples.ProjectiveLineProductLattice.pairing_coordinates
#check @KltDP.Examples.ProjectiveLineProductLattice.picardUnimodular
#print axioms KltDP.Examples.ProjectiveLineProductLattice.picardUnimodular
