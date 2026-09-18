import KltDP.Geometry.CanonicalEulerDefectVanishes
import KltDP.Geometry.RationalPicardIntersection
import KltDP.Codes.NodeParity

/-! Riemann–Roch parity for the original integral Picard intersection form.
The parity is produced from actual cohomology and the original canonical
module isomorphism. No characteristic-class hypothesis is supplied. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

local instance characteristicSourceIntegral : IsIntegral X.toScheme := X.integral

include eK in
/-- The literal original intersection expression has even integral value. -/
theorem cartier_square_sub_canonical_even (D : CartierDivisor X.toScheme) :
    Even (X.intersectionPairing hX D D - X.intersectionPairing hX K D) := by
  have h := X.cartier_euler_riemannRoch_twice hX K eK D
  rw [sub_eq_add_neg, X.intersectionPairing_add_right hX,
    X.intersectionPairing_neg_right hX, X.intersectionPairing_symm hX D K] at h
  refine ⟨eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme D) -
    eulerCharacteristic X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf), ?_⟩
  omega

include eK in
/-- The actual canonical Picard class is characteristic for the original
integer form, by the Cartier representative of every original Picard class. -/
theorem canonicalPicard_isCharacteristic :
    KltDP.Codes.IsCharacteristic (X.integralPicardIntersectionBilinForm hX)
      (cartierPicardHom X.toScheme K) := by
  intro p
  let D := X.picardRepresentative p.toMul
  have hp : cartierPicardHom X.toScheme D = p :=
    congrArg Additive.ofMul (X.cartierPicardClass_picardRepresentative p.toMul)
  rw [← hp, X.integralPicardIntersectionBilinForm_apply,
    X.integralPicardIntersectionBilinForm_apply]
  change Even (X.picardPairing hX (cartierPicardClass X.toScheme D)
      (cartierPicardClass X.toScheme D) -
    X.picardPairing hX (cartierPicardClass X.toScheme K)
      (cartierPicardClass X.toScheme D))
  rw [X.picardPairing_class hX, X.picardPairing_class hX]
  exact X.cartier_square_sub_canonical_even hX K eK D

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.canonicalPicard_isCharacteristic
#print axioms KltDP.Geometry.NormalProjectiveSurface.canonicalPicard_isCharacteristic
