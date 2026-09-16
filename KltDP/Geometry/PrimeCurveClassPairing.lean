import KltDP.Geometry.IntersectionPairingSymmetry
import KltDP.Geometry.PrimeCurveTransversalPoint
import KltDP.Geometry.KernelLinePullbackOffRange

/-!
# The symmetric Picard pairing in additive notation and its actual curve classes

This repackages the accepted symmetric Picard pairing on a regular surface. The class of a prime
curve is compared with its actual kernel ideal using the accepted Cartier/kernel adapter. A
kernel line has degree zero along a curve disjoint from its closed immersion, through the actual
trivialization on the complement. No intersection value or class identification is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PrimeCurveClassPairing

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open KltDP.Geometry.PrimeCurveTransversalPoint KltDP.Geometry.KernelLinePullbackOffRange

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The existing symmetric Picard pairing, written with additive Picard classes. -/
def pairing (p q : Additive X.toScheme.Pic) : ℤ :=
  X.picardPairing hregular p.toMul q.toMul

theorem pairing_symm (p q : Additive X.toScheme.Pic) :
    pairing X hregular p q = pairing X hregular q p :=
  X.picardPairing_symm hregular p.toMul q.toMul

theorem pairing_add_left (p p' q : Additive X.toScheme.Pic) :
    pairing X hregular (p + p') q = pairing X hregular p q + pairing X hregular p' q :=
  X.picardPairing_mul_left_of_regular hregular p.toMul p'.toMul q.toMul

theorem pairing_add_right (p q q' : Additive X.toScheme.Pic) :
    pairing X hregular p (q + q') = pairing X hregular p q + pairing X hregular p q' :=
  X.picardPairing_mul_right_of_regular hregular p.toMul q.toMul q'.toMul

theorem pairing_zero_left (q : Additive X.toScheme.Pic) : pairing X hregular 0 q = 0 := by
  have h := pairing_add_left X hregular 0 0 q
  simp only [zero_add] at h
  omega

theorem pairing_nsmul_left (n : ℕ) (p q : Additive X.toScheme.Pic) :
    pairing X hregular (n • p) q = (n : ℤ) * pairing X hregular p q := by
  induction n with
  | zero => simp only [zero_nsmul, pairing_zero_left, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [succ_nsmul, pairing_add_left, ih, Nat.cast_add, Nat.cast_one]
    ring

/-- Pairing with the Cartier class of a prime curve is its actual restriction-degree homomorphism. -/
theorem pairing_primeCurve_right (C : X.PrimeCurve) (p : Additive X.toScheme.Pic) :
    pairing X hregular p (cartierPicardHom X.toScheme (X.primeCurveCartier hregular C)) =
      X.picardRestrictionDegreeHom C p := by
  obtain ⟨D, hD⟩ := cartierPicardClass_surjective X.toScheme p.toMul
  have hp : cartierPicardHom X.toScheme D = p := congrArg Additive.ofMul hD
  rw [← hp]
  change X.picardPairing hregular (cartierPicardClass X.toScheme D)
      (cartierPicardClass X.toScheme (X.primeCurveCartier hregular C)) =
    X.picardRestrictionDegreeHom C (cartierPicardHom X.toScheme D)
  rw [X.picardPairing_class hregular, X.intersectionPairing_primeCurve hregular,
    C.picardRestrictionDegreeHom_cartierPicardHom]

theorem pairing_primeCurve_left (C : X.PrimeCurve) (p : Additive X.toScheme.Pic) :
    pairing X hregular (cartierPicardHom X.toScheme (X.primeCurveCartier hregular C)) p =
      X.picardRestrictionDegreeHom C p := by
  rw [pairing_symm, pairing_primeCurve_right]

/-- The same comparison with the inverse class of an actual curve ideal line. -/
theorem pairing_kernelLine_left (C : X.PrimeCurve) {Y : Scheme.{u}} (ι : Y ⟶ X.toScheme)
    [IsClosedImmersion ι] [AlgebraicGeometry.IsReduced Y]
    (hC : (C : Set X.toScheme) = Set.range ι.base) (L : InvertibleSheaf X.toScheme)
    (hL : L.obj = schemeKernelIdeal ι) (p : Additive X.toScheme.Pic) :
    pairing X hregular (-Additive.ofMul L.toPic) p = X.picardRestrictionDegreeHom C p := by
  rw [← cartierPicardHom_primeCurveCartier_of_kernel hregular C ι hC L hL,
    pairing_primeCurve_left]

omit [IsAlgClosed k] in
/-- The inverse kernel class has degree zero along a disjoint prime curve. -/
theorem restrictionDegreeHom_neg_kernel_zero (C : X.PrimeCurve) {Y : Scheme.{u}}
    (ι : Y ⟶ X.toScheme) [IsClosedImmersion ι] (L : InvertibleSheaf X.toScheme)
    (hL : L.obj = schemeKernelIdeal ι)
    (hdisj : Disjoint (Set.range C.inclusion.base) (Set.range ι.base)) :
    X.picardRestrictionDegreeHom C (-Additive.ofMul L.toPic) = 0 := by
  rw [map_neg, picardRestrictionDegreeHom_apply]
  change -(C.picardRestrictionDegree L.toPic) = 0
  rw [C.picardRestrictionDegree_toPic]
  have he : (pullbackInvertibleSheaf C.inclusion L).obj ≅
      _root_.SheafOfModules.unit C.toScheme.ringCatSheaf := by
    change (schemeModulePullback C.inclusion).obj L.obj ≅ _
    rw [hL]
    exact kernelLine_pullback_unitIso ι C.inclusion hdisj
  change -(C.lineDegree (pullbackInvertibleSheaf C.inclusion L)) = 0
  rw [C.lineDegree_eq_zero_of_iso_unit _ he, neg_zero]

end KltDP.Geometry.PrimeCurveClassPairing
