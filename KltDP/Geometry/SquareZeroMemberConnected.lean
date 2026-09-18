import KltDP.Geometry.SquareZeroNegativeSections
import KltDP.Geometry.EffectiveCartierGeometricConnected
import KltDP.Geometry.CartierModuleIsoOfPicardClass
import KltDP.AdmissionProbe.ProperCohomologyConsumers

/-! Actual square-zero members are geometrically connected. Negative-line
H1 vanishing comes from the original nef divisor's RR computation. An
actual line isomorphism transports it to each original Cartier member.
No connectedness or cohomology conclusion is supplied by the caller. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
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
  (hrational : Scheme.BirationalOver X.structureMorphism
    (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))

local instance memberConnectedIntegral : IsIntegral X.toScheme := X.integral

include eK hrational in
/-- The actual negative line's H1 group is zero, using proper finiteness
with its original base-field action to interpret the proved dimension. -/
theorem squareZero_negative_hOne_subsingleton (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2) :
    Subsingleton (H (cartierDivisorModule X.toScheme (-F)) 1) := by
  let L := cartierDivisorInvertibleSheaf X.toScheme (-F)
  letI := baseModule X.structureMorphism L.obj 1
  letI : FiniteDimensional k (H L.obj 1) :=
    KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_invertible_field_finiteDimensional
      X.structureMorphism L 1
  have hz := (X.squareZero_negative_hZero_hOne_eq_zero hX K eK hrational F hF hFF hKF).2
  change Module.finrank k (H L.obj 1) = 0 at hz
  change Subsingleton (H L.obj 1)
  exact (Module.finrank_zero_iff (R := k) (M := H L.obj 1)).mp hz

include eK hrational in
/-- Every nonempty original Cartier member of the actual fiber line
is geometrically connected, including its possible nilpotents. -/
theorem squareZero_member_geometrically_connected (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (E : CartierDivisor X.toScheme) (hE : HasRegularCartierEquations X.toScheme E)
    (e : cartierDivisorModule X.toScheme E ≅ cartierDivisorModule X.toScheme F)
    [Nonempty (effectiveCartierScheme X.toScheme E hE)] :
    ∀ (l : Type u) [Field l] (q : Spec (CommRingCat.of l) ⟶ Spec (CommRingCat.of k)),
      ConnectedSpace (pullback
        (effectiveCartierInclusion X.toScheme E hE ≫ X.structureMorphism) q : Scheme.{u}) := by
  have hp : cartierPicardHom X.toScheme E = cartierPicardHom X.toScheme F :=
    congrArg Additive.ofMul (cartierPicardClass_eq_of_iso X.toScheme E F e)
  obtain ⟨en⟩ := cartierModuleIso_of_picardHom_eq X.toScheme (-E) (-F) (by
    rw [map_neg, map_neg, hp])
  letI : Subsingleton (H (cartierDivisorModule X.toScheme (-F)) 1) :=
    X.squareZero_negative_hOne_subsingleton hX K eK hrational F hF hFF hKF
  let he := baseLinearEquiv X.structureMorphism 1 en
  have hz : Subsingleton (H (cartierDivisorModule X.toScheme (-E)) 1) :=
    ⟨fun a b => he.injective (Subsingleton.elim _ _)⟩
  exact EffectiveCartierGeometricConnected.geometrically_connected X.structureMorphism E hE hz

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_member_geometrically_connected
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_member_geometrically_connected
