import KltDP.Examples.FrobeniusMultiCentrePicardPushforwardSurjective
import KltDP.Examples.FrobeniusMultiCentreOldExceptionalWeilClasses
import KltDP.Examples.FrobeniusMultiCentreContractingWeilPullback
import KltDP.Geometry.CartierPicardEndpointRationalClasses

/-!
# Actual rational Picard pushforward and its original contracted classes

The map is the original source Picard-to-Weil class map, original proper
birational pushforward, and original target rationalization. The graph,
strict fibres and old exceptional kernels vanish by their actual prime
representatives and original all-prime criterion. The power comparison
uses the original pullback-line isomorphism and retains its exponent m.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreRationalPicardPushforward

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface PrimeCurveTransversalPoint
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral FrobeniusProjectivityProved
open FrobeniusMultiCentreCanonicalWeilRepresentatives FrobeniusMultiCentrePicardPushforwardSurjective
open FrobeniusMultiCentreContractedWeilClasses FrobeniusMultiCentreOldExceptionalWeilClasses
open FrobeniusMultiCentreContractingClass FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreGraphCartierStrict FrobeniusMultiCentreFiberGlobalClass
open FrobeniusMultiCentreSpecialNullCurves FrobeniusMultiCentreGraphExceptionalPairing
open FrobeniusMultiCentreExceptional FrobeniusMultiCentreExceptionalPrime
open FrobeniusMultiCentreExceptionalGlobalClasses FrobeniusMultiCentreContractingWeilPullback
open FrobeniusMultiCentreSemiampleConstruction InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)

local instance original_integral : IsIntegral (multiSurface (q + 1) n a) :=
  multiSurface_isIntegral (q + 1) n a ha

variable {Y : NormalProjectiveSurface k}
    (π : (sourceSurface q n a ha
      (originalMultiStructureProjective k (q + 1) n a)).toScheme ⟶ Y.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- The original class maps composed with the original target rationalization. -/
def rationalPicardPushforward : Additive (multiSurface (q + 1) n a).Pic →+
    Y.RationalWeilClassGroup :=
  Y.weilClassRationalization.comp
    (sourcePicardPushforward q n a ha (originalMultiStructureProjective k (q + 1) n a) π hbir)

variable (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    (hcriterion : ∀ C : (sourceSurface q n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine q n a ha) = 0)

include hπ hcriterion in
/-- The original strict graph class has zero image under the actual rational map. -/
theorem graph_image_eq_zero :
    rationalPicardPushforward q n a ha π hbir
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = 0 := by
  have hrep := congrArg (BirationalWeilClassPushforward.pushforward
    (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
    (X := Y) π hbir)
    (graph_picardToWeil q n a ha (originalMultiStructureProjective k (q + 1) n a))
  have hz := graph_class_pushforward_eq_zero q n a ha
    (originalMultiStructureProjective k (q + 1) n a) π hπ hbir hcriterion (1 : ℤ)
  exact (congrArg Y.weilClassRationalization (hrep.trans hz)).trans
    Y.weilClassRationalization.map_zero

include hπ hcriterion in
/-- Each original strict fibre class has zero actual rational image. -/
theorem fiber_image_eq_zero (i : Fin n) :
    rationalPicardPushforward q n a ha π hbir
      (-Additive.ofMul (fiberKernelLine q n a ha i).toPic) = 0 := by
  have hrep := congrArg (BirationalWeilClassPushforward.pushforward
    (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
    (X := Y) π hbir)
    (fiber_picardToWeil q n a ha (originalMultiStructureProjective k (q + 1) n a) i)
  have hz := fiber_class_pushforward_eq_zero q n a ha
    (originalMultiStructureProjective k (q + 1) n a) π hπ hbir hcriterion i (1 : ℤ)
  exact (congrArg Y.weilClassRationalization (hrep.trans hz)).trans
    Y.weilClassRationalization.map_zero

include hπ hcriterion in
/-- Each actual old exceptional kernel class has zero actual rational image. -/
theorem old_exceptional_image_eq_zero (i : Fin n) (j : Fin q) :
    rationalPicardPushforward q n a ha π hbir
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inl j)).toPic) = 0 := by
  letI := exceptionalCurve_isIntegral q n a ha i (.inl j)
  have hC := cartierPicardHom_primeCurveCartier_of_kernel
    (multiSurfaceSurface_regularPoints (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a))
    (exceptionalPrimeCurveSPn q n a ha i (.inl j)
      (originalMultiStructureProjective k (q + 1) n a))
    (exceptionalCurveι q n a i (.inl j))
    (coe_exceptionalPrimeCurveSPn q n a ha i (.inl j)
      (originalMultiStructureProjective k (q + 1) n a))
    (exceptionalKernelLine q n a ha i (.inl j)) rfl
  have hrep := (sourceSurface q n a ha
    (originalMultiStructureProjective k (q + 1) n a)).picardToWeilClassHom_cartierPicardHom
    ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).primeCurveCartier
      (multiSurfaceSurface_regularPoints (q + 1) n a ha
        (originalMultiStructureProjective k (q + 1) n a))
      (exceptionalPrimeCurveSPn q n a ha i (.inl j)
        (originalMultiStructureProjective k (q + 1) n a)))
  rw [hC, (sourceSurface q n a ha
    (originalMultiStructureProjective k (q + 1) n a)).cartierToWeilHom_primeCurveCartier] at hrep
  have hpush := congrArg (BirationalWeilClassPushforward.pushforward
    (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
    (X := Y) π hbir) hrep
  have hz := original_old_exceptional_class_pushforward_eq_zero q n a ha π hπ hbir
    hcriterion i j (1 : ℤ)
  exact (congrArg Y.weilClassRationalization (hpush.trans hz)).trans
    Y.weilClassRationalization.map_zero

variable [Surjective π] [IsIso π.c]

include hπ hcriterion in
/-- The original ample-line witness retains m in the actual rational class identity. -/
theorem power_image_eq (hn : 2 < n)
    (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
    (A : InvertibleSheaf Y.toScheme) (m : ℕ)
    (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj) :
    (m : ℤ) • rationalPicardPushforward q n a ha π hbir (contractingClass q n a ha) =
      Y.weilClassRationalization (Y.picardToWeilClassHom (Additive.ofMul A.toPic)) := by
  have hpower := contractingWeil_pullback_power q n a ha hn Y π hπ hbir hconnected hcriterion A m e
  have hrep := congrArg (BirationalWeilClassPushforward.pushforward
    (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
    (X := Y) π hbir)
    (contracting_picardToWeil q n a ha (originalMultiStructureProjective k (q + 1) n a))
  have h := congrArg Y.weilClassRationalization
    ((congrArg (fun c : Y.WeilClassGroup => (m : ℤ) • c) hrep).trans hpower)
  exact (Y.weilClassRationalization.map_zsmul _ (m : ℤ)).symm.trans h

end KltDP.Examples.FrobeniusMultiCentreRationalPicardPushforward
