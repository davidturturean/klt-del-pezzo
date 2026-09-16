import KltDP.Geometry.SchemeKernelBaseChangeIsoLocus
import KltDP.Geometry.SchemePullbackOverOpenIso
import KltDP.Geometry.PrimeCurveOfClosedImmersion
import KltDP.Geometry.PrimeCurveInclusionLift
import KltDP.Geometry.PrimeCurveTransportPullback
import KltDP.Geometry.PrimeCurveClassPairing

/-!
# Pullback pairing along an actual projective line in an isomorphism open

The original fibre product of an embedded projective line contained in
an isomorphism open is again that projective line. Its embedded kernel
is the pullback of the original kernel by the accepted module-level
base-change theorem. The canonical prime-curve lifts give an actual
isomorphism commuting with both inclusions and field structures, so
the accepted degree transport computes its pairing with any pullback.
This is the specified isomorphism-open case, not a general cycle
projection formula.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.IsomorphismLocusPullbackPairing

open KltDP.Geometry.NormalProjectiveSurface
  KltDP.Geometry.PrimeCurveOfClosedImmersion KltDP.Geometry.PrimeCurveInclusionLift
  KltDP.Geometry.PrimeCurveClassPairing KltDP.Geometry.PrimeCurveTransportPullback
  KltDP.Geometry.SchemeKernelBaseChangeIsoLocus

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X Y : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (hY : ∀ x : Y.Point, RegularPoint Y.toScheme x)
  (π : X.toScheme ⟶ Y.toScheme)
  (hπ : π ≫ Y.structureMorphism = X.structureMorphism)

include hπ

set_option maxHeartbeats 800000 in
/-- The original kernel pairing pulls back unchanged when its actual projective line lies in an
open where the original morphism is an isomorphism. -/
theorem pairing_pullback_projectiveLine_kernel
    (g : projectiveSpace k 1 ⟶ Y.toScheme) [IsClosedImmersion g]
    (U : Y.toScheme.Opens) [IsIso (π ∣_ U)]
    (hgU : Set.range g.base ⊆ (U : Set Y.toScheme))
    (hg : KltDP.SheafOfModules.IsInvertible (R := Y.toScheme.ringCatSheaf)
      (schemeKernelIdeal g)) (p : Additive Y.toScheme.Pic) :
    pairing X hX
      ((schemePicardPullbackHom π).toAdditive
        (-Additive.ofMul (InvertibleSheaf.toPic (⟨schemeKernelIdeal g, hg⟩ : InvertibleSheaf Y.toScheme))))
      ((schemePicardPullbackHom π).toAdditive p) =
    pairing Y hY
      (-Additive.ofMul (InvertibleSheaf.toPic (⟨schemeKernelIdeal g, hg⟩ : InvertibleSheaf Y.toScheme))) p := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : IsClosedImmersion (pullback.fst π g) :=
    MorphismProperty.pullback_fst (P := @IsClosedImmersion) π g inferInstance
  letI : IsIso (pullback.snd π g) :=
    isIso_pullback_snd_of_range_subset π g U (by simpa only [Scheme.Opens.range_ι] using hgU)
  letI : IsIntegral (pullback π g) :=
    isIntegral_of_iso_projectiveLine (asIso (pullback.snd π g))
  let C : Y.PrimeCurve := primeCurveOfIsoProjectiveLine Y g (Iso.refl _)
  let C' : X.PrimeCurve :=
    primeCurveOfIsoProjectiveLine X (pullback.fst π g) (asIso (pullback.snd π g))
  have hC : (C : Set Y.toScheme) = Set.range g.base :=
    coe_primeCurveOfIsoProjectiveLine Y g (Iso.refl _)
  have hC' : (C' : Set X.toScheme) = Set.range (pullback.fst π g).base :=
    coe_primeCurveOfIsoProjectiveLine X (pullback.fst π g) (asIso (pullback.snd π g))
  let f : projectiveSpace k 1 ⟶ C.toScheme := lift C g hC
  let f' : pullback π g ⟶ C'.toScheme := lift C' (pullback.fst π g) hC'
  let φ : C'.toScheme ⟶ C.toScheme := inv f' ≫ pullback.snd π g ≫ f
  haveI : IsIso φ := by dsimp [φ, f', f]; infer_instance
  have hfac : C'.inclusion ≫ π = φ ≫ C.inclusion := by
    have hf : f ≫ C.inclusion = g := lift_inclusion C g hC
    have hf' : C'.inclusion = inv f' ≫ pullback.fst π g :=
      inclusion_eq_inv_lift C' (pullback.fst π g) hC'
    calc
      C'.inclusion ≫ π = inv f' ≫ (pullback.fst π g ≫ π) := by
        rw [hf', Category.assoc]
      _ = inv f' ≫ (pullback.snd π g ≫ g) := by rw [pullback.condition]
      _ = φ ≫ C.inclusion := by simp only [φ, Category.assoc, hf]
  have hφ : φ ≫ C.toSpec = C'.toSpec := by
    change φ ≫ (C.inclusion ≫ Y.structureMorphism) = C'.inclusion ≫ X.structureMorphism
    rw [← Category.assoc, ← hfac, Category.assoc, hπ]
  have hdegree := picardRestrictionDegree_eq_of_isoFactor C' C π φ hfac hφ p.toMul
  have hleft := pairing_kernelLine_left X hX C' (pullback.fst π g) hC'
    (baseChangeKernelLine π g U hgU hg) rfl
    ((schemePicardPullbackHom π).toAdditive p)
  have hright := pairing_kernelLine_left Y hY C g hC
    (⟨schemeKernelIdeal g, hg⟩ : InvertibleSheaf Y.toScheme) rfl p
  rw [neg_baseChangeKernelLine_toPic π g U hgU hg] at hleft
  exact hleft.trans (hdegree.trans hright.symm)

end KltDP.Geometry.IsomorphismLocusPullbackPairing
