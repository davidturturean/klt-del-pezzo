import KltDP.Geometry.InvertibleSectionNonvanishingFrame
import KltDP.Geometry.InvertibleSectionNonvanishingPullback
import KltDP.Geometry.InvertibleSheafSectionPowersPullback

/-!
# Positive powers preserve original intrinsic nonvanishing opens

The actual power/pullback comparison identifies the coefficient of a
pulled power section with the ordinary power of the original pulled
coefficient. Original local frames then prove the intrinsic equality on
the original scheme. No affine or quasi-compact hypothesis is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Geometry.InvertibleSectionNonvanishingPowers

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance nonvanishingPowerMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open InvertibleSheafSectionPowers InvertibleSheafSectionPowersPullback
open InvertibleSectionNonvanishingOpen

variable {X Y : Scheme.{u}}

private theorem coefficient_pullback_power (f : Y ⟶ X) (L : InvertibleSheaf X)
    (e : (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf)
    (s : L.obj.sections) (n : ℕ) :
    frameCoefficient (pullbackInvertibleSheaf f (power L n))
        (powerPullbackIso f L n ≪≫ powerFrame (pullbackInvertibleSheaf f L) e n)
        (InvertibleSheafSectionPowersPullback.pullbackSection f (power L n).obj
          (powerSection L s n)) =
      frameCoefficient (pullbackInvertibleSheaf f L) e
        (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) ^ n := by
  have hp := powerSection_pullback_val f L s n (⊤ : X.Opens)
  have hs := pullbackSection_val f (power L n).obj (powerSection L s n) (⊤ : X.Opens)
  have h := (congrArg ((powerPullbackIso f L n).hom.val.app (op (f ⁻¹ᵁ ⊤))) hs).trans hp
  have hc := congrArg ((powerFrame (pullbackInvertibleSheaf f L) e n).hom.val.app
    (op (f ⁻¹ᵁ (⊤ : X.Opens)))) h
  change frameCoefficient (pullbackInvertibleSheaf f (power L n))
      (powerPullbackIso f L n ≪≫ powerFrame (pullbackInvertibleSheaf f L) e n)
      (InvertibleSheafSectionPowersPullback.pullbackSection f (power L n).obj
        (powerSection L s n)) =
    frameCoefficient (power (pullbackInvertibleSheaf f L) n)
      (powerFrame (pullbackInvertibleSheaf f L) e n)
      (powerSection (pullbackInvertibleSheaf f L)
        (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) n) at hc
  exact hc.trans (powerSection_frame_coefficient_top (pullbackInvertibleSheaf f L) e
    (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) n)

/-- On any actual pullback admitting a frame, positive powers have the
same original inverse-image nonvanishing open. -/
theorem preimage_nonvanishingOpen_power (f : Y ⟶ X) (L : InvertibleSheaf X)
    (e : (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf)
    (s : L.obj.sections) {n : ℕ} (hn : 0 < n) :
    f ⁻¹ᵁ nonvanishingOpen X (power L n) (powerSection L s n) =
      f ⁻¹ᵁ nonvanishingOpen X L s := by
  calc
    _ = nonvanishingOpen Y (pullbackInvertibleSheaf f (power L n))
        (InvertibleSheafSectionPowersPullback.pullbackSection f (power L n).obj
          (powerSection L s n)) :=
      (InvertibleSectionNonvanishingPullback.nonvanishingOpen_pullback
        f (power L n) (powerSection L s n)).symm
    _ = Y.basicOpen (frameCoefficient (pullbackInvertibleSheaf f (power L n))
        (powerPullbackIso f L n ≪≫ powerFrame (pullbackInvertibleSheaf f L) e n)
        (InvertibleSheafSectionPowersPullback.pullbackSection f (power L n).obj
          (powerSection L s n))) :=
      InvertibleSectionNonvanishingFrame.nonvanishingOpen_eq_basicOpen _ _ _
    _ = Y.basicOpen (frameCoefficient (pullbackInvertibleSheaf f L) e
        (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) ^ n) :=
      congrArg (fun a : Γ(Y, ⊤) => Y.basicOpen a) (coefficient_pullback_power f L e s n)
    _ = Y.basicOpen (frameCoefficient (pullbackInvertibleSheaf f L) e
        (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s)) :=
      Y.basicOpen_pow _ hn
    _ = nonvanishingOpen Y (pullbackInvertibleSheaf f L)
        (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) :=
      (InvertibleSectionNonvanishingFrame.nonvanishingOpen_eq_basicOpen _ _ _).symm
    _ = _ := InvertibleSectionNonvanishingPullback.nonvanishingOpen_pullback f L s

/-- The actual positive tensor-power section has exactly the original
section's intrinsic nonvanishing open on the original scheme. -/
theorem nonvanishingOpen_power (L : InvertibleSheaf X) (s : L.obj.sections)
    {n : ℕ} (hn : 0 < n) :
    nonvanishingOpen X (power L n) (powerSection L s n) = nonvanishingOpen X L s := by
  ext x
  let t := L.localTrivializations
  obtain ⟨W, g, ⟨i, ⟨j⟩⟩, hxW⟩ := t.coversTop (⊤ : X.Opens) x trivial
  let U : X.Opens := t.X i
  let hx : x ∈ U := j.le hxW
  let y : U.toScheme := ⟨x, hx⟩
  let e := chartPullbackUnitIsoOf U L.obj (t.unitIso i).symm
  change (y ∈ U.ι ⁻¹ᵁ nonvanishingOpen X (power L n) (powerSection L s n)) ↔
    (y ∈ U.ι ⁻¹ᵁ nonvanishingOpen X L s)
  rw [preimage_nonvanishingOpen_power U.ι L e s hn]

end KltDP.Geometry.InvertibleSectionNonvanishingPowers
