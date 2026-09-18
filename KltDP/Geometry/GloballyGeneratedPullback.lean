import KltDP.Compatibility.SheafGeneratingSectionsMap
import KltDP.Geometry.SchemeModuleFunctorial
import KltDP.Geometry.SchemeModulePullbackUnit
import KltDP.Geometry.Positivity

/-! # Original global generation is preserved by actual scheme pullback -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.GloballyGeneratedPullback

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The actual adjoint pullback transports an original generating family,
retaining the original index through the accepted free-sheaf comparison. -/
def generatingSections (M : X.Modules) (G : M.GeneratingSections) :
    ((schemeModulePullback f).obj M).GeneratingSections := by
  letI : (schemeModulePullback f).IsLeftAdjoint :=
    (schemeModulePullbackPushforwardAdjunction f).isLeftAdjoint
  exact G.map (schemeModulePullback f) (schemeModulePullbackUnitIso f).symm

theorem generatingSections_I (M : X.Modules) (G : M.GeneratingSections) :
    (generatingSections f M G).I = G.I := rfl

/-- Finite original generators remain finite after the actual pullback. -/
theorem generatingSections_finite (M : X.Modules) (G : M.GeneratingSections) [Finite G.I] :
    Finite (generatingSections f M G).I :=
  inferInstanceAs (Finite G.I)

/-- Global generation pulls back along any actual morphism of schemes. -/
theorem isGloballyGenerated (M : X.Modules) (hM : Positivity.IsGloballyGenerated M) :
    Positivity.IsGloballyGenerated ((schemeModulePullback f).obj M) := by
  letI : (schemeModulePullback f).IsLeftAdjoint :=
    (schemeModulePullbackPushforwardAdjunction f).isLeftAdjoint
  obtain ⟨I, φ, hφ⟩ := hM
  letI : Epi φ := hφ
  exact ⟨I, (_root_.SheafOfModules.mapFreeIso (schemeModulePullback f) I
    (schemeModulePullbackUnitIso f).symm).hom ≫ (schemeModulePullback f).map φ,
    inferInstance⟩

end KltDP.Geometry.GloballyGeneratedPullback
