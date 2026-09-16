import KltDP.Geometry.InvertibleSectionNonvanishingCompact
import KltDP.Geometry.InvertibleSheafSectionPowersPullback
import KltDP.Geometry.PrimeCurvePullbackFrameCore

/-!
# Original coefficients on a single actual open chart

Only the original open immersion of a frame chart is used here. The
accepted generator comparison and semilinearity compute its literal pulled
section coefficient. Restricting a compatible framed section computes its
basic open before any equality of scheme opens is used.

This provides the specific open-chart calculation needed for finite twisted
extension, without constructing an atlas under a general scheme morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafOpenFrameCoefficient

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSheafSectionPowers RationalTreePicard

variable {X : Scheme.{u}}

/-- The literal single pullback has the original coefficient through the
original structural section map of the open immersion. -/
theorem pulled_frame_coefficient (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : M.val.obj (op U)) :
    (chartPullbackUnitIsoOf U M e.symm).hom.val.app (op (U.ι ⁻¹ᵁ U))
        (pulledSection U.ι M U s) =
      U.ι.app U (e.hom.val.app (op (Over.mk (𝟙 U))) s) := by
  let a : Γ(X, U) := e.hom.val.app (op (Over.mk (𝟙 U))) s
  let σ : M.val.obj (op U) := e.inv.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))
  let τ := chartPullbackUnitIsoOf U M e.symm
  have ha : a • σ = s := by
    calc
      a • σ = e.inv.val.app (op (Over.mk (𝟙 U))) (a • (1 : Γ(X, U))) :=
        ((e.inv.val.app (op (Over.mk (𝟙 U)))).hom.map_smul a (1 : Γ(X, U))).symm
      _ = e.inv.val.app (op (Over.mk (𝟙 U))) a := by rw [smul_eq_mul, mul_one]
      _ = s := overModuleIso_inv_app_hom_app e (op (Over.mk (𝟙 U))) s
  have hσ : τ.hom.val.app (op (U.ι ⁻¹ᵁ U)) (pulledSection U.ι M U σ) =
      (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U)) :=
    chartPullbackUnitIsoOf_hom_app_pullbackSection U M e.symm σ rfl
  have hlin : τ.hom.val.app (op (U.ι ⁻¹ᵁ U)) (pulledSection U.ι M U (a • σ)) =
      U.ι.app U a • τ.hom.val.app (op (U.ι ⁻¹ᵁ U)) (pulledSection U.ι M U σ) := by
    rw [pulledSection_smul]
    exact (τ.hom.val.app (op (U.ι ⁻¹ᵁ U))).hom.map_smul _ _
  calc
    _ = τ.hom.val.app (op (U.ι ⁻¹ᵁ U)) (pulledSection U.ι M U (a • σ)) :=
      congrArg (fun v => τ.hom.val.app (op (U.ι ⁻¹ᵁ U)) (pulledSection U.ι M U v)) ha.symm
    _ = U.ι.app U a • τ.hom.val.app (op (U.ι ⁻¹ᵁ U)) (pulledSection U.ι M U σ) := hlin
    _ = _ := by rw [hσ, smul_eq_mul, mul_one]

/-- Restricting an actual framed compatible section computes the original
coefficient basic open on any actual subopen. -/
theorem basicOpen_frame_restrict (L : InvertibleSheaf X)
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf)
    (s : L.obj.sections) (V : X.Opens) :
    X.basicOpen (e.hom.val.app (op V) (s.val (op V))) =
      V ⊓ X.basicOpen (frameCoefficient L e s) := by
  let j : op (⊤ : X.Opens) ⟶ op V := (homOfLE (show V ≤ ⊤ from le_top)).op
  have h : X.presheaf.map j (frameCoefficient L e s) =
      e.hom.val.app (op V) (s.val (op V)) :=
    (PresheafOfModules.naturality_apply e.hom.val j (s.val (op ⊤))).symm.trans
      (congrArg (e.hom.val.app (op V)) (s.property j))
  exact (congrArg (fun a : Γ(X, V) => X.basicOpen a) h).symm.trans
    (X.basicOpen_res (frameCoefficient L e s) j)

/-- Restricting an original atlas frame retains its original local coordinate. -/
theorem unitIsoOver_hom_apply (M : X.Modules)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)
    (i : t.I) {V : X.Opens} (hVi : V ≤ t.X i) (s : M.val.obj (op V)) :
    (t.unitIsoOver i (homOfLE hVi)).hom.val.app (op (Over.mk (𝟙 V))) s =
      (t.unitIso i).hom.val.app (op (Over.mk (homOfLE hVi))) s := rfl

end KltDP.Geometry.InvertibleSheafOpenFrameCoefficient
