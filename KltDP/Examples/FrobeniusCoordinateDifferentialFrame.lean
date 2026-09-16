import KltDP.Examples.FrobeniusBlowupDifferential
import KltDP.Geometry.AffineTopDifferentialFrame
import KltDP.Compatibility.PolynomialStandardSmooth

/-!
# The original coordinate two-form is an actual differential frame

The polynomial chart is standard smooth of relative dimension two. The
existing top-differential theorem therefore gives an equivalence of its
actual exterior square with the coefficient ring. The original determinant
functional takes `du ∧ dv` to one; commutativity then shows that this specific
functional is an equivalence with inverse `a ↦ a • (du ∧ dv)`.

The induced tilde isomorphism uses that same functional. On every open,
the original coordinate form maps to the structure section one, while the
form obtained by differentiating the actual blowdown coordinates maps
fiberwise to the original exceptional coordinate `u`.

No global differential sheaf, canonical divisor, or numerical intersection
is asserted. The proof applies the existing pinned linear, smoothness, and
tilde APIs; no additional source proof port or literature axiom is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace KltDP.Examples.FrobeniusCoordinateDifferentialFrame

open FrobeniusBlowupContact FrobeniusBlowupDifferential
open KltDP.Geometry

universe u v

section LinearFrame

variable {A : Type u} [CommRing A] {L : Type v} [AddCommGroup L] [Module A L]

/-- In a module already equivalent to the ring, an actual functional
taking an actual vector to one gives coordinates with that vector as frame. -/
private def normalizedFrameEquiv (e : L ≃ₗ[A] A) (F : L →ₗ[A] A)
    (w : L) (h : F w = 1) : L ≃ₗ[A] A := by
  let G : A →ₗ[A] L := LinearMap.toSpanSingleton A L w
  have hswap (x y : L) : e x • y = e y • x := by
    apply e.injective
    simp only [map_smul, smul_eq_mul]
    exact mul_comm _ _
  refine LinearEquiv.ofLinear F G ?_ ?_
  · apply LinearMap.ext
    intro r
    change F (r • w) = r
    rw [map_smul, h, smul_eq_mul, mul_one]
  · apply LinearMap.ext
    intro x
    change F x • w = x
    apply e.injective
    rw [map_smul, smul_eq_mul]
    calc
      F x * e w = e w * F x := mul_comm _ _
      _ = e x := by
        have hx := congrArg F (hswap w x)
        simpa only [map_smul, h, smul_eq_mul, mul_one] using hx

end LinearFrame

variable {k : Type u} [Field k]

/-- The original iterated polynomial algebra has relative dimension two,
by composing its two actual one-variable standard-smooth presentations. -/
theorem plane_standardSmooth :
    Algebra.IsStandardSmoothOfRelativeDimension 2 k (planeRing k) := by
  letI := KltDP.Compatibility.PolynomialStandardSmooth.polynomial_standardSmooth k
  letI := KltDP.Compatibility.PolynomialStandardSmooth.polynomial_standardSmooth (Polynomial k)
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans
    (n := 1) (m := 1) k (Polynomial k) (planeRing k)

/-- The actual determinant evaluator gives coordinates on the original
top differential module, with inverse the original coordinate wedge. -/
def coordinateTopDifferentialEquiv :
    (⋀[planeRing k]^2 (PlaneDifferential k)) ≃ₗ[planeRing k] planeRing k := by
  letI := plane_standardSmooth (k := k)
  exact normalizedFrameEquiv
    (AffineTopDifferentialFrame.standardSmoothTopDifferentialEquiv k (planeRing k))
    coordinateTopFormEvaluator coordinateTopForm coordinateTopFormEvaluator_coordinateTopForm

theorem coordinateTopDifferentialEquiv_apply
    (ω : ⋀[planeRing k]^2 (PlaneDifferential k)) :
    coordinateTopDifferentialEquiv ω = coordinateTopFormEvaluator ω := rfl

theorem coordinateTopDifferentialEquiv_symm_apply (a : planeRing k) :
    (coordinateTopDifferentialEquiv (k := k)).symm a = a • coordinateTopForm := rfl

/-- Every original exterior two-form has its actual determinant coordinate. -/
theorem coordinateTopForm_expansion (ω : ⋀[planeRing k]^2 (PlaneDifferential k)) :
    coordinateTopFormEvaluator ω • coordinateTopForm = ω :=
  (coordinateTopDifferentialEquiv (k := k)).symm_apply_apply ω

theorem coordinateTopForm_spans :
    Submodule.span (planeRing k) {coordinateTopForm (k := k)} = ⊤ := by
  apply top_unique
  intro ω _
  exact Submodule.mem_span_singleton.mpr
    ⟨coordinateTopFormEvaluator ω, coordinateTopForm_expansion ω⟩

/-- The frame is an isomorphism of the actual tilde module sheaf with the
original structure-sheaf unit, induced by the original determinant map. -/
def coordinateTopDifferentialSheafIso :
    (ModuleCat.of (planeRing k) (⋀[planeRing k]^2 (PlaneDifferential k))).tilde ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of (planeRing k))).ringCatSheaf :=
  AffineModuleTilde.linearEquivIso
    (M := ModuleCat.of (planeRing k) (⋀[planeRing k]^2 (PlaneDifferential k)))
    (N := ModuleCat.of (planeRing k) (planeRing k))
    coordinateTopDifferentialEquiv ≪≫ AffineModuleTilde.unitIso (planeRing k)

/-- Canonical sections retain their original determinant coordinate under
the actual tilde map, before the original module/ring localization comparison. -/
theorem coordinateTopDifferentialSheafIso_hom_toOpen
    (U : Opens (PrimeSpectrum (planeRing k)))
    (ω : ⋀[planeRing k]^2 (PlaneDifferential k)) :
    (coordinateTopDifferentialSheafIso (k := k)).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen
          (ModuleCat.of (planeRing k) (⋀[planeRing k]^2 (PlaneDifferential k))) U ω) =
      (AffineModuleTilde.unitIso (planeRing k)).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen (ModuleCat.of (planeRing k) (planeRing k)) U
          (coordinateTopFormEvaluator ω)) := by
  change (AffineModuleTilde.unitIso (planeRing k)).hom.val.app (op U)
      ((AffineModuleTilde.map
        (coordinateTopDifferentialEquiv (k := k)).toModuleIso.hom).val.app (op U)
        (ModuleCat.Tilde.toOpen
          (ModuleCat.of (planeRing k) (⋀[planeRing k]^2 (PlaneDifferential k))) U ω)) = _
  exact congrArg ((AffineModuleTilde.unitIso (planeRing k)).hom.val.app (op U))
    (AffineModuleTilde.map_app_toOpen
      (coordinateTopDifferentialEquiv (k := k)).toModuleIso.hom U ω)

/-- The frame coordinate on an actual stalk fiber is the image of the
original polynomial coefficient in that prime localization. -/
theorem coordinateTopDifferentialSheafIso_hom_toOpen_val
    (U : Opens (PrimeSpectrum (planeRing k)))
    (ω : ⋀[planeRing k]^2 (PlaneDifferential k)) (p : U) :
    ((coordinateTopDifferentialSheafIso (k := k)).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen
          (ModuleCat.of (planeRing k) (⋀[planeRing k]^2 (PlaneDifferential k))) U ω)).val p =
      algebraMap (planeRing k) (Localization.AtPrime p.val.asIdeal)
        (coordinateTopFormEvaluator ω) := by
  rw [coordinateTopDifferentialSheafIso_hom_toOpen,
    AffineModuleTilde.unitIso_hom_app_val]
  exact AffineModuleTilde.unitFiberEquiv_mkLinearMap
    (planeRing k) p.val (coordinateTopFormEvaluator ω)

/-- The original coordinate wedge is the actual unit section in this frame. -/
theorem coordinateTopDifferentialSheafIso_hom_coordinateTopForm
    (U : Opens (PrimeSpectrum (planeRing k))) :
    (coordinateTopDifferentialSheafIso (k := k)).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen
          (ModuleCat.of (planeRing k) (⋀[planeRing k]^2 (PlaneDifferential k))) U
          coordinateTopForm) = (1 : Γ(Spec (CommRingCat.of (planeRing k)), U)) := by
  apply Subtype.ext
  funext p
  simpa only [coordinateTopFormEvaluator_coordinateTopForm, map_one] using
    coordinateTopDifferentialSheafIso_hom_toOpen_val U coordinateTopForm p

/-- The actual blowdown-coordinate form has the original exceptional
coordinate on every prime-localization fiber, in the proved coordinate frame. -/
theorem coordinateTopDifferentialSheafIso_hom_pulledCoordinateTopForm_val
    (U : Opens (PrimeSpectrum (planeRing k))) (p : U) :
    ((coordinateTopDifferentialSheafIso (k := k)).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen
          (ModuleCat.of (planeRing k) (⋀[planeRing k]^2 (PlaneDifferential k))) U
          pulledCoordinateTopForm)).val p =
      algebraMap (planeRing k) (Localization.AtPrime p.val.asIdeal) uCoord := by
  simpa only [coordinateTopFormEvaluator_pulledCoordinateTopForm] using
    coordinateTopDifferentialSheafIso_hom_toOpen_val U pulledCoordinateTopForm p

end KltDP.Examples.FrobeniusCoordinateDifferentialFrame
