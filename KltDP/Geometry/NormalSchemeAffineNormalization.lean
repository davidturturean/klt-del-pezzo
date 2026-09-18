import KltDP.Geometry.NormalOpenSections
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Identity normalization on the original normal scheme's affine opens

The ambient field is the original generic stalk.  Every chart below is
the spectrum of the actual integral-closure subalgebra, and its projection
is induced by the original generic-germ scalar map.  Normality proves
that projection invertible; no normalization or resolution is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalSchemeAffineNormalization

variable (X : Scheme.{u}) [IsIntegral X]

/-- The original section ring is its integral closure inside the original
function field.  Bottom is the image of its original scalar map. -/
theorem integralClosure_eq_bot (hnormal : IsNormalScheme X)
    (U : X.Opens) [Nonempty U] :
    integralClosure Γ(X, U) X.functionField = ⊥ :=
  (IsIntegrallyClosedIn.integralClosure_eq_bot_iff X.functionField
    (X.germToFunctionField_injective U)).mpr
      (isIntegrallyClosedIn_openSections_of_isNormal X hnormal U)

/-- The actual scalar map onto the integral closure is bijective. -/
theorem scalar_bijective (hnormal : IsNormalScheme X)
    (U : X.Opens) [Nonempty U] :
    Function.Bijective
      (algebraMap Γ(X, U) (integralClosure Γ(X, U) X.functionField)) := by
  letI : IsIntegrallyClosedIn Γ(X, U) X.functionField :=
    isIntegrallyClosedIn_openSections_of_isNormal X hnormal U
  constructor
  · intro a b hab
    apply X.germToFunctionField_injective U
    exact congrArg
      (fun q : integralClosure Γ(X, U) X.functionField => (q : X.functionField)) hab
  · intro q
    obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral q.2
    exact ⟨a, Subtype.ext ha⟩

/-- This isomorphism has the literal original scalar map as its forward map. -/
def sectionsEquiv (hnormal : IsNormalScheme X) (U : X.Opens) [Nonempty U] :
    Γ(X, U) ≃ₐ[Γ(X, U)] integralClosure Γ(X, U) X.functionField :=
  AlgEquiv.ofBijective (Algebra.ofId Γ(X, U)
    (integralClosure Γ(X, U) X.functionField)) (scalar_bijective X hnormal U)

/-- The actual integral-closure spectrum in the original function field. -/
def chart (U : X.Opens) [Nonempty U] : Scheme.{u} :=
  Spec (CommRingCat.of (integralClosure Γ(X, U) X.functionField))

/-- Its actual projection to the original affine section spectrum. -/
def projection (U : X.Opens) [Nonempty U] : chart X U ⟶ Spec Γ(X, U) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap Γ(X, U) (integralClosure Γ(X, U) X.functionField)))

/-- Normality makes that same projection an isomorphism. -/
def chartIso (hnormal : IsNormalScheme X) (U : X.Opens) [Nonempty U] :
    chart X U ≅ Spec Γ(X, U) :=
  Scheme.Spec.mapIso (sectionsEquiv X hnormal U).toRingEquiv.toCommRingCatIso.op

@[simp] theorem chartIso_hom (hnormal : IsNormalScheme X)
    (U : X.Opens) [Nonempty U] :
    (chartIso X hnormal U).hom = projection X U := rfl

@[reassoc (attr := simp)] theorem chartIso_inv_projection
    (hnormal : IsNormalScheme X) (U : X.Opens) [Nonempty U] :
    (chartIso X hnormal U).inv ≫ projection X U = 𝟙 _ :=
  (chartIso X hnormal U).inv_hom_id

theorem projection_isIso (hnormal : IsNormalScheme X)
    (U : X.Opens) [Nonempty U] : IsIso (projection X U) := by
  rw [← chartIso_hom X hnormal U]
  infer_instance

/-- The original affine open itself is the actual normalization chart. -/
def originalOpenIso (hnormal : IsNormalScheme X)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    U.toScheme ≅ chart X U :=
  hU.isoSpec ≪≫ (chartIso X hnormal U).symm

/-- The chart comparison retains the original inclusion followed by the
identity of the original scheme. -/
@[reassoc] theorem originalOpenIso_projection
    (hnormal : IsNormalScheme X)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (originalOpenIso X hnormal U hU).hom ≫ projection X U ≫ hU.fromSpec =
      U.ι ≫ 𝟙 X := by
  change (hU.isoSpec.hom ≫ (chartIso X hnormal U).inv) ≫
    projection X U ≫ hU.fromSpec = U.ι ≫ 𝟙 X
  rw [Category.assoc, chartIso_inv_projection_assoc,
    IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec, Category.comp_id]

end KltDP.Geometry.NormalSchemeAffineNormalization

#print axioms KltDP.Geometry.NormalSchemeAffineNormalization.scalar_bijective
#print axioms KltDP.Geometry.NormalSchemeAffineNormalization.originalOpenIso_projection
