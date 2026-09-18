import KltDP.Literature.Stacks.ProperCohomologyFinite
import KltDP.Geometry.InvertibleCoherentModule
import KltDP.Geometry.FiniteTypeNoetherian
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite original affine-base global sections of a proper scheme

The accepted Stacks 02O6 theorem gives finite original derived H0 of a
coherent module over the original Noetherian base ring. The existing
base-ring-linear derived/Ext and H0/sections comparisons retain the exact
scalar map. Properness makes the source locally Noetherian, so its actual
unit module is coherent. Its top sections are the original global ring.

The resulting finite ring map defines the original affine factor of
`X.toSpecΓ`. The triangle is the pinned Gamma-Spec adjunction identity.
The short Spec-map finiteness calculation reuses the existing private
producer in `AffineQuadraticCover`; no quadratic construction is imported.
No field, integrality, reducedness, or geometric-fibre assumption is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProperAffineSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open ModuleCohomology

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))

/-- The exact scalar map from the original affine base to original global functions. -/
def baseScalar : R →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/-- Actual coherent top sections are finite for the original base-ring action. -/
theorem coherent_sections_finite [IsNoetherianRing R] [IsProper f]
    (M : X.Modules) [IsCoherentModule M] :
    letI := baseRingSectionsModule f M
    Module.Finite R (sections M) := by
  letI := baseRingModule f M 0
  letI := baseRingRightDerivedModule f M 0
  letI := baseRingSectionsModule f M
  letI : Module.Finite R (rightDerivedH M 0) :=
    KltDP.Literature.Stacks.properCohomology_finite f M 0
  exact Module.Finite.equiv
    ((zariskiRightDerivedLinearEquiv f M 0).symm.trans
      (hZeroBaseRingLinearEquivSections f M))

/-- The original global-function ring is finite over the original Noetherian base ring. -/
theorem globalSections_moduleFinite [IsNoetherianRing R] [IsProper f] :
    letI := (baseScalar f).toAlgebra
    Module.Finite R Γ(X, ⊤) := by
  letI := (baseScalar f).toAlgebra
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_locallyOfFiniteType_toSpec f
  let M : X.Modules := _root_.SheafOfModules.unit X.ringCatSheaf
  letI : IsCoherentModule M := inferInstance
  exact coherent_sections_finite f M

/-- The same finiteness as a property of the exact original scalar ring homomorphism. -/
theorem baseScalar_finite [IsNoetherianRing R] [IsProper f] :
    (baseScalar f).Finite :=
  globalSections_moduleFinite f

/-- The original affine factor over the original spectrum of the base ring. -/
def toSpecBase : Spec Γ(X, ⊤) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (baseScalar f))

/-- The actual affinization map and its actual scalar factor recover the original morphism. -/
@[reassoc] theorem toSpecΓ_toSpecBase : X.toSpecΓ ≫ toSpecBase f = f := by
  change X.toSpecΓ ≫
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) = f
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.comp_id]

private theorem specMap_isFinite {A B : CommRingCat.{u}} (g : A ⟶ B)
    (hg : g.hom.Finite) : AlgebraicGeometry.IsFinite (Spec.map g) := by
  apply (HasAffineProperty.iff_of_isAffine (P := @AlgebraicGeometry.IsFinite)).mpr
  refine ⟨inferInstance, ?_⟩
  have H := RingHom.finite_respectsIso
  rw [← H.cancel_right_isIso _ (Scheme.ΓSpecIso _).hom,
    ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp,
    H.cancel_left_isIso]
  exact hg

/-- The actual affine factor of a proper scheme over a Noetherian ring is finite. -/
theorem toSpecBase_isFinite [IsNoetherianRing R] [IsProper f] : IsFinite (toSpecBase f) :=
  specMap_isFinite (CommRingCat.ofHom (baseScalar f)) (baseScalar_finite f)

end KltDP.Geometry.ProperAffineSections
