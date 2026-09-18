import KltDP.Geometry.NefIsotropicSectionGrowth
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# A nonconstant rational function from independent actual Cartier sections

The original Cartier module is a submodule of the actual rational-function
module. Its global rational-value map is injective and respects the original
base-field scalar action. The quotient of the values of two independent
sections therefore cannot equal any scalar coming from the original base
field. No pencil, ratio-nonconstancy, or basepoint-freeness is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.SmoothCanonicalCartierRepresentative

universe u

namespace KltDP.Geometry.CartierIndependentSectionRatio

section Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The original global Cartier-module section is determined by its
actual value in the original function field. -/
theorem rationalValue_injective (D : CartierDivisor X) :
    Function.Injective (cartierGlobalSectionRationalValue X D) := by
  intro s t h
  apply Subtype.ext
  exact (rationalFunctionModuleSectionsEquiv X ⊤).injective h

/-- The actual quotient of the rational values of the two supplied
original sections; independence proves its denominator is nonzero below. -/
def ratio (D : CartierDivisor X)
    (s : Fin 2 → sections (cartierDivisorModule X D)) : X.functionField :=
  cartierGlobalSectionRationalValue X D (s 0) /
    cartierGlobalSectionRationalValue X D (s 1)

end Scheme

section OverField

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The original base-field scalar map, through the original structure
morphism's global sections and the original generic-point germ. -/
def baseFieldToFunctionField : k →+* X.functionField :=
  (algebraMap Γ(X, ⊤) X.functionField).comp (baseFieldToGlobalSections f)

/-- The actual rational-value map respects precisely the scalar action
used by the original base-field cohomology and section constructions. -/
theorem rationalValue_base_smul (D : CartierDivisor X) (a : k)
    (s : sections (cartierDivisorModule X D)) :
    letI := baseSectionsModule f (cartierDivisorModule X D)
    cartierGlobalSectionRationalValue X D (a • s) =
      baseFieldToFunctionField f a * cartierGlobalSectionRationalValue X D s := by
  letI := baseSectionsModule f (cartierDivisorModule X D)
  change rationalFunctionModuleSectionsEquiv X ⊤
      ((baseFieldToGlobalSections f a) • s.val) =
    baseFieldToFunctionField f a * rationalFunctionModuleSectionsEquiv X ⊤ s.val
  rw [map_smul, Algebra.smul_def]
  rfl

/-- If the actual quotient were an original base-field scalar, injectivity
of rational values would make the two original sections linearly dependent. -/
theorem ratio_ne_scalar (D : CartierDivisor X)
    (s : Fin 2 → sections (cartierDivisorModule X D))
    (hs : letI := baseSectionsModule f (cartierDivisorModule X D); LinearIndependent k s)
    (a : k) : ratio X D s ≠ baseFieldToFunctionField f a := by
  letI := baseSectionsModule f (cartierDivisorModule X D)
  obtain ⟨hsOne, hindependent⟩ := linearIndependent_fin2.mp hs
  have hden := cartierGlobalSectionRationalValue_ne_zero X D (s 1) hsOne
  intro hconstant
  have hvalue : cartierGlobalSectionRationalValue X D (s 0) =
      baseFieldToFunctionField f a * cartierGlobalSectionRationalValue X D (s 1) :=
    (div_eq_iff hden).mp hconstant
  apply hindependent a
  apply rationalValue_injective X D
  rw [rationalValue_base_smul f D a (s 1)]
  exact hvalue.symm

/-- Two independent actual sections produce a rational function outside
the image of every original base-field scalar. -/
theorem exists_nonconstant_rationalFunction (D : CartierDivisor X)
    (s : Fin 2 → sections (cartierDivisorModule X D))
    (hs : letI := baseSectionsModule f (cartierDivisorModule X D); LinearIndependent k s) :
    ∃ q : X.functionField, ∀ a : k, q ≠ baseFieldToFunctionField f a :=
  ⟨ratio X D s, fun a => ratio_ne_scalar f D s hs a⟩

end OverField

section SmoothSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- Actual nef isotropic section growth constructs a nonconstant rational
function on the original smooth surface, using the constructed canonical
divisor and no supplied sections, pencil, or rational function. -/
theorem exists_nonconstant_of_nef_isotropic (A : CartierDivisor X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A))
    (hAA : intersectionPairing X X.regularPoints_of_isSmooth A A = 0)
    (hKA : intersectionPairing X X.regularPoints_of_isSmooth
      ((X.regularCartierWeilEquiv X.regularPoints_of_isSmooth).symm (weilRepresentative X)) A < 0) :
    ∃ q : X.toScheme.functionField, ∀ a : k,
      q ≠ baseFieldToFunctionField X.structureMorphism a := by
  obtain ⟨n, _, s, hs⟩ :=
    NefIsotropicSectionGrowth.exists_two_independent_sections_of_constructedCanonical
      X A hA hAA hKA 1
  exact exists_nonconstant_rationalFunction X.structureMorphism (n • A) s hs

end SmoothSurface

end KltDP.Geometry.CartierIndependentSectionRatio
