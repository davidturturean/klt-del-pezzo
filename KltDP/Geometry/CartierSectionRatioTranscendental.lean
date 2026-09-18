import KltDP.Geometry.CartierIndependentSectionRatio
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Algebraic.Integral

/-!
# The actual section ratio gives an embedding of the rational function field

Over an algebraically closed base, an algebraic element has linear minimal
polynomial and lies in the original base-field image. Thus the already
proved nonconstant Cartier-section ratio is transcendental for the actual
base scalar algebra. Pinned polynomial evaluation and `RatFunc.liftAlgHom`
then construct an injective k-algebra map k(t) into the original function
field, sending t to that same actual section ratio.

This is a function-field inclusion. No global P1 morphism, pencil,
basepoint-freeness, or separability is asserted or supplied as a premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.SmoothCanonicalCartierRepresentative
open KltDP.Geometry.CartierIndependentSectionRatio

universe u

namespace KltDP.Geometry.CartierSectionRatioTranscendental

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The actual base algebra is the already constructed original structure
map followed by the original generic-point germ. -/
abbrev baseFunctionFieldAlgebra : Algebra k X.functionField :=
  (baseFieldToFunctionField f).toAlgebra

/-- Over the original algebraically closed field, an element outside its
actual scalar image cannot be algebraic. This uses the pinned minimal
polynomial theorems rather than an assumed transcendence statement. -/
theorem transcendental_of_ne_scalar (q : X.functionField)
    (hq : ∀ a : k, q ≠ baseFieldToFunctionField f a) :
    letI := baseFunctionFieldAlgebra f
    Transcendental k q := by
  letI := baseFunctionFieldAlgebra f
  intro halgebraic
  have hdegree := IsAlgClosed.degree_eq_one_of_irreducible k
    (minpoly.irreducible halgebraic.isIntegral)
  obtain ⟨a, ha⟩ := minpoly.mem_range_of_degree_eq_one k q hdegree
  exact hq a ha.symm

/-- The ratio of the two independent original Cartier sections is
transcendental for the exact scalar action of the original base field. -/
theorem ratio_transcendental (D : CartierDivisor X)
    (s : Fin 2 → sections (cartierDivisorModule X D))
    (hs : letI := baseSectionsModule f (cartierDivisorModule X D); LinearIndependent k s) :
    letI := baseFunctionFieldAlgebra f
    Transcendental k (ratio X D s) :=
  transcendental_of_ne_scalar f (ratio X D s) (fun a => ratio_ne_scalar f D s hs a)

/-- Evaluate the rational-function variable at the original section ratio.
Injective polynomial evaluation supplies the exact denominator condition
required by the pinned rational-function lift. -/
def ratioRatFuncHom (D : CartierDivisor X)
    (s : Fin 2 → sections (cartierDivisorModule X D))
    (hs : letI := baseSectionsModule f (cartierDivisorModule X D); LinearIndependent k s) :
    letI := baseFunctionFieldAlgebra f
    RatFunc k →ₐ[k] X.functionField := by
  letI := baseFunctionFieldAlgebra f
  let φ : k[X] →ₐ[k] X.functionField := Polynomial.aeval (ratio X D s)
  have hφ : Function.Injective φ :=
    transcendental_iff_injective.mp (ratio_transcendental f D s hs)
  exact RatFunc.liftAlgHom φ
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ)

/-- The resulting actual field map is injective. -/
theorem ratioRatFuncHom_injective (D : CartierDivisor X)
    (s : Fin 2 → sections (cartierDivisorModule X D))
    (hs : letI := baseSectionsModule f (cartierDivisorModule X D); LinearIndependent k s) :
    letI := baseFunctionFieldAlgebra f
    Function.Injective (ratioRatFuncHom f D s hs) := by
  letI := baseFunctionFieldAlgebra f
  exact (ratioRatFuncHom f D s hs).toRingHom.injective

/-- The rational-function variable is sent to the original quotient of
the two actual section values. -/
theorem ratioRatFuncHom_variable (D : CartierDivisor X)
    (s : Fin 2 → sections (cartierDivisorModule X D))
    (hs : letI := baseSectionsModule f (cartierDivisorModule X D); LinearIndependent k s) :
    letI := baseFunctionFieldAlgebra f
    ratioRatFuncHom f D s hs (algebraMap k[X] (RatFunc k) Polynomial.X) = ratio X D s := by
  letI := baseFunctionFieldAlgebra f
  let φ : k[X] →ₐ[k] X.functionField := Polynomial.aeval (ratio X D s)
  have hφ : Function.Injective φ :=
    transcendental_iff_injective.mp (ratio_transcendental f D s hs)
  have h := RatFunc.liftAlgHom_apply_div φ
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ) Polynomial.X (1 : k[X])
  simpa only [φ, map_one, div_one, Polynomial.aeval_X] using h

section SmoothSurface

variable (S : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 S.structureMorphism]

local instance source_isSmooth : IsSmooth S.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism

/-- The original nef isotropic divisor and its negative canonical
intersection construct an actual injective k-algebra map k(t) into the
original surface function field. All sections and transcendence are proved. -/
theorem exists_ratFunc_embedding_of_nef_isotropic (A : CartierDivisor S.toScheme)
    (hA : Positivity.IsNef S.structureMorphism
      (cartierDivisorInvertibleSheaf S.toScheme A))
    (hAA : intersectionPairing S S.regularPoints_of_isSmooth A A = 0)
    (hKA : intersectionPairing S S.regularPoints_of_isSmooth
      ((S.regularCartierWeilEquiv S.regularPoints_of_isSmooth).symm (weilRepresentative S)) A < 0) :
    letI := baseFunctionFieldAlgebra S.structureMorphism
    ∃ φ : RatFunc k →ₐ[k] S.toScheme.functionField, Function.Injective φ := by
  letI := baseFunctionFieldAlgebra S.structureMorphism
  obtain ⟨n, _, s, hs⟩ :=
    NefIsotropicSectionGrowth.exists_two_independent_sections_of_constructedCanonical
      S A hA hAA hKA 1
  exact ⟨ratioRatFuncHom S.structureMorphism (n • A) s hs,
    ratioRatFuncHom_injective S.structureMorphism (n • A) s hs⟩

end SmoothSurface

end KltDP.Geometry.CartierSectionRatioTranscendental
