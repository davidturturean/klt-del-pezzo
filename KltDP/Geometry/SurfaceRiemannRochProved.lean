import KltDP.Literature.Hartshorne.SurfaceRiemannRoch

/-!
# The full surface Riemann--Roch formula and actual effective divisors

The individually reviewed full published statement supplies the existing
original-object specialization proofs. No hypothetical RR parameter remains.
The effective-divisor conclusions retain their genuine complementary-section
vanishing and positive numerical-expression hypotheses. No top-duality
identity or Euler-characteristic-one statement is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Geometry.SmoothCanonicalCartierRepresentative

universe u

namespace KltDP.Geometry.SurfaceRiemannRochProved

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The complete three-term RR formula for the original integral divisors
and any original canonical divisor on this regular projective surface. -/
theorem riemannRoch (D K : X.WeilDivisor) (hK : IsCanonical X hregular K) :
    (hDimension X hregular D 0 : ℚ) - (hDimension X hregular D 1 : ℚ) +
      (hDimension X hregular (K - D) 0 : ℚ) = rrNumber X hregular D K :=
  SurfaceRiemannRochSource.raw_apply X hregular
    KltDP.Literature.Hartshorne.surface_riemannRoch_literal D K hK

/-- The published formula produces an original nonzero section. -/
theorem exists_nonzero_section (D K : X.WeilDivisor)
    (hK : IsCanonical X hregular K)
    (hvanish : Subsingleton (sections (divisorModule X hregular (K - D))))
    (hpositive : 0 < rrNumber X hregular D K) :
    ∃ s : sections (divisorModule X hregular D), s ≠ 0 :=
  SurfaceRiemannRochSource.exists_nonzero_section X hregular
    KltDP.Literature.Hartshorne.surface_riemannRoch_literal D K hK hvanish hpositive

/-- The section gives an effective integral Weil divisor in the original
linear-equivalence class, with its actual finite prime support. -/
theorem exists_effectiveWeil (D K : X.WeilDivisor)
    (hK : IsCanonical X hregular K)
    (hvanish : Subsingleton (sections (divisorModule X hregular (K - D))))
    (hpositive : 0 < rrNumber X hregular D K) :
    ∃ Z : X.WeilDivisor, EffectiveDivisor Z ∧ X.LinearlyEquivalent Z D :=
  SurfaceRiemannRochSource.exists_effectiveWeil X hregular
    KltDP.Literature.Hartshorne.surface_riemannRoch_literal D K hK hvanish hpositive

section SmoothConsumer

variable [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- The original constructed smooth canonical divisor supplies its
canonical condition internally, with no separate canonical-choice input. -/
theorem exists_effectiveWeil_of_constructedCanonical (D : X.WeilDivisor)
    (hvanish : Subsingleton (sections (divisorModule X X.regularPoints_of_isSmooth
      (weilRepresentative X - D))))
    (hpositive : 0 < rrNumber X X.regularPoints_of_isSmooth D (weilRepresentative X)) :
    ∃ Z : X.WeilDivisor, EffectiveDivisor Z ∧ X.LinearlyEquivalent Z D :=
  SurfaceRiemannRochSource.exists_effectiveWeil_of_constructedCanonical X
    KltDP.Literature.Hartshorne.surface_riemannRoch_literal D hvanish hpositive

end SmoothConsumer

end KltDP.Geometry.SurfaceRiemannRochProved

set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.explicit false
set_option pp.maxSteps 1000000
set_option pp.notation false

#check @KltDP.Literature.Hartshorne.surface_riemannRoch_literal
#print axioms KltDP.Literature.Hartshorne.surface_riemannRoch_literal
#check @KltDP.Geometry.SurfaceRiemannRochProved.riemannRoch
#print axioms KltDP.Geometry.SurfaceRiemannRochProved.riemannRoch
#check @KltDP.Geometry.SurfaceRiemannRochProved.exists_nonzero_section
#print axioms KltDP.Geometry.SurfaceRiemannRochProved.exists_nonzero_section
#check @KltDP.Geometry.SurfaceRiemannRochProved.exists_effectiveWeil_of_constructedCanonical
#print axioms KltDP.Geometry.SurfaceRiemannRochProved.exists_effectiveWeil_of_constructedCanonical
