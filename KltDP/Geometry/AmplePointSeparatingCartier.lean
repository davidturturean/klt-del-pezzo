import KltDP.Geometry.AmplePointSeparatingSection
import KltDP.Geometry.EffectiveCartierSectionSupport

/-!
# Actual ample Cartier representatives separating two points

The proved point-ideal section producer and the section-preserving effective
Cartier construction supply an actual divisor whose support contains the chosen
closed point and avoids the distinct point. The original tensor-ideal section,
its literal inclusion image, and the isomorphism from the original Cartier
module are all retained. Serre ampleness supplies a positive tensor power.

No support, section, coherence, frame, or local-epimorphism witness is assumed
in the ample consumer. This proves no general curve-degree strictness and
constructs no witness of IsAmple; those are separate geometric obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AmplePointSeparatingCartier

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} [IsIntegral X]

local instance (Z : Scheme.{u}) : MonoidalCategory Z.Modules :=
  Scheme.Modules.monoidalCategory Z

/-- Global generation of the actual point-ideal twist produces the original
effective Cartier divisor through that point and avoiding the distinct point. -/
theorem exists_point_separating_effectiveCartier (L : InvertibleSheaf X)
    (x y : X) (hclosed : IsClosed ({x} : Set X)) (hne : y ≠ x)
    (hL : Positivity.IsGloballyGenerated
      (L.obj ⊗ schemeKernelIdeal (X.fromSpecResidueField x))) :
    ∃ (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
      (a : cartierDivisorModule X E ≅ L.obj)
      (s : (L.obj ⊗ schemeKernelIdeal (X.fromSpecResidueField x)).val.obj (op ⊤)),
      a.hom.val.app (op ⊤) (effectiveCartierSection X E hE) =
        (SchemeKernelTensor.inclusion (X.fromSpecResidueField x) L.obj).val.app (op ⊤) s ∧
      x ∈ (effectiveCartierIdealDataOfRegularEquations X E hE).support ∧
      y ∉ (effectiveCartierIdealDataOfRegularEquations X E hE).support := by
  obtain ⟨U, hyU, e, s, _, hs, hx, hy⟩ :=
    AmplePointSeparatingSection.exists_point_separating_image_section L x y hclosed hne hL
  obtain ⟨E, hE, a, ha, hxE, hyE⟩ :=
    EffectiveCartierSectionSupport.exists_effectiveCartier_through_and_avoiding X L
      ((SchemeKernelTensor.inclusion (X.fromSpecResidueField x) L.obj).val.app (op ⊤) s)
      hs x y hx U hyU e hy
  exact ⟨E, hE, a, s, ha, hxE, hyE⟩

/-- Serre ampleness supplies a positive power represented by an actual
effective Cartier divisor containing the chosen closed point and avoiding the
distinct point, with the original point-ideal section preserved. -/
theorem exists_positive_power_point_separating_effectiveCartier [IsLocallyNoetherian X]
    (L : InvertibleSheaf X) (hL : AmpleSerre.IsAmple L)
    (x y : X) (hclosed : IsClosed ({x} : Set X)) (hne : y ≠ x) :
    ∃ (n : ℕ), 0 < n ∧ ∃ (M : InvertibleSheaf X), M.toPic = L.toPic ^ n ∧
      ∃ (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
        (a : cartierDivisorModule X E ≅ M.obj)
        (s : (M.obj ⊗ schemeKernelIdeal (X.fromSpecResidueField x)).val.obj (op ⊤)),
        a.hom.val.app (op ⊤) (effectiveCartierSection X E hE) =
          (SchemeKernelTensor.inclusion (X.fromSpecResidueField x) M.obj).val.app (op ⊤) s ∧
        x ∈ (effectiveCartierIdealDataOfRegularEquations X E hE).support ∧
        y ∉ (effectiveCartierIdealDataOfRegularEquations X E hE).support := by
  obtain ⟨n, hn, M, hM, U, hyU, e, s, _, hs, hx, hy⟩ :=
    AmplePointSeparatingSection.exists_positive_power_point_separating_section
      L hL x y hclosed hne
  obtain ⟨E, hE, a, ha, hxE, hyE⟩ :=
    EffectiveCartierSectionSupport.exists_effectiveCartier_through_and_avoiding X M
      ((SchemeKernelTensor.inclusion (X.fromSpecResidueField x) M.obj).val.app (op ⊤) s)
      hs x y hx U hyU e hy
  exact ⟨n, hn, M, hM, E, hE, a, s, ha, hxE, hyE⟩

end KltDP.Geometry.AmplePointSeparatingCartier
