import KltDP.Geometry.SpecPrincipalQuotientStalkKernel
import KltDP.Geometry.EffectiveCartierOfInvertibleIdeal

/-!
# Actual principal quotient equations on image affine opens

The pinned open-base-change kernel formula transports the actual local
principal quotient kernel to the original ambient scheme. Both the
transported equation and its regularity use the canonical section-ring
isomorphisms. This supplies a concrete affine equation for the original
global kernel, rather than a replacement closed subscheme.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.PrincipalQuotientOpenChart

variable {R : Type u} [CommRing R] {Y Z : Scheme.{u}}

/-- The actual image affine open of the original affine chart. -/
def imageAffineOpen (j : Spec (.of R) ⟶ Y) [IsOpenImmersion j] : Y.affineOpens :=
  ⟨j ''ᵁ ⊤, (isAffineOpen_top (Spec (.of R))).image_of_isOpenImmersion j⟩

/-- Actual polynomial coefficients, transported to sections on the original image open. -/
def sectionEquiv (j : Spec (.of R) ⟶ Y) [IsOpenImmersion j] :
    R ≃+* Γ(Y, (imageAffineOpen j).1) :=
  (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.trans
    (j.appIso ⊤).commRingCatIsoToRingEquiv.symm

/-- The original global kernel on the actual chart image has its original transported generator. -/
theorem kernel_ideal_eq_span (f : Z ⟶ Y) [QuasiCompact f]
    (j : Spec (.of R) ⟶ Y) [IsOpenImmersion j] (r : R)
    (i : SpecPrincipalQuotient.scheme r ⟶ Z)
    (H : IsPullback (SpecPrincipalQuotient.inclusion r) i j f) :
    f.ker.ideal (imageAffineOpen j) = Ideal.span {sectionEquiv j r} := by
  let ε := (j.appIso ⊤).commRingCatIsoToRingEquiv
  have h := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f
    (SpecPrincipalQuotient.inclusion r) i j H ⟨⊤, isAffineOpen_top (Spec (.of R))⟩
  rw [SpecPrincipalQuotient.ker_ideal_top] at h
  have h' : (f.ker.ideal (imageAffineOpen j)).comap ε.symm.toRingHom =
      Ideal.span {SpecPrincipalQuotient.sectionOf r} := h.symm
  calc
    f.ker.ideal (imageAffineOpen j) =
        Ideal.map ε.symm.toRingHom ((f.ker.ideal (imageAffineOpen j)).comap ε.symm.toRingHom) :=
      (Ideal.map_comap_of_surjective ε.symm.toRingHom ε.symm.surjective _).symm
    _ = Ideal.span {sectionEquiv j r} := by
      rw [h', Ideal.map_span, Set.image_singleton]
      rfl

/-- The original nonzerodivisor remains regular in the actual ambient chart section ring. -/
theorem sectionEquiv_regular (j : Spec (.of R) ⟶ Y) [IsOpenImmersion j]
    (r : R) (hr : r ∈ nonZeroDivisors R) :
    sectionEquiv j r ∈ nonZeroDivisors Γ(Y, (imageAffineOpen j).1) := by
  apply mem_nonZeroDivisors_of_injective (f := (sectionEquiv j).symm)
    (sectionEquiv j).symm.injective
  simpa only [RingEquiv.symm_apply_apply] using hr

end KltDP.Geometry.PrincipalQuotientOpenChart

#print axioms KltDP.Geometry.PrincipalQuotientOpenChart.kernel_ideal_eq_span
#print axioms KltDP.Geometry.PrincipalQuotientOpenChart.sectionEquiv_regular
