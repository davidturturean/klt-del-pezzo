import KltDP.Geometry.IndependentSectionCartierDivisors
import KltDP.Geometry.SectionEffectiveWeil
import KltDP.Geometry.ProjectiveProper

/-! The actual two independent Cartier sections construct two distinct
effective original Weil members. The returned Cartier-module isomorphisms
carry their canonical sections back to the original supplied sections. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open KltDP.Geometry.ModuleCohomology
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)

local instance independentWeilIntegral : IsIntegral X.toScheme := X.integral

include hX in
/-- Distinctness, effectivity and linear equivalence are proved for the
original divisor objects, preserving both original sections. -/
theorem exists_distinct_effectiveCartier_members_of_independent
    (F : CartierDivisor X.toScheme)
    (s : Fin 2 → sections (cartierDivisorModule X.toScheme F))
    (hs : letI := baseSectionsModule X.structureMorphism (cartierDivisorModule X.toScheme F)
      LinearIndependent k s) :
    ∃ (E : Fin 2 → CartierDivisor X.toScheme)
      (hE : ∀ i, HasRegularCartierEquations X.toScheme (E i))
      (e : ∀ i, cartierDivisorModule X.toScheme (E i) ≅ cartierDivisorModule X.toScheme F),
      (∀ i, (e i).hom.val.app (op (⊤ : X.toScheme.Opens))
        (effectiveCartierSection X.toScheme (E i) (hE i)) = s i) ∧
      (∀ i, X.LinearlyEquivalent (X.cartierToWeilHom (E i)) (X.cartierToWeilHom F)) ∧
      X.cartierToWeilHom (E 0) ≠ X.cartierToWeilHom (E 1) := by
  letI := baseSectionsModule X.structureMorphism (cartierDivisorModule X.toScheme F)
  let q : Fin 2 → X.toScheme.functionFieldˣ := fun i =>
    Units.mk0 (cartierGlobalSectionRationalValue X.toScheme F (s i))
      (cartierGlobalSectionRationalValue_ne_zero X.toScheme F (s i) (hs.ne_zero i))
  let E : Fin 2 → CartierDivisor X.toScheme := fun i =>
    F + principalCartierDivisorHom X.toScheme (Additive.ofMul (q i))
  have hE : ∀ i, HasRegularCartierEquations X.toScheme (E i) := fun i =>
    cartierPrincipalShift_hasRegularEquations X.toScheme F (s i) (q i) rfl
  let e : ∀ i, cartierDivisorModule X.toScheme (E i) ≅ cartierDivisorModule X.toScheme F :=
    fun i => cartierPrincipalShiftIso X.toScheme F (q i)
  refine ⟨E, hE, e, ?_, ?_, ?_⟩
  · intro i
    exact cartierPrincipalShiftIso_canonicalSection X.toScheme F (s i) (q i) rfl (hE i)
  · intro i
    refine ⟨q i, ?_⟩
    change X.cartierToWeilHom
      (F + principalCartierDivisorHom X.toScheme (Additive.ofMul (q i))) -
        X.cartierToWeilHom F = X.principalDivisor (q i)
    rw [map_add, X.cartierToWeilHom_principal]
    abel
  · intro heq
    apply CartierIndependentSectionRatio.principalShifts_ne X.structureMorphism F s hs q
      (fun _ => rfl)
    apply (X.regularCartierWeilEquiv hX).injective
    exact heq

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.exists_distinct_effectiveCartier_members_of_independent
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_distinct_effectiveCartier_members_of_independent
