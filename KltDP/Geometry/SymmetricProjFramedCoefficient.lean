/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeProjectiveBaseChange
import KltDP.Geometry.RelativeProjectiveCoefficientFunctor
import KltDP.Geometry.SheafProjectiveCoefficientNaturality

/-!
# Coefficient maps between original symmetric Proj schemes in actual frames

Actual bases transport the original polynomial coefficient map to the intrinsic
symmetric Proj schemes. Its original base square is cartesian. A single actual
semilinear map preserving two pairs of frames makes the two constructions equal;
no projective map is asserted for an arbitrary semilinear map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Geometry.RelativeSymmetricProj
open RelativeProjectiveChart

variable {R S T M N P : Type u} [CommRing R] [CommRing S] [CommRing T]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  [AddCommGroup P] [Module T P] {n : ℕ}

/-- The coefficient morphism expressed on the actual original modules. -/
def framedCoefficientMorphism (b : Basis (Fin (n + 1)) R M)
    (c : Basis (Fin (n + 1)) S N) (φ : R →+* S) : scheme S N ⟶ scheme R M :=
  (basisIso c).hom ≫ coefficientMorphism n φ ≫ (basisIso b).inv

/-- The original degree-zero structure maps retain the original coefficient map. -/
@[reassoc] theorem framedCoefficientMorphism_toBase (b : Basis (Fin (n + 1)) R M)
    (c : Basis (Fin (n + 1)) S N) (φ : R →+* S) :
    framedCoefficientMorphism b c φ ≫ toBase R M =
      toBase S N ≫ Spec.map (CommRingCat.ofHom φ) := by
  simp only [framedCoefficientMorphism, Category.assoc, basisIso_inv_toBase,
    coefficientMorphism_toBase, basisIso_toBase_assoc]

/-- The original symmetric Proj square is cartesian for actual chosen frames. -/
theorem isPullback_framedCoefficientMorphism (b : Basis (Fin (n + 1)) R M)
    (c : Basis (Fin (n + 1)) S N) (φ : R →+* S) :
    IsPullback (framedCoefficientMorphism b c φ) (toBase S N)
      (toBase R M) (Spec.map (CommRingCat.ofHom φ)) := by
  refine (isPullback_freeProjectivization n φ).of_iso
    (basisIso c).symm (basisIso b).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [framedCoefficientMorphism, Category.assoc]
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id, basisIso_inv_toBase]
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id, basisIso_inv_toBase]
  · simp

/-- The same actual frame with identity coefficients gives the identity morphism. -/
@[simp] theorem framedCoefficientMorphism_id (b : Basis (Fin (n + 1)) R M) :
    framedCoefficientMorphism b b (RingHom.id R) = 𝟙 (scheme R M) := by
  simp [framedCoefficientMorphism]

/-- Shared middle frames give composition over the original coefficient maps. -/
@[reassoc] theorem framedCoefficientMorphism_comp (b : Basis (Fin (n + 1)) R M)
    (c : Basis (Fin (n + 1)) S N) (d : Basis (Fin (n + 1)) T P)
    (φ : R →+* S) (ψ : S →+* T) :
    framedCoefficientMorphism c d ψ ≫ framedCoefficientMorphism b c φ =
      framedCoefficientMorphism b d (ψ.comp φ) := by
  simp only [framedCoefficientMorphism, Category.assoc, Iso.inv_hom_id_assoc,
    coefficientMorphism_comp_assoc]

/-- Two pairs of frames preserved by the same actual semilinear map give the
same morphism between the original symmetric Proj schemes. -/
theorem framedCoefficientMorphism_eq_of_preservesFrames
    (b c : Basis (Fin (n + 1)) R M) (b' c' : Basis (Fin (n + 1)) S N)
    {φ : R →+* S} (f : M →ₛₗ[φ] N)
    (hb : ∀ i, f (b i) = b' i) (hc : ∀ i, f (c i) = c' i) :
    framedCoefficientMorphism b b' φ = framedCoefficientMorphism c c' φ := by
  have h := congrArg (fun k => (basisIso b').hom ≫ k ≫ (basisIso c).inv)
    (transition_coefficientMorphism b c b' c' f hb hc)
  simpa [framedCoefficientMorphism, transition, Category.assoc] using h.symm

end KltDP.Geometry.RelativeSymmetricProj

#print axioms KltDP.Geometry.RelativeSymmetricProj.isPullback_framedCoefficientMorphism
#print axioms KltDP.Geometry.RelativeSymmetricProj.framedCoefficientMorphism_comp
#print axioms KltDP.Geometry.RelativeSymmetricProj.framedCoefficientMorphism_eq_of_preservesFrames
