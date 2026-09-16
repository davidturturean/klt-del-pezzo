import KltDP.Geometry.AffineBlowupComplement
import KltDP.Geometry.ProjectiveSpaceIntegral
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Integrality and the actual function field of an affine blowup

The Rees algebra of an ideal in a domain is the existing polynomial
subalgebra, hence a domain. For a nonzero ideal the complement is nonempty;
the proved complement isomorphism therefore makes its actual Rees Proj
nonempty. The homogeneous zero prime is dense in every nonempty Proj of
a graded domain. Together with the already proved domain-stalk result this
establishes integrality, without finite generation or normality assumptions.

The function-field identification is constructed from the actual generic
stalk maps of the two open immersions from the shared complement. It is an
isomorphism of the existing scheme function fields, not a replacement field
included as construction data. No exceptional-divisor, normality, or
intersection formula is assumed or proved in this file.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- The homogeneous zero prime is a dense point of every nonempty Proj of
a graded domain. Nonemptiness rules out containment of the irrelevant ideal
in the zero ideal. -/
theorem proj_irreducibleSpace_of_isDomain_of_nonempty {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] [IsDomain A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [Nonempty (Proj 𝒜)] :
    IrreducibleSpace (Proj 𝒜) := by
  let p : Proj 𝒜 := Classical.choice inferInstance
  let η : ProjectiveSpectrum 𝒜 :=
    { asHomogeneousIdeal := ⊥
      isPrime := by
        change (⊥ : Ideal A).IsPrime
        exact Ideal.bot_prime
      not_irrelevant_le := fun h => p.not_irrelevant_le (h.trans bot_le) }
  have hη : IsGenericPoint η (Set.univ : Set (Proj 𝒜)) := by
    change closure ({η} : Set (ProjectiveSpectrum 𝒜)) = Set.univ
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    change ProjectiveSpectrum.zeroLocus 𝒜 ((⊥ : Ideal A) : Set A) = Set.univ
    exact ProjectiveSpectrum.zeroLocus_bot _
  exact (irreducibleSpace_def _).mpr hη.isIrreducible

/-- Actual nonempty Proj of a graded domain is integral. Reducedness reuses
the existing domain-stalk proof in `ProjectiveSpaceIntegral`. -/
theorem proj_isIntegral_of_isDomain_of_nonempty {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] [IsDomain A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [Nonempty (Proj 𝒜)] :
    IsIntegral (Proj 𝒜) := by
  letI : IrreducibleSpace (Proj 𝒜) :=
    proj_irreducibleSpace_of_isDomain_of_nonempty 𝒜
  letI : IsReduced (Proj 𝒜) := proj_isReduced_of_isDomain 𝒜
  exact isIntegral_of_irreducibleSpace_of_isReduced (Proj 𝒜)

/-- An actual open immersion between irreducible schemes identifies their
generic-point stalks. For integral schemes these are the actual fields of
rational functions. -/
def openImmersionFunctionFieldIso {U X : Scheme.{u}}
    [IrreducibleSpace U] [IrreducibleSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] : X.functionField ≅ U.functionField :=
  X.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
    asIso (j.stalkMap (genericPoint U))

namespace AffineBlowup

variable {R : Type u} [CommRing R] [IsDomain R] (I : Ideal R)

/-- The generic zero prime of the base lies outside a nonzero center. -/
theorem bot_mem_centerComplement (hI : I ≠ ⊥) :
    (⊥ : PrimeSpectrum R) ∈ centerComplement I := by
  change ¬ I ≤ (⊥ : Ideal R)
  exact fun h => hI (le_antisymm h bot_le)

/-- The actual complement of a nonzero ideal is nonempty. -/
theorem centerComplement_nonempty (hI : I ≠ ⊥) :
    Nonempty (centerComplement I).toScheme :=
  ⟨⟨(⊥ : PrimeSpectrum R), bot_mem_centerComplement I hI⟩⟩

/-- The established complement isomorphism supplies a point of its actual
inverse image before any integrality of the blowup is used. -/
theorem preimage_centerComplement_nonempty (hI : I ≠ ⊥) :
    Nonempty ((toSpec I) ⁻¹ᵁ centerComplement I).toScheme :=
  ⟨(complementIso I).inv.base (Classical.choice (centerComplement_nonempty I hI))⟩

/-- Blowing up a nonzero ideal in a domain gives a nonempty actual scheme. -/
theorem scheme_nonempty (hI : I ≠ ⊥) : Nonempty (scheme I) :=
  ⟨((toSpec I) ⁻¹ᵁ centerComplement I).ι.base
    (Classical.choice (preimage_centerComplement_nonempty I hI))⟩

/-- The existing Rees Proj is integral, derived from the original domain
and the literal nonzero-ideal condition. No integrality is supplied as data. -/
theorem scheme_isIntegral (hI : I ≠ ⊥) : IsIntegral (scheme I) := by
  letI : Nonempty (Proj (ReesGrading.component I)) := scheme_nonempty I hI
  exact proj_isIntegral_of_isDomain_of_nonempty (ReesGrading.component I)

/-- Every nonzero center has dense open complement in the original base. -/
theorem centerComplement_dense (hI : I ≠ ⊥) :
    Dense (centerComplement I : Set (Spec (CommRingCat.of R))) :=
  (centerComplement I).isOpen.dense ⟨(⊥ : PrimeSpectrum R), bot_mem_centerComplement I hI⟩

/-- The inverse image of the center complement is dense in the actual
blowup, by the newly derived integrality and its concrete nonempty witness. -/
theorem preimage_centerComplement_dense (hI : I ≠ ⊥) :
    Dense (((toSpec I) ⁻¹ᵁ centerComplement I) : Set (scheme I)) := by
  letI : IsIntegral (scheme I) := scheme_isIntegral I hI
  obtain ⟨p⟩ := preimage_centerComplement_nonempty I hI
  exact ((toSpec I) ⁻¹ᵁ centerComplement I).isOpen.dense ⟨p.1, p.2⟩

/-- The canonical structure morphism sends the actual generic point of the
blowup to the actual generic point of the base. Its integrality instance is
the theorem above, not an additional assumption. -/
theorem toSpec_genericPoint (hI : I ≠ ⊥) :
    letI : IsIntegral (scheme I) := scheme_isIntegral I hI
    (toSpec I).base (genericPoint (scheme I)) =
      genericPoint (Spec (CommRingCat.of R)) := by
  letI : IsIntegral (scheme I) := scheme_isIntegral I hI
  let V := (toSpec I) ⁻¹ᵁ centerComplement I
  letI : Nonempty V.toScheme := preimage_centerComplement_nonempty I hI
  have hV := genericPoint_eq_of_isOpenImmersion V.ι
  have hR := genericPoint_eq_of_isOpenImmersion
    ((complementIso I).hom ≫ (centerComplement I).ι)
  calc
    (toSpec I).base (genericPoint (scheme I)) =
        (toSpec I).base (V.ι.base (genericPoint V.toScheme)) :=
      congrArg (toSpec I).base hV.symm
    _ = ((complementIso I).hom ≫ (centerComplement I).ι).base
        (genericPoint V.toScheme) :=
      congrArg (fun f : V.toScheme ⟶ Spec (CommRingCat.of R) =>
        f.base (genericPoint V.toScheme)) (complementIso_hom_ι I).symm
    _ = genericPoint (Spec (CommRingCat.of R)) := hR

/-- The actual function fields are identified by restriction to their
shared dense open subscheme. The direction is the contravariant direction
from the base field to the blowup field. -/
def functionFieldIso (hI : I ≠ ⊥) :
    letI : IsIntegral (scheme I) := scheme_isIntegral I hI
    (Spec (CommRingCat.of R)).functionField ≅ (scheme I).functionField := by
  letI : IsIntegral (scheme I) := scheme_isIntegral I hI
  let V := (toSpec I) ⁻¹ᵁ centerComplement I
  letI : Nonempty V.toScheme := preimage_centerComplement_nonempty I hI
  exact openImmersionFunctionFieldIso
      ((complementIso I).hom ≫ (centerComplement I).ι) ≪≫
    (openImmersionFunctionFieldIso V.ι).symm

/-- The field identification has the exact common-open normalization: its
composition with the blowup restriction equals the base restriction. -/
theorem functionFieldIso_hom_restriction (hI : I ≠ ⊥) :
    letI : IsIntegral (scheme I) := scheme_isIntegral I hI
    letI : Nonempty ((toSpec I) ⁻¹ᵁ centerComplement I).toScheme :=
      preimage_centerComplement_nonempty I hI
    (functionFieldIso I hI).hom ≫
        (openImmersionFunctionFieldIso ((toSpec I) ⁻¹ᵁ centerComplement I).ι).hom =
      (openImmersionFunctionFieldIso
        ((complementIso I).hom ≫ (centerComplement I).ι)).hom := by
  letI : IsIntegral (scheme I) := scheme_isIntegral I hI
  letI : Nonempty ((toSpec I) ⁻¹ᵁ centerComplement I).toScheme :=
    preimage_centerComplement_nonempty I hI
  simp [functionFieldIso]

/-- A ring equivalence of the two existing function fields, obtained from
the generic-stalk isomorphism with its proved common-open normalization. -/
def functionFieldEquiv (hI : I ≠ ⊥) :
    letI : IsIntegral (scheme I) := scheme_isIntegral I hI
    (Spec (CommRingCat.of R)).functionField ≃+* (scheme I).functionField := by
  letI : IsIntegral (scheme I) := scheme_isIntegral I hI
  exact (functionFieldIso I hI).commRingCatIsoToRingEquiv

end AffineBlowup

end KltDP.Geometry
