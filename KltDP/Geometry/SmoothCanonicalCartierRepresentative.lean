import KltDP.Geometry.SmoothSurfaceKaehlerAtlas
import KltDP.Geometry.CartierPicardComparison
import KltDP.Geometry.CartierWeilClassMap

/-!
# Cartier representatives of the constructed smooth-surface line bundle

The accepted Kähler atlas constructs an invertible sheaf on a scheme smooth
of relative dimension two over a field. On an integral scheme, the accepted
Cartier-to-Picard construction supplies an actual Cartier representative and
an isomorphism from its original O(K). Any two representatives of this same
line bundle differ by the divisor of an actual nonzero rational function.
The original Cartier-to-Weil map preserves that function on a normal
projective surface.

This is a representative of the constructed Kähler-frame line bundle.
Identification with the dualizing sheaf, rational-top-form valuation
formulas, birational compatibility, adjunction, and duality are separate
mathematical obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SmoothCanonicalCartierRepresentative

open SmoothSurfaceKaehlerAtlas

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsSmoothOfRelativeDimension 2 f]

/-- The produced smooth-surface line bundle has an actual Cartier representative. -/
theorem exists_representative :
    ∃ D : CartierDivisor X,
      Nonempty (cartierDivisorModule X D ≅ (canonicalSheafOfSmoothSurface f).obj) := by
  obtain ⟨D, ⟨e⟩⟩ :=
    exists_cartierDivisor_module_iso X (canonicalSheafOfSmoothSurface f).obj
  exact ⟨D, ⟨e.symm⟩⟩

/-- A chosen actual Cartier representative of the Kähler-frame line bundle. -/
def cartierRepresentative : CartierDivisor X :=
  (exists_representative f).choose

/-- The original divisor sheaf is isomorphic to the constructed line bundle. -/
def cartierRepresentativeIso :
    cartierDivisorModule X (cartierRepresentative f) ≅
      (canonicalSheafOfSmoothSurface f).obj :=
  Classical.choice (exists_representative f).choose_spec

/-- Any two such representatives differ by an actual principal Cartier divisor. -/
theorem choices_principal (D E : CartierDivisor X)
    (eD : cartierDivisorModule X D ≅ (canonicalSheafOfSmoothSurface f).obj)
    (eE : cartierDivisorModule X E ≅ (canonicalSheafOfSmoothSurface f).obj) :
    ∃ q : X.functionFieldˣ,
      D - E = principalCartierDivisorHom X (Additive.ofMul q) := by
  have hclass := cartierPicardClass_eq_of_iso X D E (eD ≪≫ eE.symm)
  apply (cartierPicardClass_eq_one_iff X (D - E)).mp
  rw [cartierPicardClass_sub, hclass]
  exact div_self' (cartierPicardClass X E)

section Surface

variable (S : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 S.structureMorphism]

/-- The finite Weil divisor of the chosen Cartier representative. -/
def weilRepresentative : S.WeilDivisor :=
  S.cartierToWeilHom (cartierRepresentative S.structureMorphism)

/-- Choice independence uses the same original rational function in the Weil relation. -/
theorem choices_linearlyEquivalent (D E : CartierDivisor S.toScheme)
    (eD : cartierDivisorModule S.toScheme D ≅
      (canonicalSheafOfSmoothSurface S.structureMorphism).obj)
    (eE : cartierDivisorModule S.toScheme E ≅
      (canonicalSheafOfSmoothSurface S.structureMorphism).obj) :
    S.LinearlyEquivalent (S.cartierToWeilHom D) (S.cartierToWeilHom E) := by
  obtain ⟨q, hq⟩ := choices_principal S.structureMorphism D E eD eE
  exact ⟨q, S.cartierToWeilHom_sub_of_principal D E q hq⟩

end Surface

end KltDP.Geometry.SmoothCanonicalCartierRepresentative
