import KltDP.Geometry.SmoothCanonicalExteriorComparison
import KltDP.Geometry.SmoothCanonicalCartierRepresentative

/-!
# Cartier representatives of the intrinsic top-differential sheaf

The actual Cartier divisor constructed on a smooth integral surface represents
the independently defined second exterior sheaf of relative differentials.
Representatives obtained from different actual Kähler atlases differ by the
divisor of an actual nonzero rational function. No duality or valuation formula
is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SmoothCanonicalCartierExterior

open SmoothCanonicalExteriorComparison SmoothCanonicalCartierRepresentative

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The original Cartier representative has the intrinsic top-differential sheaf. -/
def representativeIsoExterior [IsSmoothOfRelativeDimension 2 f] :
    cartierDivisorModule X (cartierRepresentative f) ≅
      relativeDifferentialExterior f 2 :=
  cartierRepresentativeIso f ≪≫ canonicalSheafOfSmoothSurfaceIsoExterior f

/-- Two Cartier representatives of the same intrinsic exterior sheaf differ by
the principal divisor of an actual rational function. -/
theorem exterior_choices_principal (n : ℕ) (D E : CartierDivisor X)
    (eD : cartierDivisorModule X D ≅ relativeDifferentialExterior f n)
    (eE : cartierDivisorModule X E ≅ relativeDifferentialExterior f n) :
    ∃ q : X.functionFieldˣ,
      D - E = principalCartierDivisorHom X (Additive.ofMul q) := by
  have hclass := cartierPicardClass_eq_of_iso X D E (eD ≪≫ eE.symm)
  apply (cartierPicardClass_eq_one_iff X (D - E)).mp
  rw [cartierPicardClass_sub, hclass]
  exact div_self' (cartierPicardClass X E)

/-- Changing the actual differential atlas preserves the Cartier class, with
its original rational-function witness. -/
theorem atlas_choices_principal {ι κ : Type u} {n : ℕ}
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (b : ∀ i, letI := KaehlerChartAtlas.chartAlgebra f U hU i;
      Basis (Fin n) Γ(X, U i) (KaehlerDifferential k Γ(X, U i)))
    (hcovU : (⨆ i, U i) = ⊤)
    (V : κ → X.Opens) (hV : ∀ j, IsAffineOpen (V j))
    (c : ∀ j, letI := KaehlerChartAtlas.chartAlgebra f V hV j;
      Basis (Fin n) Γ(X, V j) (KaehlerDifferential k Γ(X, V j)))
    (hcovV : (⨆ j, V j) = ⊤)
    (D E : CartierDivisor X)
    (eD : cartierDivisorModule X D ≅
      (KaehlerChartAtlas.canonicalSheaf f U hU b hcovU).obj)
    (eE : cartierDivisorModule X E ≅
      (KaehlerChartAtlas.canonicalSheaf f V hV c hcovV).obj) :
    ∃ q : X.functionFieldˣ,
      D - E = principalCartierDivisorHom X (Additive.ofMul q) :=
  exterior_choices_principal f n D E
    (eD ≪≫ kaehlerChartAtlasIso f U hU b hcovU)
    (eE ≪≫ kaehlerChartAtlasIso f V hV c hcovV)

end KltDP.Geometry.SmoothCanonicalCartierExterior
