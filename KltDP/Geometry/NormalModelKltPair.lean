import KltDP.Geometry.NormalModelKlt

/-!
# Effective rational boundaries and the literal zero-boundary specialization

The canonical frame remains normalized against the actual canonical Weil
representative KX. Only the Cartier numerator becomes a numerator of KX
plus the effective rational boundary. All original normal models, reference
choices, frames and positive numerators are retained. This defines the full
pair hypothesis needed for del Pezzo type and proves its zero specialization;
it does not assert rationality or vanishing.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry
open NormalProjectiveSurface NormalModelCanonical
attribute [local instance] integralSchemeStalk_isDomain
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The all-normal-model discrepancy test with an actual effective rational
boundary. No individual Q-Cartier assumption on KX or the boundary is made. -/
def IsKltPairWithCanonicalDivisor (X : NormalProjectiveSurface k) (KX : X.WeilDivisor)
    (boundary : X.RationalWeilDivisor) : Prop :=
  (∀ C : X.PrimeCurve, 0 ≤ boundary C) ∧
  IsCanonicalWeilDivisor X KX ∧
    X.QCartier ((rationalizeWeilDivisor X KX + boundary)) ∧
    ∀ (U : X.toScheme.Opens) (hne : Nonempty U.toScheme),
      letI : Nonempty U.toScheme := hne
      letI : Nonempty U := ⟨Classical.choice hne⟩
      letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
      IsSmoothOfRelativeDimension 2 (U.ι ≫ X.structureMorphism) →
      (∀ C : X.PrimeCurve, C.genericPoint ∈ U) →
      ∀ (KU : CartierDivisor U.toScheme)
        (eKU : cartierDivisorModule U.toScheme KU ≅
          SmoothCanonicalExteriorComparison.relativeDifferentialExterior
            (U.ι ≫ X.structureMorphism) 2),
        OpenCartierWeil.restrictedWeilHom U KU = KX →
        ∀ (V : Scheme.{u}) [IsIntegral V] (hnormal : IsNormalScheme V)
          (v : V ⟶ X.toScheme) [LocallyOfFiniteType (v ≫ X.structureMorphism)]
          (hv : IsBirationalScheme v) (x : CodimensionOnePoint V),
          letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
          letI : IsDiscreteValuationRing (V.presheaf.stalk x.val) :=
            normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
          (∃ F : LocalFrame (v ≫ X.structureMorphism) x.val,
            IsNormalized X U KU eKU v x.val F) ∧
          ∀ F : LocalFrame (v ≫ X.structureMorphism) x.val,
            IsNormalized X U KU eKU v x.val F →
            ∀ (n : ℕ), 0 < n → ∀ A : CartierDivisor X.toScheme,
              rationalizeWeilDivisor X (X.cartierToWeilHom A) =
                n • (rationalizeWeilDivisor X KX + boundary) →
              (-1 : ℚ) < discrepancyForCartierMultiple X v x.val F n A

/-- KLT for the actual effective rational pair. -/
def IsKltPair (X : NormalProjectiveSurface k) (boundary : X.RationalWeilDivisor) : Prop :=
  ∃ KX : X.WeilDivisor, IsKltPairWithCanonicalDivisor X KX boundary

/-- Boundary zero recovers exactly the existing all-normal-model predicate. -/
theorem isKltPairWithCanonicalDivisor_zero_iff (X : NormalProjectiveSurface k)
    (KX : X.WeilDivisor) :
    IsKltPairWithCanonicalDivisor X KX 0 ↔ IsKltWithCanonicalDivisor X KX := by
  constructor
  · rintro ⟨_, h⟩
    simpa only [IsKltWithCanonicalDivisor, add_zero] using h
  · intro h
    refine ⟨?_, ?_⟩
    · intro C
      change (0 : ℚ) ≤ 0
      exact le_rfl
    · simpa only [IsKltWithCanonicalDivisor, add_zero] using h

/-- No extra boundary, reference, model or Cartier-index hypothesis is needed
for the ordinary zero-boundary specialization. -/
theorem isKltPair_zero_iff (X : NormalProjectiveSurface k) :
    IsKltPair X 0 ↔ IsKlt X := by
  simp only [IsKltPair, IsKlt, isKltPairWithCanonicalDivisor_zero_iff]

end KltDP.Geometry

#check @KltDP.Geometry.IsKltPairWithCanonicalDivisor
#print axioms KltDP.Geometry.isKltPairWithCanonicalDivisor_zero_iff
#print axioms KltDP.Geometry.isKltPair_zero_iff
