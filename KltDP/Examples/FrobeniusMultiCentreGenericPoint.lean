import KltDP.Geometry.BirationalAdapters
import KltDP.Geometry.CartierDivisorPullback
import KltDP.Examples.FrobeniusMultiCentreIntegral
import KltDP.Examples.FrobeniusMultiCentreExceptional

/-!
# Birationality and generic points of the actual multi-centre projections

The accepted projection `multiProjection p n a` is an isomorphism over the
nonempty complement of the selected centres `(a i, (a i)^p)`. The projection to
one tower at positive depth is an isomorphism over the preimage of that same
complement. Its nonemptiness follows from the accepted isomorphism of the
selected tower over this complement.

The existing birationality adapter supplies the actual generic-point equation
and the isomorphism of generic stalks. The equation then supplies the original
`GenericPointPreserving` class used by the Cartier/function-field pullback API.
All integrality proofs are supplied by the accepted constructions. The only
geometric hypotheses are algebraic closure and distinct parameters; no
projectivity, characteristic or birationality premise is added. At depth one
the selected affine centres lie on the diagonal `(a i, a i)`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreGenericPoint

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusTranslatedCharts
  FrobeniusContactTowerSelectedPoint FrobeniusMultiCentreSurface
  FrobeniusMultiCentreIntegral FrobeniusMultiCentreExceptional
  FrobeniusTowerFunctionField.PlaneChartedScheme

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The actual projection to `P¹ × P¹` is birational, with the source's
integrality supplied by the accepted multi-centre construction. -/
theorem multiProjection_isBirationalScheme (p n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) :
    letI : IsIntegral (multiSurface p n a) := multiSurface_isIntegral p n a ha
    letI : IsIntegral (projectiveProduct k) :=
      FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
    IsBirationalScheme (multiProjection p n a) := by
  letI : IsIntegral (multiSurface p n a) := multiSurface_isIntegral p n a ha
  letI : IsIntegral (projectiveProduct k) :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  letI : Nonempty (earlierComplement p n a).toScheme := earlierComplement_nonempty p n a
  letI : IsIso (multiProjection p n a ∣_ earlierComplement p n a) :=
    multiProjection_restrict_isIso p n a _ (not_mem_earlierComplement p n a)
  exact isBirationalScheme_of_isIso_restrict (multiProjection p n a) (earlierComplement p n a)

/-- The original Cartier pullback API applies to the actual multi-centre
projection: its generic point maps to the generic point of the product. -/
theorem multiProjection_genericPointPreserving (p n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) :
    letI : IsIntegral (multiSurface p n a) := multiSurface_isIntegral p n a ha
    letI : IsIntegral (projectiveProduct k) :=
      FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
    GenericPointPreserving (multiProjection p n a) := by
  letI : IsIntegral (multiSurface p n a) := multiSurface_isIntegral p n a ha
  letI : IsIntegral (projectiveProduct k) :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  exact ⟨(multiProjection_isBirationalScheme p n a ha).map_genericPoint⟩

/-- At positive depth, the actual projection to any selected tower is
birational. The common centre complement gives a nonempty isomorphism open. -/
theorem towerProjection_isBirationalScheme (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (i : Fin n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    letI : IsIntegral (translatedInitial (q + 1) (a i)).carrier :=
      FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
    letI : IsIntegral (selectedStage (q + 1) (a i) (q + 1)) :=
      instStageIsIntegral (translatedInitial (q + 1) (a i)) (q + 1)
    IsBirationalScheme (towerProjection (q + 1) n a i) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsIntegral (translatedInitial (q + 1) (a i)).carrier :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  letI : IsIntegral (selectedStage (q + 1) (a i) (q + 1)) :=
    instStageIsIntegral (translatedInitial (q + 1) (a i)) (q + 1)
  let U := earlierComplement (q + 1) n a
  let V := selectedProjection (q + 1) (a i) (q + 1) ⁻¹ᵁ U
  letI : Nonempty U.toScheme := earlierComplement_nonempty (q + 1) n a
  letI : IsIso (selectedProjection (q + 1) (a i) (q + 1) ∣_ U) :=
    selectedProjection_restrict_isIso (q + 1) (a i) U
      (not_mem_earlierComplement (q + 1) n a i)
  letI : Nonempty V.toScheme := by
    obtain ⟨x, hx⟩ := preimage_nonempty_of_isIso_restrict
      (selectedProjection (q + 1) (a i) (q + 1)) U
    exact ⟨⟨x, hx⟩⟩
  letI : IsIso (towerProjection (q + 1) n a i ∣_ V) :=
    towerProjection_restrict_isIso q n a i U
      (fun j _ => not_mem_earlierComplement (q + 1) n a j)
  exact isBirationalScheme_of_isIso_restrict (towerProjection (q + 1) n a i) V

/-- The original Cartier/function-field pullback applies to the actual
projection to any selected tower at positive depth. -/
theorem towerProjection_genericPointPreserving (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (i : Fin n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    letI : IsIntegral (translatedInitial (q + 1) (a i)).carrier :=
      FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
    letI : IsIntegral (selectedStage (q + 1) (a i) (q + 1)) :=
      instStageIsIntegral (translatedInitial (q + 1) (a i)) (q + 1)
    GenericPointPreserving (towerProjection (q + 1) n a i) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsIntegral (translatedInitial (q + 1) (a i)).carrier :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  letI : IsIntegral (selectedStage (q + 1) (a i) (q + 1)) :=
    instStageIsIntegral (translatedInitial (q + 1) (a i)) (q + 1)
  exact ⟨(towerProjection_isBirationalScheme q n a ha i).map_genericPoint⟩

end KltDP.Examples.FrobeniusMultiCentreGenericPoint
