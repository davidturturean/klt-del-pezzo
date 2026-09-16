import KltDP.LinearAlgebra.OrthogonalCopyGram
import KltDP.LinearAlgebra.PrincipalSubmatrixComparison
import Mathlib.Data.Fintype.Card

/-!
# Removing branch indices before taking two orthogonal copies

An actual subset of a finite family is removed. Positive definiteness of
the original negative Gram matrix implies positive definiteness on the
remaining indices by the proved principal-submatrix adapter. Two supplied
families with the same actual pairings as the remaining original family
and zero cross-pairings therefore span twice the complement cardinality.
The cardinality is computed from the actual removed subset, not supplied
as a separate rank assumption.

In the presence of an actual positive target vector this contradicts the
target dimension identity `2 * (r - n)`. This is the linear-algebra part
of the final paragraph of manuscript `thm:no-even-nodes`. The original
and target bilinear spaces may differ, as they do for divisor classes on
the original and covering surfaces. Constructing those spaces and the
lifted curves, proving the intersection equalities and positivity, and
deriving the geometric Picard identity remain separate obligations.
-/

noncomputable section

namespace KltDP.LinearAlgebra

open Matrix CanonicalCorrection

/-- Reindexing an actual family takes the corresponding actual principal
submatrix of its negative Gram matrix. No injectivity is needed here. -/
theorem negativeGram_reindex {R S I J : Type*} [CommRing R]
    [AddCommGroup S] [Module R S] (B : LinearMap.BilinForm R S)
    (v : I → S) (e : J → I) :
    negativeGram B (v ∘ e) = (negativeGram B v).submatrix e e := rfl

/-- An injectively selected actual subfamily inherits positive definiteness
from the original negative Gram matrix. -/
theorem negativeGram_reindex_posDef {S I J : Type*}
    [AddCommGroup S] [Module ℚ S] [Fintype I] [Fintype J]
    (B : LinearMap.BilinForm ℚ S) (v : I → S)
    (hA : (negativeGram B v).PosDef) (e : J → I) (he : Function.Injective e) :
    (negativeGram B (v ∘ e)).PosDef := by
  classical
  rw [negativeGram_reindex]
  exact posDef_principal_submatrix hA e he

section Complement

variable {S T I : Type*} [AddCommGroup S] [Module ℚ S]
  [AddCommGroup T] [Module ℚ T] [Fintype I]

/-- The span of the actual two copies has twice the size of the actual
complement of the removed indices. Its rank is derived from the pairings. -/
theorem removed_configuration_copies_span_finrank
    (B : LinearMap.BilinForm ℚ S) (v : I → S) (hA : (negativeGram B v).PosDef)
    (removed : I → Prop) [DecidablePred removed]
    (C : LinearMap.BilinForm ℚ T) (left right : {i // ¬removed i} → T)
    (hleft : ∀ i j, C (left i) (left j) = B (v i.val) (v j.val))
    (hright : ∀ i j, C (right i) (right j) = B (v i.val) (v j.val))
    (hlr : ∀ i j, C (left i) (right j) = 0)
    (hrl : ∀ j i, C (right j) (left i) = 0) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (Sum.elim left right))) =
      2 * (Fintype.card I - Fintype.card {i // removed i}) := by
  let A := negativeGram B (v ∘ (Subtype.val : {i // ¬removed i} → I))
  have hrestricted : A.PosDef :=
    negativeGram_reindex_posDef B v hA Subtype.val Subtype.val_injective
  have hleftA : negativeGram C left = A := by
    ext i j
    exact congrArg Neg.neg (hleft i j)
  have hrightA : negativeGram C right = A := by
    ext i j
    exact congrArg Neg.neg (hright i j)
  have h := orthogonal_copies_span_finrank C A hrestricted left right
    hleftA hrightA hlr hrl
  rw [Fintype.card_subtype_compl removed] at h
  exact h

/-- The actual two copies occupy fewer dimensions than the target space
when it contains a positive vector. The complement count is proved here. -/
theorem removed_configuration_copies_card_lt_finrank [FiniteDimensional ℚ T]
    (B : LinearMap.BilinForm ℚ S) (v : I → S) (hA : (negativeGram B v).PosDef)
    (removed : I → Prop) [DecidablePred removed]
    (C : LinearMap.BilinForm ℚ T) (left right : {i // ¬removed i} → T)
    (hleft : ∀ i j, C (left i) (left j) = B (v i.val) (v j.val))
    (hright : ∀ i j, C (right i) (right j) = B (v i.val) (v j.val))
    (hlr : ∀ i j, C (left i) (right j) = 0)
    (hrl : ∀ j i, C (right j) (left i) = 0)
    (hpositive : ∃ x : T, 0 < C x x) :
    2 * (Fintype.card I - Fintype.card {i // removed i}) < Module.finrank ℚ T := by
  let A := negativeGram B (v ∘ (Subtype.val : {i // ¬removed i} → I))
  have hrestricted : A.PosDef :=
    negativeGram_reindex_posDef B v hA Subtype.val Subtype.val_injective
  have hleftA : negativeGram C left = A := by
    ext i j
    exact congrArg Neg.neg (hleft i j)
  have hrightA : negativeGram C right = A := by
    ext i j
    exact congrArg Neg.neg (hright i j)
  have h := orthogonal_copies_card_lt_finrank C A hrestricted left right
    hleftA hrightA hlr hrl hpositive
  rw [Fintype.card_subtype_compl removed] at h
  exact h

/-- The geometric Picard identity contradicts the bound derived from the
actual original family and its two orthogonal surviving copies. -/
theorem removed_configuration_rank_identity_impossible [FiniteDimensional ℚ T]
    (B : LinearMap.BilinForm ℚ S) (v : I → S) (hA : (negativeGram B v).PosDef)
    (removed : I → Prop) [DecidablePred removed]
    (C : LinearMap.BilinForm ℚ T) (left right : {i // ¬removed i} → T)
    (hleft : ∀ i j, C (left i) (left j) = B (v i.val) (v j.val))
    (hright : ∀ i j, C (right i) (right j) = B (v i.val) (v j.val))
    (hlr : ∀ i j, C (left i) (right j) = 0)
    (hrl : ∀ j i, C (right j) (left i) = 0)
    (hpositive : ∃ x : T, 0 < C x x)
    (hdimension : Module.finrank ℚ T =
      2 * (Fintype.card I - Fintype.card {i // removed i})) : False := by
  have h := removed_configuration_copies_card_lt_finrank B v hA removed C left right
    hleft hright hlr hrl hpositive
  rw [hdimension] at h
  exact (lt_irrefl _) h

end Complement

end KltDP.LinearAlgebra
