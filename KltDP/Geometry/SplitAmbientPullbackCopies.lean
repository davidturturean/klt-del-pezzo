import KltDP.Geometry.QuadraticAtlasGlobalSplitting
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The two actual labeled copies in an ambient split pullback

Each copy is the original coproduct injection, the inverse of the actual
splitting, and the original first pullback projection. Its map to the
original base is proved, not supplied. The two pullback images are disjoint;
their ambient images remain disjoint under a preimmersion of the original
curve. A closed original inclusion gives two actual closed immersions.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.SplitAmbientPullbackCopies

open QuadraticAtlasGlobalSplitting

/-- The original scheme coproduct inclusions are closed as well as open. -/
theorem inclusion_isClosedImmersion (C : Scheme.{u}) (ε : Bool) :
    IsClosedImmersion (inclusion ε C) := by
  cases ε <;> dsimp only [inclusion]
  · apply IsClosedImmersion.of_isPreimmersion
    rw [(AlgebraicGeometry.isCompl_range_inl_inr C C).eq_compl]
    exact (IsOpenImmersion.isOpen_range (coprod.inr : C ⟶ C ⨿ C)).isClosed_compl
  · apply IsClosedImmersion.of_isPreimmersion
    rw [(AlgebraicGeometry.isCompl_range_inl_inr C C).symm.eq_compl]
    exact (IsOpenImmersion.isOpen_range (coprod.inl : C ⟶ C ⨿ C)).isClosed_compl

variable {X Z C : Scheme.{u}} (p : Z ⟶ X) (f : C ⟶ X)
    (q : pullback p f ≅ C ⨿ C)

/-- The original positive or negative copy inside the actual pullback. -/
def copyToPullback (ε : Bool) : C ⟶ pullback p f := inclusion ε C ≫ q.inv

/-- Its actual morphism into the original ambient cover. -/
def ambientCopy (ε : Bool) : C ⟶ Z := copyToPullback p f q ε ≫ pullback.fst p f

@[simp, reassoc]
theorem copyToPullback_hom (ε : Bool) : copyToPullback p f q ε ≫ q.hom = inclusion ε C := by
  simp only [copyToPullback, Category.assoc, Iso.inv_hom_id, Category.comp_id]

instance copyToPullback_isClosedImmersion (ε : Bool) :
    IsClosedImmersion (copyToPullback p f q ε) := by
  letI := inclusion_isClosedImmersion C ε
  dsimp only [copyToPullback]
  infer_instance

instance ambientCopy_isClosedImmersion [IsClosedImmersion f] (ε : Bool) :
    IsClosedImmersion (ambientCopy p f q ε) := by
  letI : IsClosedImmersion (pullback.fst p f) :=
    MorphismProperty.pullback_fst (P := @IsClosedImmersion) p f inferInstance
  dsimp only [ambientCopy]
  infer_instance

/-- The two actual pullback copies have disjoint image ranges. -/
theorem copyToPullback_disjoint :
    Disjoint (Set.range (copyToPullback p f q false).base)
      (Set.range (copyToPullback p f q true).base) := by
  change Disjoint (Set.range (q.inv.base ∘ (coprod.inl : C ⟶ C ⨿ C).base))
    (Set.range (q.inv.base ∘ (coprod.inr : C ⟶ C ⨿ C).base))
  rw [Set.range_comp, Set.range_comp]
  exact Set.disjoint_image_of_injective q.inv.isOpenEmbedding.injective
    (AlgebraicGeometry.isCompl_range_inl_inr C C).disjoint

/-- A preimmersion of the original curve preserves disjointness in the ambient cover. -/
theorem ambientCopy_disjoint [IsPreimmersion f] :
    Disjoint (Set.range (ambientCopy p f q false).base)
      (Set.range (ambientCopy p f q true).base) := by
  letI : IsPreimmersion (pullback.fst p f) :=
    MorphismProperty.pullback_fst (P := @IsPreimmersion) p f inferInstance
  change Disjoint
    (Set.range ((pullback.fst p f).base ∘ (copyToPullback p f q false).base))
    (Set.range ((pullback.fst p f).base ∘ (copyToPullback p f q true).base))
  rw [Set.range_comp, Set.range_comp]
  exact Set.disjoint_image_of_injective (pullback.fst p f).isEmbedding.injective
    (copyToPullback_disjoint p f q)

variable (hq : q.hom ≫ coprod.desc (𝟙 C) (𝟙 C) = pullback.snd p f)

include hq in
theorem inv_snd : q.inv ≫ pullback.snd p f = coprod.desc (𝟙 C) (𝟙 C) := by
  rw [← hq, Iso.inv_hom_id_assoc]

include hq in
/-- Each labeled pullback copy is an actual section of the original second projection. -/
@[reassoc]
theorem copyToPullback_snd (ε : Bool) : copyToPullback p f q ε ≫ pullback.snd p f = 𝟙 C := by
  rw [copyToPullback, Category.assoc, inv_snd p f q hq]
  cases ε <;> simp only [inclusion, coprod.inl_desc, coprod.inr_desc]

include hq in
/-- Each actual ambient copy projects to precisely the original morphism of the curve. -/
@[reassoc]
theorem ambientCopy_projection (ε : Bool) : ambientCopy p f q ε ≫ p = f := by
  rw [ambientCopy, Category.assoc, pullback.condition, ← Category.assoc,
    copyToPullback_snd p f q hq, Category.id_comp]

end KltDP.Geometry.SplitAmbientPullbackCopies

#print axioms KltDP.Geometry.SplitAmbientPullbackCopies.ambientCopy_projection
#print axioms KltDP.Geometry.SplitAmbientPullbackCopies.ambientCopy_disjoint
