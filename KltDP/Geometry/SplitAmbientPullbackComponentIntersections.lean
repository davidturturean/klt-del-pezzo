import KltDP.Geometry.SplitAmbientPullbackComponentCopies
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Intersections of the actual component copies

Within either label, the original component intersection scheme is
preserved, with both original projections. Opposite labels have empty
intersection. The corresponding ambient image formulas use the same
original component maps as the doubled component count.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.SplitAmbientPullbackComponentIntersections

open RationalTreePicard SplitAmbientPullbackCopies SplitAmbientPullbackComponentCopies

variable {X Z C : Scheme.{u}} [NoetherianSpace C]
    (p : Z ⟶ X) (f : C ⟶ X) (q : pullback p f ≅ C ⨿ C)

/-- Same-label intersections are exactly the images of the original intersection sets. -/
theorem image_inter_same_label [IsClosedImmersion f] (ε : Bool)
    (D E : ↥(irreducibleComponents C)) :
    componentImage p f q (ε, D) ∩ componentImage p f q (ε, E) =
      (ambientCopy p f q ε).base '' ((D : Set C) ∩ (E : Set C)) := by
  rw [componentImage_eq, componentImage_eq]
  exact (Set.image_inter (ambientCopy p f q ε).isClosedEmbedding.injective).symm

/-- Opposite-label components have disjoint ambient images. -/
theorem image_disjoint_opposite [IsPreimmersion f]
    (D E : ↥(irreducibleComponents C)) :
    Disjoint (componentImage p f q (false, D)) (componentImage p f q (true, E)) := by
  rw [componentImage_eq, componentImage_eq]
  exact (ambientCopy_disjoint p f q).mono
    (Set.image_subset_range _ _) (Set.image_subset_range _ _)

/-- A mono preserves the original component intersection scheme. -/
def componentIntersectionIso {A B Y W : Scheme.{u}}
    (a : A ⟶ Y) (b : B ⟶ Y) (m : Y ⟶ W) [Mono m] :
    pullback a b ≅ pullback (a ≫ m) (b ≫ m) :=
  (IsPullback.of_isLimit (pullbackIsPullbackOfCompMono a b m)).isoPullback

@[reassoc]
theorem componentIntersectionIso_hom_fst {A B Y W : Scheme.{u}}
    (a : A ⟶ Y) (b : B ⟶ Y) (m : Y ⟶ W) [Mono m] :
    (componentIntersectionIso a b m).hom ≫ pullback.fst (a ≫ m) (b ≫ m) =
      pullback.fst a b :=
  IsPullback.isoPullback_hom_fst _

@[reassoc]
theorem componentIntersectionIso_hom_snd {A B Y W : Scheme.{u}}
    (a : A ⟶ Y) (b : B ⟶ Y) (m : Y ⟶ W) [Mono m] :
    (componentIntersectionIso a b m).hom ≫ pullback.snd (a ≫ m) (b ≫ m) =
      pullback.snd a b :=
  IsPullback.isoPullback_hom_snd _

@[reassoc]
theorem componentIntersectionIso_inv_fst {A B Y W : Scheme.{u}}
    (a : A ⟶ Y) (b : B ⟶ Y) (m : Y ⟶ W) [Mono m] :
    (componentIntersectionIso a b m).inv ≫ pullback.fst a b =
      pullback.fst (a ≫ m) (b ≫ m) :=
  IsPullback.isoPullback_inv_fst _

@[reassoc]
theorem componentIntersectionIso_inv_snd {A B Y W : Scheme.{u}}
    (a : A ⟶ Y) (b : B ⟶ Y) (m : Y ⟶ W) [Mono m] :
    (componentIntersectionIso a b m).inv ≫ pullback.snd a b =
      pullback.snd (a ≫ m) (b ≫ m) :=
  IsPullback.isoPullback_inv_snd _

/-- The actual intersection in the original surface is the intersection in either ambient copy. -/
def sameLabelIntersectionIso [IsClosedImmersion f] (ε : Bool)
    (D E : ↥(irreducibleComponents C)) :
    pullback (componentUnionInclusion C {D} ≫ f) (componentUnionInclusion C {E} ≫ f) ≅
      pullback (componentCopy p f q ε D) (componentCopy p f q ε E) :=
  (componentIntersectionIso (componentUnionInclusion C {D})
    (componentUnionInclusion C {E}) f).symm ≪≫
  componentIntersectionIso (componentUnionInclusion C {D})
    (componentUnionInclusion C {E}) (ambientCopy p f q ε)

@[reassoc]
theorem sameLabelIntersectionIso_hom_fst [IsClosedImmersion f] (ε : Bool)
    (D E : ↥(irreducibleComponents C)) :
    (sameLabelIntersectionIso p f q ε D E).hom ≫
      pullback.fst (componentCopy p f q ε D) (componentCopy p f q ε E) =
        pullback.fst (componentUnionInclusion C {D} ≫ f)
          (componentUnionInclusion C {E} ≫ f) := by
  simp only [sameLabelIntersectionIso, Iso.trans_hom, Iso.symm_hom, componentCopy,
    Category.assoc, componentIntersectionIso_hom_fst, componentIntersectionIso_inv_fst]

@[reassoc]
theorem sameLabelIntersectionIso_hom_snd [IsClosedImmersion f] (ε : Bool)
    (D E : ↥(irreducibleComponents C)) :
    (sameLabelIntersectionIso p f q ε D E).hom ≫
      pullback.snd (componentCopy p f q ε D) (componentCopy p f q ε E) =
        pullback.snd (componentUnionInclusion C {D} ≫ f)
          (componentUnionInclusion C {E} ≫ f) := by
  simp only [sameLabelIntersectionIso, Iso.trans_hom, Iso.symm_hom, componentCopy,
    Category.assoc, componentIntersectionIso_hom_snd, componentIntersectionIso_inv_snd]

/-- The actual scheme-theoretic intersection between opposite labels is empty. -/
instance oppositeLabelIntersection_isEmpty [IsPreimmersion f]
    (D E : ↥(irreducibleComponents C)) :
    IsEmpty (pullback (componentCopy p f q false D) (componentCopy p f q true E) : Scheme.{u}) :=
  Scheme.isEmpty_pullback (componentCopy p f q false D) (componentCopy p f q true E)
    (image_disjoint_opposite p f q D E)

end KltDP.Geometry.SplitAmbientPullbackComponentIntersections

#print axioms KltDP.Geometry.SplitAmbientPullbackComponentIntersections.sameLabelIntersectionIso
#print axioms KltDP.Geometry.SplitAmbientPullbackComponentIntersections.oppositeLabelIntersection_isEmpty
