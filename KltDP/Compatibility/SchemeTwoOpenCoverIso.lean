import KltDP.Compatibility.SchemeTwoOpenGluing

/-!
# Comparison of two-open gluing with an actual covered scheme

Pinned `Scheme.Cover.glueMorphisms` constructs the inverse to the map from
two-open gluing whenever the two given open immersions cover the target
and their given overlap is the actual pullback. Coverage and the pullback
property are explicit hypotheses of this general gluing adapter; no inverse
map, isomorphism, or desired descent conclusion is part of the input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.SchemeTwoOpenGluing

variable {A B W X : Scheme.{u}} (f : W ⟶ A) (g : W ⟶ B)
    [IsOpenImmersion f] [IsOpenImmersion g]
    (a : A ⟶ X) (b : B ⟶ X) [IsOpenImmersion a] [IsOpenImmersion b]
    (H : IsPullback f g a b)
    (hcover : ∀ x : X, (∃ y : A, a.base y = x) ∨ (∃ y : B, b.base y = x))

omit [IsOpenImmersion g] [IsOpenImmersion a] in
/-- For actual open immersions, the commuting square is a pullback when
the given overlap has exactly the inverse-image open range. -/
theorem isPullback_of_range (hcomm : f ≫ a = g ≫ b)
    (hrange : Set.range f.base = a.base ⁻¹' Set.range b.base) :
    IsPullback f g a b := by
  have heq : Set.range f.base = Set.range (pullback.fst a b).base := by
    rw [IsOpenImmersion.range_pullback_fst_of_right]
    exact hrange
  let e := IsOpenImmersion.isoOfRangeEq f (pullback.fst a b) heq
  refine IsPullback.of_iso_pullback ⟨hcomm⟩ e
    (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _) ?_
  apply (cancel_mono b).mp
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  rw [IsOpenImmersion.isoOfRangeEq_hom_fac]
  exact hcomm

def targetCoverMap : ∀ i : Side.{u}, piece (A := A) (B := B) i ⟶ X
  | .left => a
  | .right => b

/-- The two actual open immersions form an actual cover of the target. -/
def targetCover : X.OpenCover :=
  Scheme.Cover.mkOfCovers Side (piece (A := A) (B := B)) (targetCoverMap a b)
    (fun x => by
      rcases hcover x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨.left, y, hy⟩
      · exact ⟨.right, y, hy⟩)
    (fun i => by cases i <;> dsimp [targetCoverMap] <;> infer_instance)

def coverMapToGlued : ∀ i : Side.{u}, piece (A := A) (B := B) i ⟶ glued f g
  | .left => leftι f g
  | .right => rightι f g

include H in
omit [IsOpenImmersion a] [IsOpenImmersion b] in
/-- Compatibility for the actual pullback of the two target inclusions. -/
theorem pullback_coverMap_compatibility :
    pullback.fst a b ≫ leftι f g = pullback.snd a b ≫ rightι f g := by
  rw [← IsPullback.isoPullback_inv_fst H, ← IsPullback.isoPullback_inv_snd H,
    Category.assoc, Category.assoc, overlap_condition]

include H in
theorem coverMapToGlued_compatibility (i j : Side.{u}) :
    pullback.fst ((targetCover a b hcover).map i) ((targetCover a b hcover).map j) ≫
        coverMapToGlued f g i =
      pullback.snd _ _ ≫ coverMapToGlued f g j := by
  cases i <;> cases j
  · change pullback.fst a a ≫ leftι f g = pullback.snd a a ≫ leftι f g
    exact congrArg (· ≫ leftι f g)
      ((cancel_mono a).mp (pullback.condition (f := a) (g := a)))
  · exact pullback_coverMap_compatibility f g a b H
  · change pullback.fst b a ≫ rightι f g = pullback.snd b a ≫ leftι f g
    rw [← IsPullback.isoPullback_inv_fst H.flip, ← IsPullback.isoPullback_inv_snd H.flip,
      Category.assoc, Category.assoc, ← overlap_condition]
  · change pullback.fst b b ≫ rightι f g = pullback.snd b b ≫ rightι f g
    exact congrArg (· ≫ rightι f g)
      ((cancel_mono b).mp (pullback.condition (f := b) (g := b)))

/-- The inverse map is obtained by actual descent of the two gluing inclusions. -/
def fromTarget : X ⟶ glued f g :=
  (targetCover a b hcover).glueMorphisms (coverMapToGlued f g)
    (coverMapToGlued_compatibility f g a b H hcover)

@[simp] theorem a_fromTarget :
    a ≫ fromTarget f g a b H hcover = leftι f g :=
  (targetCover a b hcover).ι_glueMorphisms _ _ .left

@[simp] theorem b_fromTarget :
    b ≫ fromTarget f g a b H hcover = rightι f g :=
  (targetCover a b hcover).ι_glueMorphisms _ _ .right

/-- The actual two-open gluing is isomorphic to the scheme covered by
these same pieces and this same scheme-theoretic overlap. -/
def isoOfCover : glued f g ≅ X where
  hom := toTarget f g a b H.w
  inv := fromTarget f g a b H hcover
  hom_inv_id := by
    apply hom_ext f g
    · rw [← Category.assoc, leftι_toTarget, a_fromTarget, Category.comp_id]
    · rw [← Category.assoc, rightι_toTarget, b_fromTarget, Category.comp_id]
  inv_hom_id := by
    apply (targetCover a b hcover).hom_ext
    intro i
    cases i
    · change a ≫ (fromTarget f g a b H hcover ≫ toTarget f g a b H.w) = a ≫ 𝟙 X
      rw [← Category.assoc, a_fromTarget, leftι_toTarget, Category.comp_id]
    · change b ≫ (fromTarget f g a b H hcover ≫ toTarget f g a b H.w) = b ≫ 𝟙 X
      rw [← Category.assoc, b_fromTarget, rightι_toTarget, Category.comp_id]

@[simp] theorem isoOfCover_hom :
    (isoOfCover f g a b H hcover).hom = toTarget f g a b H.w := rfl

end KltDP.SchemeTwoOpenGluing
