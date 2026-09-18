import KltDP.Examples.ProjectiveLineProductRationality

/-!
# Rationality from an actual product neighborhood of the ruling

The product chart and the isomorphism of its original base with P1 are
explicit geometric inputs. The original chart maps to the existing
projective product by a pullback of the base open immersion. Both its
images are dense, so the existing partial-isomorphism API proves
birationality to the actual affine plane indexed by Fin 2.

This adapter does not construct the product neighborhood from the ruled
surface conditions and does not introduce any literature assumption.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
universe u

namespace KltDP.Geometry.RuledProductChartRationality

open KltDP.Examples FrobeniusProjectivePoints FrobeniusStageZeroProjective

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (V : NormalProjectiveSurface k) {C : Scheme.{u}}
variable (c : C ⟶ Spec (CommRingCat.of k)) (q : V.toScheme ⟶ C)
variable (hq : q ≫ c = V.structureMorphism)
variable (U : C.Opens) (hU : Nonempty U.toScheme)
variable (e : (q ⁻¹ᵁ U).toScheme ≅
  pullback (projectiveSpaceToSpec k 1) (U.ι ≫ c))
variable (he : e.hom ≫ pullback.snd (projectiveSpaceToSpec k 1) (U.ι ≫ c) =
  q ∣_ U)
variable (eC : C ≅ projectiveSpace k 1)
variable (heC : eC.hom ≫ projectiveSpaceToSpec k 1 = c)

include hq hU he heC in
/-- The supplied product neighborhood gives birationality over the original
field to the existing projective product, with no global bundle choice. -/
theorem birationalOver_projectiveProduct :
    Scheme.BirationalOver V.structureMorphism
      (projectiveProductSurface (k := k)).structureMorphism := by
  let sectionU : U.toScheme ⟶
      pullback (projectiveSpaceToSpec k 1) (U.ι ≫ c) :=
    pullback.lift ((U.ι ≫ c) ≫ pointMorphism (0 : k)) (𝟙 U.toScheme)
      (by simp only [Category.assoc, pointMorphism_over_base,
        Category.comp_id, Category.id_comp])
  letI : Nonempty (q ⁻¹ᵁ U).toScheme :=
    ⟨(sectionU ≫ e.inv).base (Classical.choice hU)⟩
  let i : pullback (projectiveSpaceToSpec k 1) (U.ι ≫ c) ⟶
      projectiveProduct k :=
    pullback.map (projectiveSpaceToSpec k 1) (U.ι ≫ c)
      (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)
      (𝟙 _) (U.ι ≫ eC.hom) (𝟙 _)
      (by simp only [Category.comp_id, Category.id_comp])
      (by simp only [Category.comp_id, Category.assoc, heC])
  letI : IsOpenImmersion i := by
    dsimp only [i]
    infer_instance
  have hifst : i ≫ pullback.fst (projectiveSpaceToSpec k 1)
      (projectiveSpaceToSpec k 1) =
      pullback.fst (projectiveSpaceToSpec k 1) (U.ι ≫ c) := by
    dsimp only [i]
    simpa only [Category.comp_id] using pullback.lift_fst _ _ _
  have hi : i ≫ projectiveProductToSpec =
      pullback.snd (projectiveSpaceToSpec k 1) (U.ι ≫ c) ≫ (U.ι ≫ c) := by
    change i ≫ (pullback.fst _ _ ≫ projectiveSpaceToSpec k 1) = _
    rw [← Category.assoc, hifst]
    exact pullback.condition
  let j : (q ⁻¹ᵁ U).toScheme ⟶ projectiveProduct k := e.hom ≫ i
  letI : IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  letI : IsIntegral (projectiveProduct k) :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  letI : IsDominant j :=
    ⟨j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  letI : IsDominant (q ⁻¹ᵁ U).ι :=
    ⟨(q ⁻¹ᵁ U).ι.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hj : j ≫ projectiveProductToSpec =
      (q ⁻¹ᵁ U).ι ≫ V.structureMorphism := by
    calc
      j ≫ projectiveProductToSpec = e.hom ≫
          (pullback.snd (projectiveSpaceToSpec k 1) (U.ι ≫ c) ≫ (U.ι ≫ c)) := by
        dsimp only [j]
        rw [Category.assoc, hi]
      _ = (e.hom ≫ pullback.snd (projectiveSpaceToSpec k 1) (U.ι ≫ c)) ≫
          U.ι ≫ c := by simp only [Category.assoc]
      _ = (q ∣_ U) ≫ U.ι ≫ c := by rw [he]
      _ = (q ⁻¹ᵁ U).ι ≫ V.structureMorphism := by
        rw [morphismRestrict_ι_assoc, hq]
  have hleft := Scheme.Hom.birationalOver (q ⁻¹ᵁ U).ι V.structureMorphism
    ((q ⁻¹ᵁ U).ι ≫ V.structureMorphism) rfl
  have hright := Scheme.Hom.birationalOver j projectiveProductToSpec
    ((q ⁻¹ᵁ U).ι ≫ V.structureMorphism) hj
  exact hleft.symm.trans hright

include hq hU he heC in
/-- The original surface is birational over its field to exactly affine
two-space, from the supplied actual chart and original-base isomorphism. -/
theorem birationalOver_affinePlane :
    Scheme.BirationalOver V.structureMorphism
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) :=
  (birationalOver_projectiveProduct V c q hq U hU e he eC heC).trans
    ProjectiveLineProductRationality.birationalOver_affinePlane

end KltDP.Geometry.RuledProductChartRationality

#check @KltDP.Geometry.RuledProductChartRationality.birationalOver_projectiveProduct
#check @KltDP.Geometry.RuledProductChartRationality.birationalOver_affinePlane
#print axioms KltDP.Geometry.RuledProductChartRationality.birationalOver_affinePlane
