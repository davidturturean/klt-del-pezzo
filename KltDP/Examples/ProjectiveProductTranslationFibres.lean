import KltDP.Examples.ProjectiveProductTranslation
import KltDP.Examples.FrobeniusUnaffectedFibers

/-!
# The product translation moves the rulings of `P¹ × P¹`

`τ_a × τ_b` carries the horizontal fibre `y = c` onto `y = c + b` (through `τ_a` on the fibre) and
the vertical fibre `x = c` onto `x = c + a` (through `τ_b`), as morphisms and as supports. In
particular the fibre `y = a^p` of the translated tower's centre is the translate of the fibre
`y = 0` of the origin tower's centre by `τ_a × τ_{a^p}`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.ProjectiveProductTranslationFibres

open KltDP.Geometry KltDP.Geometry.ProjectiveLineTranslation FrobeniusProjectivePoints
  FrobeniusGraphClosed FrobeniusGraphPicardClassZeroFiber FrobeniusUnaffectedFibers
  ProjectiveProductTranslation

variable {k : Type u} [Field k]

/-- **`τ_a × τ_b` carries the horizontal fibre `y = c` onto `y = c + b`.** -/
theorem horizontalFiberMorphism_productTranslation (a b c : k) :
    horizontalFiberMorphism c ≫ productTranslation a b =
      projectiveTranslation a ≫ horizontalFiberMorphism (c + b) := by
  apply pullback.hom_ext
  · have hL : (horizontalFiberMorphism c ≫ productTranslation a b) ≫ firstProjection =
        projectiveTranslation a := by
      rw [Category.assoc, productTranslation_fst, ← Category.assoc, horizontalFiberMorphism_fst,
        Category.id_comp]
    have hR : (projectiveTranslation a ≫ horizontalFiberMorphism (c + b)) ≫ firstProjection =
        projectiveTranslation a := by
      rw [Category.assoc, horizontalFiberMorphism_fst, Category.comp_id]
    rw [hL, hR]
  · have hL : (horizontalFiberMorphism c ≫ productTranslation a b) ≫ secondProjection =
        projectiveSpaceToSpec k 1 ≫ pointMorphism (c + b) := by
      rw [Category.assoc, productTranslation_snd, ← Category.assoc, horizontalFiberMorphism_snd,
        Category.assoc, pointMorphism_projectiveTranslation]
    have hR : (projectiveTranslation a ≫ horizontalFiberMorphism (c + b)) ≫ secondProjection =
        projectiveSpaceToSpec k 1 ≫ pointMorphism (c + b) := by
      rw [Category.assoc, horizontalFiberMorphism_snd, ← Category.assoc,
        projectiveTranslation_over_base]
    rw [hL, hR]

/-- **`τ_a × τ_b` carries the vertical fibre `x = c` onto `x = c + a`.** -/
theorem verticalFiberMorphismAt_productTranslation (a b c : k) :
    verticalFiberMorphismAt c ≫ productTranslation a b =
      projectiveTranslation b ≫ verticalFiberMorphismAt (c + a) := by
  apply pullback.hom_ext
  · have hL : (verticalFiberMorphismAt c ≫ productTranslation a b) ≫ firstProjection =
        projectiveSpaceToSpec k 1 ≫ pointMorphism (c + a) := by
      rw [Category.assoc, productTranslation_fst, ← Category.assoc, verticalFiberMorphismAt_fst,
        Category.assoc, pointMorphism_projectiveTranslation]
    have hR : (projectiveTranslation b ≫ verticalFiberMorphismAt (c + a)) ≫ firstProjection =
        projectiveSpaceToSpec k 1 ≫ pointMorphism (c + a) := by
      rw [Category.assoc, verticalFiberMorphismAt_fst, ← Category.assoc,
        projectiveTranslation_over_base]
    rw [hL, hR]
  · have hL : (verticalFiberMorphismAt c ≫ productTranslation a b) ≫ secondProjection =
        projectiveTranslation b := by
      rw [Category.assoc, productTranslation_snd, ← Category.assoc, verticalFiberMorphismAt_snd,
        Category.id_comp]
    have hR : (projectiveTranslation b ≫ verticalFiberMorphismAt (c + a)) ≫ secondProjection =
        projectiveTranslation b := by
      rw [Category.assoc, verticalFiberMorphismAt_snd, Category.comp_id]
    rw [hL, hR]

/-- The support of `y = c + b` is the image of the support of `y = c`. -/
theorem range_horizontalFiberMorphism_productTranslation (a b c : k) :
    Set.range (horizontalFiberMorphism (c + b)).base =
      (productTranslation a b).base '' Set.range (horizontalFiberMorphism c).base := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    refine ⟨(horizontalFiberMorphism c).base ((projectiveTranslation (-a)).base z),
      ⟨_, rfl⟩, ?_⟩
    have h1 := congrArg (fun f => f.base ((projectiveTranslation (-a)).base z))
      (horizontalFiberMorphism_productTranslation a b c)
    have h2 := congrArg (fun f => f.base z) (projectiveTranslation_comp_neg a)
    change (horizontalFiberMorphism c ≫ productTranslation a b).base
      ((projectiveTranslation (-a)).base z) = _
    rw [horizontalFiberMorphism_productTranslation]
    change (horizontalFiberMorphism (c + b)).base
      ((projectiveTranslation (-a) ≫ projectiveTranslation a).base z) = _
    rw [projectiveTranslation_comp_neg]
    rfl
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(projectiveTranslation a).base z, ?_⟩
    change (projectiveTranslation a ≫ horizontalFiberMorphism (c + b)).base z =
      (horizontalFiberMorphism c ≫ productTranslation a b).base z
    rw [horizontalFiberMorphism_productTranslation]

/-- The support of `x = c + a` is the image of the support of `x = c`. -/
theorem range_verticalFiberMorphismAt_productTranslation (a b c : k) :
    Set.range (verticalFiberMorphismAt (c + a)).base =
      (productTranslation a b).base '' Set.range (verticalFiberMorphismAt c).base := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    refine ⟨(verticalFiberMorphismAt c).base ((projectiveTranslation (-b)).base z),
      ⟨_, rfl⟩, ?_⟩
    change (verticalFiberMorphismAt c ≫ productTranslation a b).base
      ((projectiveTranslation (-b)).base z) = _
    rw [verticalFiberMorphismAt_productTranslation]
    change (verticalFiberMorphismAt (c + a)).base
      ((projectiveTranslation (-b) ≫ projectiveTranslation b).base z) = _
    rw [projectiveTranslation_comp_neg]
    rfl
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(projectiveTranslation b).base z, ?_⟩
    change (projectiveTranslation b ≫ verticalFiberMorphismAt (c + a)).base z =
      (verticalFiberMorphismAt c ≫ productTranslation a b).base z
    rw [verticalFiberMorphismAt_productTranslation]

/-- The fibre `y = a^p` through the translated centre is the translate of the fibre `y = 0`
through the origin. -/
theorem horizontalFiber_zero_productTranslation (p : ℕ) (a : k) :
    horizontalFiberMorphism 0 ≫ productTranslation a (a ^ p) =
      projectiveTranslation a ≫ horizontalFiberMorphism (a ^ p) := by
  rw [horizontalFiberMorphism_productTranslation, zero_add]

end KltDP.Examples.ProjectiveProductTranslationFibres
