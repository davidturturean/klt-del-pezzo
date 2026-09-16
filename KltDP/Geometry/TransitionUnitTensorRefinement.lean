import KltDP.Geometry.TransitionUnitTensor
import KltDP.Geometry.TransitionUnitRefinement

/-!
# Tensor products for transition data on different open covers

Two actual open covers have their literal intersection cover. The
original units restrict along its two projection maps. Refinement of
the two actual module sheaves, followed by the proved tensor-product
isomorphism on that common cover, gives the tensor-product cocycle and
its actual Picard-class formula.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

variable (X : Scheme.{u}) {ι κ : Type u} (U : ι → X.Opens) (V : κ → X.Opens)

/-- The actual common cover formed by intersections of the two original atlases. -/
def tensorCover (p : ι × κ) : X.Opens := U p.1 ⊓ V p.2

theorem tensorCover_cover (hU : (⨆ i, U i) = ⊤) (hV : (⨆ j, V j) = ⊤) :
    (⨆ p, tensorCover X U V p) = ⊤ := by
  apply top_unique
  intro x hx
  have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
  have hxV : x ∈ ⨆ j, V j := by rw [hV]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxV
  exact Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩

/-- The left transition units, restricted through the actual first projection. -/
def leftTensorUnits (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) :
    ∀ p q, Γ(X, tensorCover X U V p ⊓ tensorCover X U V q)ˣ :=
  refinedUnits X U g (tensorCover X U V) Prod.fst (fun _ => inf_le_left)

/-- The right transition units, restricted through the actual second projection. -/
def rightTensorUnits (h : ∀ i j : κ, Γ(X, V i ⊓ V j)ˣ) :
    ∀ p q, Γ(X, tensorCover X U V p ⊓ tensorCover X U V q)ˣ :=
  refinedUnits X V h (tensorCover X U V) Prod.snd (fun _ => inf_le_right)

theorem leftTensorUnits_isCocycle
    (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (hg : IsCocycle X U g) :
    IsCocycle X (tensorCover X U V) (leftTensorUnits X U V g) :=
  refinedUnits_isCocycle X U g (tensorCover X U V) Prod.fst (fun _ => inf_le_left) hg

theorem rightTensorUnits_isCocycle
    (h : ∀ i j : κ, Γ(X, V i ⊓ V j)ˣ) (hh : IsCocycle X V h) :
    IsCocycle X (tensorCover X U V) (rightTensorUnits X U V h) :=
  refinedUnits_isCocycle X V h (tensorCover X U V) Prod.snd (fun _ => inf_le_right) hh

/-- The product of the two original unit families on their literal common refinement. -/
def jointProductUnits
    (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (h : ∀ i j : κ, Γ(X, V i ⊓ V j)ˣ) :
    ∀ p q, Γ(X, tensorCover X U V p ⊓ tensorCover X U V q)ˣ :=
  productUnits X (tensorCover X U V) (leftTensorUnits X U V g) (rightTensorUnits X U V h)

theorem jointProductUnits_isCocycle
    (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (h : ∀ i j : κ, Γ(X, V i ⊓ V j)ˣ)
    (hg : IsCocycle X U g) (hh : IsCocycle X V h) :
    IsCocycle X (tensorCover X U V) (jointProductUnits X U V g h) :=
  productUnits_isCocycle X (tensorCover X U V)
    (leftTensorUnits X U V g) (rightTensorUnits X U V h)
    (leftTensorUnits_isCocycle X U V g hg) (rightTensorUnits_isCocycle X U V h hh)

/-- Actual tensor products have the product of the restricted transition cocycles. -/
def tensorRefinementIso
    (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (h : ∀ i j : κ, Γ(X, V i ⊓ V j)ˣ)
    (hg : IsCocycle X U g) (hh : IsCocycle X V h)
    (hU : (⨆ i, U i) = ⊤) (hV : (⨆ j, V j) = ⊤) :
    letI := Scheme.Modules.monoidalCategory X
    moduleSheaf X U g ⊗ moduleSheaf X V h ≅
      moduleSheaf X (tensorCover X U V) (jointProductUnits X U V g h) := by
  letI := Scheme.Modules.monoidalCategory X
  let hC := tensorCover_cover X U V hU hV
  exact (_root_.CategoryTheory.MonoidalCategory.tensorIso
    (refinementIso X U g (tensorCover X U V) Prod.fst (fun _ => inf_le_left) hg hC)
    (refinementIso X V h (tensorCover X U V) Prod.snd (fun _ => inf_le_right) hh hC)) ≪≫
    tensorIso X (tensorCover X U V) (leftTensorUnits X U V g) (rightTensorUnits X U V h)
      (leftTensorUnits_isCocycle X U V g hg) (rightTensorUnits_isCocycle X U V h hh) hC

/-- Multiplicativity in the actual Picard group holds for independently chosen atlases. -/
theorem picardClass_jointProductUnits
    (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (h : ∀ i j : κ, Γ(X, V i ⊓ V j)ˣ)
    (hg : IsCocycle X U g) (hh : IsCocycle X V h)
    (hU : (⨆ i, U i) = ⊤) (hV : (⨆ j, V j) = ⊤) :
    picardClass X (tensorCover X U V) (jointProductUnits X U V g h)
        (jointProductUnits_isCocycle X U V g h hg hh) (tensorCover_cover X U V hU hV) =
      picardClass X U g hg hU * picardClass X V h hh hV := by
  letI := Scheme.Modules.monoidalCategory X
  apply Units.ext
  change (picardClass X (tensorCover X U V) (jointProductUnits X U V g h)
      (jointProductUnits_isCocycle X U V g h hg hh) (tensorCover_cover X U V hU hV) :
        Skeleton X.Modules) =
    (picardClass X U g hg hU : Skeleton X.Modules) *
      (picardClass X V h hh hV : Skeleton X.Modules)
  rw [picardClass_val, picardClass_val, picardClass_val, ← Skeleton.toSkeleton_tensorObj]
  exact Quotient.sound ⟨(tensorRefinementIso X U V g h hg hh hU hV).symm⟩

end KltDP.Geometry.TransitionUnitGluing
