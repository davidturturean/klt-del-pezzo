import KltDP.Geometry.TransitionUnitGauge
import KltDP.Geometry.InvertibleSheafPicard

/-!
# Actual Picard classes of covering transition cocycles

The previously constructed invertible sheaf determines a class in the
scheme's actual tensor Picard group. Gauge-equivalent transition data give
equal classes by the constructed module-sheaf isomorphism. This is the
same-cover gauge step; no refinement quotient or classification theorem is
asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
  (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (hg : IsCocycle X U g)
  (hU : (⨆ i, U i) = ⊤)

/-- The actual tensor Picard class of the constructed cocycle-glued sheaf. -/
def picardClass : X.Pic :=
  (invertibleSheaf X U g hg hU).toPic

/-- The underlying Picard class retains the original matching-family sheaf. -/
@[simp]
theorem picardClass_val :
    letI := Scheme.Modules.monoidalCategory X
    (picardClass X U g hg hU : Skeleton X.Modules) =
      toSkeleton (moduleSheaf X U g) :=
  InvertibleSheaf.toPic_val (invertibleSheaf X U g hg hU)

/-- The actual gauge isomorphism identifies the tensor Picard classes. -/
theorem picardClass_eq_of_gauge
    (h : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (hh : IsCocycle X U h)
    (b : ∀ i : ι, Γ(X, U i)ˣ) (hb : IsGauge X U g h b) :
    picardClass X U g hg hU = picardClass X U h hh hU := by
  letI := Scheme.Modules.monoidalCategory X
  apply Units.ext
  rw [picardClass_val, picardClass_val]
  exact Quotient.sound ⟨gaugeIso X U g h b hb⟩

end KltDP.Geometry.TransitionUnitGluing
