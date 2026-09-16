import KltDP.Geometry.AmpleOfAffineNonvanishingCover
import KltDP.Geometry.InvertibleSectionNonvanishingPullback
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine pullback of an original affine nonvanishing-section cover -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.AffinePullbackOfNonvanishingCoverAmple

open InvertibleSectionNonvanishingOpen

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f] (L : InvertibleSheaf X)

/-- The actual pulled sections along an affine morphism retain an affine
nonvanishing cover and prove Serre ampleness on the original QCQS source. -/
theorem isAmple_pullback_of_finite_cover
    (hY : IsCompact (Set.univ : Set Y))
    (hYqs : IsQuasiSeparated (Set.univ : Set Y))
    {I : Type u} [Finite I] (s : I → L.obj.sections)
    (ha : ∀ i, IsAffineOpen (nonvanishingOpen X L (s i)))
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, nonvanishingOpen X L (s i)) :
    AmpleSerre.IsAmple (pullbackInvertibleSheaf f L) := by
  apply AmpleOfAffineNonvanishingCover.isAmple_of_finite_cover
    (pullbackInvertibleSheaf f L) hY hYqs
    (fun i => InvertibleSheafSectionPowersPullback.pullbackSection f L.obj (s i))
  · intro i
    rw [InvertibleSectionNonvanishingPullback.nonvanishingOpen_pullback]
    exact (ha i).preimage f
  · intro y hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
      (hcover (show f.base y ∈ (⊤ : X.Opens) from trivial))
    apply Opens.mem_iSup.mpr
    exact ⟨i, by
      rw [InvertibleSectionNonvanishingPullback.nonvanishingOpen_pullback]
      exact hi⟩

end KltDP.Geometry.AffinePullbackOfNonvanishingCoverAmple
