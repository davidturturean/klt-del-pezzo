import KltDP.Geometry.SchemeIsoEulerTransport
import KltDP.Geometry.Positivity

/-!
# Actual bigness is invariant under a scheme isomorphism

The existing base-linear cohomology comparison for isomorphism pushforward,
together with pushforward being inverse pullback, preserves the original
cohomology dimensions. This descends through the original sheaf skeleton
to Picard classes and commutes with their actual powers. The original
homeomorphism preserves the topological dimension used in `Positivity.IsBig`.

No properness, integrality, finite-dimensionality, section comparison,
triviality, or additional bigness criterion is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.BignessIsomorphism

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- The actual topological dimension used by the original growth definition
is unchanged by the underlying homeomorphism of a scheme isomorphism. -/
theorem natDim_eq (j : Y ⟶ X) [IsIso j] : Positivity.natDim Y = Positivity.natDim X := by
  have h := IsHomeomorph.topologicalKrullDim_eq (asIso j).schemeIsoToHomeo
    (asIso j).schemeIsoToHomeo.isHomeomorph
  unfold Positivity.natDim
  rw [h]

variable (j : Y ⟶ X) [IsIso j] (f : X ⟶ Spec (CommRingCat.of k))

/-- All original cohomology dimensions are preserved by actual pullback,
for the source scalar action induced by the composite structure morphism. -/
theorem cohomologyDimension_pullback (M : X.Modules) (n : ℕ) :
    cohomologyDimension (j ≫ f) ((schemeModulePullback j).obj M) n =
      cohomologyDimension f M n := by
  have h := cohomologyDimension_pushforward_iso (asIso j).symm (j ≫ f) M n
  have hinv : (asIso j).symm.hom ≫ (j ≫ f) = f := by
    change (asIso j).inv ≫ ((asIso j).hom ≫ f) = f
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hinv] at h
  exact (cohomologyDimension_eq_of_iso (j ≫ f)
    ((schemeIsoPushforwardPullbackIso (asIso j).symm).app M) n).symm.trans h

private theorem skeletonHZero_pullback (a : Skeleton X.Modules) :
    Positivity.skeletonHZero (j ≫ f) (schemeModulePullbackClassMap j a) =
      Positivity.skeletonHZero f a := by
  refine Quotient.inductionOn a (fun M => ?_)
  change cohomologyDimension (j ≫ f) ((schemeModulePullback j).obj M) 0 =
    cohomologyDimension f M 0
  exact cohomologyDimension_pullback j f M 0

/-- The original h⁰ function agrees on original Picard pullbacks. -/
theorem picardHZero_pullback (p : X.Pic) :
    Positivity.picardHZero (j ≫ f) (schemePicardPullbackHom j p) =
      Positivity.picardHZero f p := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  change Positivity.skeletonHZero (j ≫ f)
    (schemeModulePullbackClassMap j (p : Skeleton X.Modules)) =
      Positivity.skeletonHZero f (p : Skeleton X.Modules)
  exact skeletonHZero_pullback j f _

/-- Pullback preserves the original section dimensions of every actual
Picard power of the given invertible sheaf. -/
theorem picardHZero_pullback_pow (L : InvertibleSheaf X) (n : ℕ) :
    Positivity.picardHZero (j ≫ f) ((pullbackInvertibleSheaf j L).toPic ^ n) =
      Positivity.picardHZero f (L.toPic ^ n) := by
  rw [← schemePicardPullbackHom_toPic, ← map_pow, picardHZero_pullback]

/-- Pullback along an actual scheme isomorphism preserves and reflects
the unchanged original definition of bigness. -/
theorem isBig_pullback_iff (L : InvertibleSheaf X) :
    Positivity.IsBig (j ≫ f) (pullbackInvertibleSheaf j L) ↔ Positivity.IsBig f L := by
  unfold Positivity.IsBig
  simp only [natDim_eq j, picardHZero_pullback_pow j f]

/-- The same comparison with an explicitly identified original source
structure morphism. -/
theorem isBig_pullback_iff_of_comp_eq (g : Y ⟶ Spec (CommRingCat.of k))
    (h : j ≫ f = g) (L : InvertibleSheaf X) :
    Positivity.IsBig g (pullbackInvertibleSheaf j L) ↔ Positivity.IsBig f L := by
  rw [← h]
  exact isBig_pullback_iff j f L

end KltDP.Geometry.BignessIsomorphism
