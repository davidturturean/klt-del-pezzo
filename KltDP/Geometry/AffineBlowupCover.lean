import KltDP.Geometry.AffineBlowup
import KltDP.Compatibility.ProjGeneratedCover
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!
# The actual degree-one affine cover of a Rees Proj

An actual generating family of an ideal generates its Rees algebra in
degree one. The bounded upstream Proj proof then gives the irrelevant
ideal inclusion and the actual affine chart cover. Coverage is derived
from ideal generation and is not an additional input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open scoped DirectSum

namespace KltDP.Geometry.AffineBlowup

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Actual generators of `I` give generators of the polynomial Rees
subalgebra, by the pinned degree-one generation theorem. -/
theorem adjoin_monomial_generators {ι : Type*} (f : ι → I)
    (hf : Ideal.span (Set.range (fun i => (f i : R))) = I) :
    Algebra.adjoin R (Set.range (fun i => monomial 1 (f i : R))) = reesAlgebra I := by
  have hmap : Submodule.map (monomial 1 : R →ₗ[R] R[X]) I =
      Submodule.span R (Set.range (fun i => monomial 1 (f i : R))) := by
    calc
      _ = Submodule.map (monomial 1 : R →ₗ[R] R[X])
          (Submodule.span R (Set.range (fun i => (f i : R)))) :=
        congrArg (Submodule.map (monomial 1 : R →ₗ[R] R[X])) hf.symm
      _ = _ := by rw [Submodule.map_span, ← Set.range_comp']
  have h := adjoin_monomial_eq_reesAlgebra (I := I)
  rw [hmap, Algebra.adjoin_span] at h
  exact h

/-- The actual lifted degree-one elements generate the Rees algebra
itself, as opposed to merely its image in the polynomial ring. -/
theorem adjoin_degreeOne_generators {ι : Type*} (f : ι → I)
    (hf : Ideal.span (Set.range (fun i => (f i : R))) = I) :
    Algebra.adjoin R (Set.range (fun i => degreeOne I (f i))) = ⊤ := by
  apply Subalgebra.map_injective
    (f := (reesAlgebra I).val) (fun _ _ h => Subtype.ext h)
  rw [← Algebra.adjoin_image, ← Set.range_comp', Algebra.map_top,
    Subalgebra.range_val]
  exact adjoin_monomial_generators I f hf

/-- Changing the base from `R` to the actual degree-zero part preserves
the proved generation by the same homogeneous elements. -/
theorem adjoin_degreeOne_generators_over_zero {ι : Type*} (f : ι → I)
    (hf : Ideal.span (Set.range (fun i => (f i : R))) = I) :
    Algebra.adjoin (ReesGrading.component I 0)
      (Set.range (fun i => degreeOne I (f i))) = ⊤ := by
  letI : IsScalarTower R (ReesGrading.component I 0) (reesAlgebra I) :=
    IsScalarTower.of_algebraMap_eq' (R := R)
      (S := ReesGrading.component I 0) (A := reesAlgebra I) (by ext r; rfl)
  have hle : Algebra.adjoin R (Set.range (fun i => degreeOne I (f i))) ≤
      (Algebra.adjoin (ReesGrading.component I 0)
        (Set.range (fun i => degreeOne I (f i)))).restrictScalars R := by
    apply Algebra.adjoin_le (R := R) (A := reesAlgebra I)
      (S := (Algebra.adjoin (ReesGrading.component I 0)
        (Set.range (fun i => degreeOne I (f i)))).restrictScalars R)
    simp only [Subalgebra.coe_restrictScalars]
    exact Algebra.subset_adjoin (R := ReesGrading.component I 0)
  apply top_le_iff.mp
  intro x _
  apply hle
  rw [adjoin_degreeOne_generators I f hf]
  trivial

/-- Actual generators of the center ideal generate enough of the Rees
irrelevant ideal to cover its Proj. -/
theorem irrelevant_le_span_generators {ι : Type*} (f : ι → I)
    (hf : Ideal.span (Set.range (fun i => (f i : R))) = I) :
    (HomogeneousIdeal.irrelevant (ReesGrading.component I)).toIdeal ≤
      Ideal.span (Set.range (fun i => degreeOne I (f i))) :=
  ProjGeneratedCover.irrelevant_le_span_of_adjoin_eq_top
    (ReesGrading.component I) (fun i => degreeOne I (f i))
    (fun i => ⟨1, degreeOne_mem I (f i)⟩)
    (adjoin_degreeOne_generators_over_zero I f hf)

/-- The basic opens from an actual ideal generating family cover. -/
theorem iSup_chartOpen_generators {ι : Type*} (f : ι → I)
    (hf : Ideal.span (Set.range (fun i => (f i : R))) = I) :
    (⨆ i, chartOpen I (f i)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (ReesGrading.component I)
    (fun i => degreeOne I (f i)) (irrelevant_le_span_generators I f hf)

/-- The actual affine cover indexed by a generating family of the
center ideal. In particular, a finite family gives a finite cover. -/
def generatingAffineCover {ι : Type*} (f : ι → I)
    (hf : Ideal.span (Set.range (fun i => (f i : R))) = I) :
    (scheme I).AffineOpenCover :=
  Proj.openCoverOfISupEqTop (ReesGrading.component I)
    (fun i => degreeOne I (f i)) (m := fun _ => 1)
    (fun i => degreeOne_mem I (f i)) (fun _ => by norm_num)
    (irrelevant_le_span_generators I f hf)

/-- The affine cover maps are precisely the previously constructed
actual chart open immersions. -/
theorem generatingAffineCover_map {ι : Type*} (f : ι → I)
    (hf : Ideal.span (Set.range (fun i => (f i : R))) = I) (i : ι) :
    (generatingAffineCover I f hf).map i = chartι I (f i) := rfl

/-- The full family of elements of an ideal generates that ideal. -/
theorem span_all_elements : Ideal.span (Set.range (fun a : I => (a : R))) = I := by
  have hrange : Set.range (fun a : I => (a : R)) = (I : Set R) := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      exact b.property
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [hrange, Ideal.span_eq]

/-- The full degree-one family covers without any generating-family
or coverage hypothesis. -/
theorem iSup_chartOpen : (⨆ a : I, chartOpen I a) = ⊤ :=
  iSup_chartOpen_generators I (fun a => a) (span_all_elements I)

/-- The actual affine cover by all degree-one Rees charts. -/
def degreeOneAffineCover : (scheme I).AffineOpenCover :=
  generatingAffineCover I (fun a => a) (span_all_elements I)

end KltDP.Geometry.AffineBlowup
