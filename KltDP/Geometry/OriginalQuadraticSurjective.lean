import KltDP.Geometry.InvertibleQuadraticAtlas
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Surjectivity of the original quadratic cover

The original quadratic quotient retains the base ring injectively,
as detected by its already constructed constant coordinate. Its actual
finite algebra is integral, so lying over proves surjectivity on spectra.
The original affine base charts and original gluing triangles transfer
this to the unchanged global cover. Empty chart rings are allowed.
No root, field extension, nonsquare coefficient, or cover point is supplied.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
universe u

namespace KltDP.Geometry.QuadraticCover

variable {R : Type u} [CommRing R]

/-- Constants embed in the actual quadratic algebra, including the zero-ring case. -/
theorem algebraMap_injective (s : R) :
    Function.Injective (algebraMap R (CoverAlgebra s)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact fun _ _ _ => Subsingleton.elim _ _
  · intro a b h
    have hc := congrArg (constantCoeff s) h
    simpa only [constantCoeff_algebraMap] using hc

/-- Lying over for the original monic finite algebra supplies every actual affine fiber point. -/
theorem toBase_surjective (s : R) : Function.Surjective (toBase s).base := by
  letI : Module.Finite R (CoverAlgebra s) := finite s
  have hint : (algebraMap R (CoverAlgebra s)).IsIntegral := Algebra.IsIntegral.isIntegral
  exact hint.specComap_surjective (algebraMap_injective s)

end KltDP.Geometry.QuadraticCover

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open QuadraticCover TransitionUnitGluing

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- The actual original chart triangles prove that the global cover is surjective. -/
theorem morphism_surjective : Function.Surjective D.morphism.base := by
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show x ∈ ⨆ i, D.opens i by rw [D.covers]; trivial)
  have hr : x ∈ Set.range (D.affine i).fromSpec.base := by
    rw [IsAffineOpen.range_fromSpec]
    exact hi
  obtain ⟨z, hz⟩ := hr
  obtain ⟨y, hy⟩ := toBase_surjective (res X (le_refl (D.opens i)) (D.sections i)) z
  refine ⟨(D.chartι i).base y, ?_⟩
  change (D.chartι i ≫ D.morphism).base y = x
  rw [D.chartι_morphism]
  change (D.affine i).fromSpec.base
    ((toBase (res X (le_refl (D.opens i)) (D.sections i))).base y) = x
  rw [hy, hz]

theorem morphism_isSurjective : AlgebraicGeometry.Surjective D.morphism :=
  ⟨D.morphism_surjective⟩

end KltDP.Geometry.QuadraticCoverAtlas.Data

namespace KltDP.Geometry.InvertibleQuadraticAtlas

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [X.IsSeparated]

local instance originalQuadraticSurjectiveMonoidal : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

/-- The unchanged cover of any actual square-root section maps onto its original base. -/
theorem fromSquareRoot_isSurjective (L : InvertibleSheaf X) (N : X.Modules)
    (e : L.obj ⊗ L.obj ≅ N) (b : N.val.obj (op (⊤ : X.Opens))) :
    AlgebraicGeometry.Surjective (fromSquareRoot X L N e b).morphism :=
  (fromSquareRoot X L N e b).morphism_isSurjective

end KltDP.Geometry.InvertibleQuadraticAtlas

#print axioms KltDP.Geometry.InvertibleQuadraticAtlas.fromSquareRoot_isSurjective
