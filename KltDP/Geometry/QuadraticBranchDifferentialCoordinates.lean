import KltDP.Geometry.QuadraticAbsoluteDifferentialExtension
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Actual dual coordinates for a branch-normalized quadratic differential frame

A given basis of the original base differentials beginning with d(s)
produces two actual linear functionals on the original cover differentials.
They take dt and the image of the second base vector to (1,0) and (0,1).
No cover basis or differential isomorphism is assumed. Existence of the
normalized base basis from actual smooth branch geometry remains separate.
-/

noncomputable section

universe u

namespace KltDP.Geometry.QuadraticCover

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R]

/-- An original base coordinate, followed by the actual coefficient map. -/
def baseDifferentialCoordinate (s : R)
    (b : Basis (Fin 2) R (KaehlerDifferential k R)) (i : Fin 2) :
    KaehlerDifferential k R →ₗ[R] CoverAlgebra s :=
  (Algebra.ofId R (CoverAlgebra s)).toLinearMap.comp (b.coord i)

/-- The coefficient derivation 2t times the first coordinate extends
with actual root derivative one. -/
def branchDifferentialCoordinateZero (s : R)
    (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (hb : b 0 = KaehlerDifferential.D k R s) :
    KaehlerDifferential k (CoverAlgebra s) →ₗ[CoverAlgebra s] CoverAlgebra s :=
  absoluteDifferentialExtension k R s ((2 * root s) • baseDifferentialCoordinate k R s b 0)
    1 (by rw [← hb]; simp [baseDifferentialCoordinate])

/-- The second coefficient coordinate extends with actual root
derivative zero. -/
def branchDifferentialCoordinateOne (s : R)
    (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (hb : b 0 = KaehlerDifferential.D k R s) :
    KaehlerDifferential k (CoverAlgebra s) →ₗ[CoverAlgebra s] CoverAlgebra s :=
  absoluteDifferentialExtension k R s (baseDifferentialCoordinate k R s b 1)
    0 (by rw [← hb]; simp [baseDifferentialCoordinate])

@[simp]
theorem branchDifferentialCoordinateZero_D_root (s : R)
    (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (hb : b 0 = KaehlerDifferential.D k R s) :
    branchDifferentialCoordinateZero k R s b hb
      (KaehlerDifferential.D k (CoverAlgebra s) (root s)) = 1 :=
  absoluteDifferentialExtension_D_root _ _ _ _ _ _

@[simp]
theorem branchDifferentialCoordinateOne_D_root (s : R)
    (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (hb : b 0 = KaehlerDifferential.D k R s) :
    branchDifferentialCoordinateOne k R s b hb
      (KaehlerDifferential.D k (CoverAlgebra s) (root s)) = 0 :=
  absoluteDifferentialExtension_D_root _ _ _ _ _ _

@[simp]
theorem branchDifferentialCoordinateZero_map_one (s : R)
    (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (hb : b 0 = KaehlerDifferential.D k R s) :
    branchDifferentialCoordinateZero k R s b hb
      (KaehlerDifferential.map k k R (CoverAlgebra s) (b 1)) = 0 := by
  rw [branchDifferentialCoordinateZero, absoluteDifferentialExtension_map]
  simp [baseDifferentialCoordinate]

@[simp]
theorem branchDifferentialCoordinateOne_map_one (s : R)
    (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (hb : b 0 = KaehlerDifferential.D k R s) :
    branchDifferentialCoordinateOne k R s b hb
      (KaehlerDifferential.map k k R (CoverAlgebra s) (b 1)) = 1 := by
  rw [branchDifferentialCoordinateOne, absoluteDifferentialExtension_map]
  simp [baseDifferentialCoordinate]

/-- Both actual dual coordinates as a single original-module map. -/
def branchDifferentialCoordinates (s : R)
    (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (hb : b 0 = KaehlerDifferential.D k R s) :
    KaehlerDifferential k (CoverAlgebra s) →ₗ[CoverAlgebra s]
      (CoverAlgebra s × CoverAlgebra s) :=
  (branchDifferentialCoordinateZero k R s b hb).prod
    (branchDifferentialCoordinateOne k R s b hb)

@[simp]
theorem branchDifferentialCoordinates_D_root (s : R)
    (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (hb : b 0 = KaehlerDifferential.D k R s) :
    branchDifferentialCoordinates k R s b hb
      (KaehlerDifferential.D k (CoverAlgebra s) (root s)) = (1, 0) := by
  ext <;> simp [branchDifferentialCoordinates]

@[simp]
theorem branchDifferentialCoordinates_map_one (s : R)
    (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (hb : b 0 = KaehlerDifferential.D k R s) :
    branchDifferentialCoordinates k R s b hb
      (KaehlerDifferential.map k k R (CoverAlgebra s) (b 1)) = (0, 1) := by
  ext <;> simp [branchDifferentialCoordinates]

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.branchDifferentialCoordinates_map_one
