import KltDP.Geometry.QuadraticAbsoluteDerivation
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Dual absolute differential coordinates on the original quadratic cover

The actual derivation extension gives a linear functional on the actual
absolute Kaehler module. Its composition with the original coefficient
differential map is the given base functional; its value on dt is the
specified derivative of the original root. These two identities supply
the dual-coordinate check for the subsequent normalized differential basis.
-/

noncomputable section

universe u

namespace KltDP.Geometry.QuadraticCover

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R]

/-- Extend an actual base differential functional across the original
quadratic relation. -/
def absoluteDifferentialExtension (s : R)
    (ell : KaehlerDifferential k R →ₗ[R] CoverAlgebra s) (v : CoverAlgebra s)
    (h : ell (KaehlerDifferential.D k R s) = (2 * root s) * v) :
    KaehlerDifferential k (CoverAlgebra s) →ₗ[CoverAlgebra s] CoverAlgebra s :=
  Derivation.liftKaehlerDifferential
    (absoluteDerivation k R s (ell.compDer (KaehlerDifferential.D k R)) v h)

/-- The original root differential has the required actual coordinate. -/
@[simp]
theorem absoluteDifferentialExtension_D_root (s : R)
    (ell : KaehlerDifferential k R →ₗ[R] CoverAlgebra s) (v : CoverAlgebra s)
    (h : ell (KaehlerDifferential.D k R s) = (2 * root s) * v) :
    absoluteDifferentialExtension k R s ell v h
      (KaehlerDifferential.D k (CoverAlgebra s) (root s)) = v := by
  rw [absoluteDifferentialExtension, Derivation.liftKaehlerDifferential_comp_D,
    absoluteDerivation_root]

/-- The original coefficient differential map retains the original
functional, as an equality of actual linear maps. -/
theorem absoluteDifferentialExtension_comp_map (s : R)
    (ell : KaehlerDifferential k R →ₗ[R] CoverAlgebra s) (v : CoverAlgebra s)
    (h : ell (KaehlerDifferential.D k R s) = (2 * root s) * v) :
    ((absoluteDifferentialExtension k R s ell v h).restrictScalars R).comp
      (KaehlerDifferential.map k k R (CoverAlgebra s)) = ell := by
  apply Derivation.liftKaehlerDifferential_unique
  apply Derivation.ext
  intro a
  change absoluteDifferentialExtension k R s ell v h
      (KaehlerDifferential.map k k R (CoverAlgebra s) (KaehlerDifferential.D k R a)) =
    ell (KaehlerDifferential.D k R a)
  rw [KaehlerDifferential.map_D, absoluteDifferentialExtension,
    Derivation.liftKaehlerDifferential_comp_D]
  exact absoluteDerivation_algebraMap k R s a _ v h

/-- Pointwise form of the original-map comparison, for arbitrary forms. -/
theorem absoluteDifferentialExtension_map (s : R)
    (ell : KaehlerDifferential k R →ₗ[R] CoverAlgebra s) (v : CoverAlgebra s)
    (h : ell (KaehlerDifferential.D k R s) = (2 * root s) * v)
    (eta : KaehlerDifferential k R) :
    absoluteDifferentialExtension k R s ell v h
      (KaehlerDifferential.map k k R (CoverAlgebra s) eta) = ell eta :=
  LinearMap.congr_fun (absoluteDifferentialExtension_comp_map k R s ell v h) eta

end KltDP.Geometry.QuadraticCover

#check @KltDP.Geometry.QuadraticCover.absoluteDifferentialExtension_comp_map
#print axioms KltDP.Geometry.QuadraticCover.absoluteDifferentialExtension_comp_map
