import KltDP.Geometry.AffineInvertibleGlobalSectionsFlat
import KltDP.Geometry.AffineInvertibleGlobalSectionsRank
import KltDP.Geometry.AffinePIDTildeTrivial

/-!
# Actual invertible sheaves on an affine PID

The original invertible sheaf is recovered from its actual global
sections by the proved affine counit. Those sections are finite and
flat, hence torsion-free, and their rank is one. Pinned PID freeness
supplies a basis, whose actual tilde map gives the unit-sheaf isomorphism.
The affine-line specialization assumes no chart triviality of the input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- The actual global sections of an original invertible sheaf on an affine PID have a basis of size one. -/
def pidInvertibleGlobalSectionsEquiv (L : InvertibleSheaf (Spec (.of R))) :
    sectionModule L.obj ⊤ ≃ₗ[R] R := by
  letI := invertibleGlobalSections_finite L
  letI := invertibleGlobalSections_noZeroSMulDivisors L
  exact pidRankOneLinearEquiv (sectionModule L.obj ⊤) (invertibleGlobalSections_finrank L)

/-- Every original invertible sheaf on Spec of a PID is actually isomorphic to the unit sheaf. -/
def pidInvertibleUnitIso (L : InvertibleSheaf (Spec (.of R))) :
    L.obj ≅ _root_.SheafOfModules.unit (Spec (.of R)).ringCatSheaf :=
  (invertibleCounitIso L).symm ≪≫
    linearEquivIso (M := sectionModule L.obj ⊤) (N := ModuleCat.of R R)
      (pidInvertibleGlobalSectionsEquiv L) ≪≫ unitIso R

/-- The underlying affine line is literally Spec k[t], and the input is an arbitrary original invertible sheaf. -/
def affineLineInvertibleUnitIso (k : Type u) [Field k]
    (L : InvertibleSheaf (Spec (.of (Polynomial k)))) :
    L.obj ≅ _root_.SheafOfModules.unit (Spec (.of (Polynomial k))).ringCatSheaf :=
  pidInvertibleUnitIso L

end KltDP.Geometry.AffineModuleTilde
