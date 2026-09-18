import KltDP.Geometry.AffineNativeTopDifferentialSheaf
import KltDP.Geometry.EtaleCoordinateDifferentialBasis
import KltDP.Compatibility.StandardSmoothEtaleCoordinates

/-!
# The whole differential comparison on an actual standard-smooth source

The original standard-smooth presentation supplies actual polynomial étale
coordinates. Their differentials give the native source basis, so the entire
original native and intrinsic top-differential sheaf maps agree without a
basis, coordinate, or compatibility premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.AffineNativeTopDifferential

open AffineKaehlerTildeDerivation

universe u

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] (n : ℕ)

/-- Actual standard smoothness supplies an actual basis of coordinate
function differentials, in the original Kähler module. -/
theorem exists_coordinate_basis [Algebra.IsStandardSmoothOfRelativeDimension n k A] :
    ∃ β : Basis (Fin n) A (KaehlerDifferential k A), ∃ x : Fin n → A,
      ∀ i, β i = KaehlerDifferential.D k A (x i) := by
  obtain ⟨g, hg⟩ :=
    KltDP.StandardSmoothCoordinates.exists_standardSmoothZero_mvPolynomial n k A
  letI : Algebra (MvPolynomial (Fin n) k) A := g.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin n) k) A := hg
  refine ⟨EtaleCoordinateDifferentialBasis.basis k A n,
    fun i => g (MvPolynomial.X i), fun i => ?_⟩
  exact EtaleCoordinateDifferentialBasis.basis_apply k A n i

variable {A} {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)

/-- The entire original native and intrinsic maps agree for every original
algebra homomorphism whose affine source is standard smooth. All coordinates
and the source basis are derived internally. -/
theorem native_intrinsic_square [Algebra.IsStandardSmoothOfRelativeDimension n k A] :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom φ.toRingHom))).map
        (AffineDifferentialExteriorTildeMap.map k A n) ≫ intrinsicMap k φ n =
      nativeSheafMap k φ n ≫ AffineDifferentialExteriorTildeMap.map k B n := by
  obtain ⟨β, x, hx⟩ := exists_coordinate_basis k A n
  exact native_intrinsic_square_of_coordinate_basis k φ n β x hx

end KltDP.Geometry.AffineNativeTopDifferential
