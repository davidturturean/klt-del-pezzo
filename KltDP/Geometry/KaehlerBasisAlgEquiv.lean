import KltDP.Geometry.EtaleDifferentialBasisTransport
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Native Kähler bases transported through an actual algebra equivalence

The scalar extension uses the given algebra equivalence itself. Since it
is localization at one, the existing formally étale differential map
transports the basis to the native differential module of the target.
-/

noncomputable section

universe u v

namespace KltDP.Geometry.KaehlerBasisAlgEquiv

variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    {ι : Type v} (b : Basis ι A (KaehlerDifferential k A))

include e b in
/-- A native basis transported along the original algebra equivalence. -/
def basis : Basis ι B (KaehlerDifferential k B) := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  letI : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq fun r => (e.commutes r).symm
  letI : IsLocalization.Away (1 : A) B :=
    IsLocalization.away_of_isUnit_of_bijective B isUnit_one e.bijective
  letI : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (1 : A))
  exact EtaleDifferentialBasisTransport.basis k A B b

/-- A vector that was the differential of an element remains the
differential of its actual image under the algebra equivalence. -/
theorem basis_apply_of_eq_D (i : ι) (a : A)
    (ha : b i = KaehlerDifferential.D k A a) :
    basis e b i = KaehlerDifferential.D k B (e a) := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  letI : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq fun r => (e.commutes r).symm
  letI : IsLocalization.Away (1 : A) B :=
    IsLocalization.away_of_isUnit_of_bijective B isUnit_one e.bijective
  letI : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (1 : A))
  exact EtaleDifferentialBasisTransport.basis_apply_of_eq_D k A B b i a ha

end KltDP.Geometry.KaehlerBasisAlgEquiv
