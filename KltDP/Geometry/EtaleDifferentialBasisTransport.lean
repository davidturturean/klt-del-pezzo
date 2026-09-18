import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Native differential bases under an actual formally étale ring map

Transport an existing source differential basis along the original algebra
map and the pinned native Kähler base-change equivalence. When a source basis
vector is `dx`, the target vector is literally `d(algebraMap x)`.
-/

noncomputable section

namespace KltDP.Geometry.EtaleDifferentialBasisTransport

universe u v

variable (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra A B] [Algebra k B]
variable [hTower : IsScalarTower k A B] [hEtale : Algebra.FormallyEtale A B]
variable {ι : Type v} (β : Basis ι A (KaehlerDifferential k A))

include hTower hEtale in
/-- The transported basis uses the original scalar-extension differential. -/
def basis : Basis ι B (KaehlerDifferential k B) :=
  (β.baseChange B).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A B)

include hTower hEtale in
theorem basis_apply (i : ι) :
    basis k A B β i =
      KaehlerDifferential.mapBaseChange k A B (1 ⊗ₜ[A] β i) := by
  rw [basis, Basis.map_apply, Basis.baseChange_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply]

include hTower hEtale in
/-- Native coordinate vectors remain native differentials of the actual images. -/
theorem basis_apply_of_eq_D (i : ι) (x : A) (hx : β i = KaehlerDifferential.D k A x) :
    basis k A B β i = KaehlerDifferential.D k B (algebraMap A B x) := by
  rw [basis_apply, hx, KaehlerDifferential.mapBaseChange_tmul,
    KaehlerDifferential.map_D, one_smul]

end KltDP.Geometry.EtaleDifferentialBasisTransport
