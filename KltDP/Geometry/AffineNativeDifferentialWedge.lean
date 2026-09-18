import KltDP.Geometry.AffineNativeTopDifferentialMap

/-!
# The original native map on wedges of arbitrary differential forms

The original scalar-extension map is evaluated on arbitrary pure wedges.
The algebra-map specialization identifies the normalized algebra instance
explicitly before comparing it with the original Kähler map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace KltDP.Geometry.AffineNativeTopDifferential

universe u

variable (k : Type u) [CommRing k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- The actual native map evaluates on every original wedge, with its
actual scalar action fixed by the supplied algebra homomorphism. -/
theorem map_one_tmul_forms (φ : A →ₐ[k] B) (n : ℕ)
    (v : Fin n → KaehlerDifferential k A) :
    map k φ n ((1 : B) ⊗ₜ[A,φ.toRingHom] exteriorPower.ιMulti A n v) =
      letI : Algebra A B := φ.toRingHom.toAlgebra
      letI : IsScalarTower k A B :=
        IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
      exteriorPower.ιMulti B n (fun i => KaehlerDifferential.map k k A B (v i)) := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  change exteriorPower.map n (KaehlerDifferential.mapBaseChange k A B)
    (KltDP.Compatibility.ExteriorPowerBaseChange.map A B n (KaehlerDifferential k A)
      (1 ⊗ₜ[A] exteriorPower.ιMulti A n v)) = _
  refine (AffineModuleTildeTransposeNormalization.exteriorBaseChange_map_ιMulti n
    (KaehlerDifferential.mapBaseChange k A B) v).trans ?_
  apply congrArg (exteriorPower.ιMulti B n)
  funext i
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul]

/-- A supplied algebra structure agrees with the actual homomorphism.
The homomorphism remains fixed while its induced algebra is identified. -/
theorem map_one_tmul_forms_of_algebraMap (φ : A →ₐ[k] B)
    [Algebra A B] [IsScalarTower k A B]
    (hφ : φ.toRingHom = algebraMap A B)
    (n : ℕ) (v : Fin n → KaehlerDifferential k A) :
    map k φ n ((1 : B) ⊗ₜ[A,φ.toRingHom] exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (fun i => KaehlerDifferential.map k k A B (v i)) := by
  have he : φ.toRingHom.toAlgebra = (inferInstance : Algebra A B) :=
    Algebra.algebra_ext _ _ fun x => DFunLike.congr_fun hφ x
  cases he
  exact map_one_tmul_forms k φ n v

/-- When the homomorphism is the original algebra map, the target forms
use that same original algebra structure and the original Kähler map. -/
theorem map_one_tmul_forms_algebraMap [Algebra A B] [IsScalarTower k A B]
    (n : ℕ) (v : Fin n → KaehlerDifferential k A) :
    map k (IsScalarTower.toAlgHom k A B) n
        ((1 : B) ⊗ₜ[A,(algebraMap A B)] exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (fun i => KaehlerDifferential.map k k A B (v i)) := by
  exact map_one_tmul_forms_of_algebraMap k (IsScalarTower.toAlgHom k A B) rfl n v

end KltDP.Geometry.AffineNativeTopDifferential

#print axioms KltDP.Geometry.AffineNativeTopDifferential.map_one_tmul_forms_algebraMap
