import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import KltDP.Geometry.AffineModuleTildeTransposeNormalization
import KltDP.Geometry.AffineKaehlerTildeDerivation
import KltDP.Geometry.AffineTopDifferentialFrame

/-!
# The original affine native top-differential map

Extend the original source exterior module along the supplied original
algebra map, apply the existing exterior base-change map, and take the
exterior of the original Kähler map. Both the bundled source and its scalar
action are the original ModuleCat.extendScalars object. No frame is used to
define the map or to prove its derivative-wedge formula.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace KltDP.Geometry.AffineNativeTopDifferential

open AffineKaehlerTildeDerivation AffineTopDifferentialFrame

universe u

variable (k : Type u) [CommRing k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
variable (φ : A →ₐ[k] B) (n : ℕ)

/-- The actual affine native map on the original scalar-extended top forms. -/
def map :
    (ModuleCat.extendScalars φ.toRingHom).obj ((differentialModule k A).exteriorPower n) ⟶
      (differentialModule k B).exteriorPower n := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  exact ModuleCat.ofHom
    ((exteriorPower.map n (KaehlerDifferential.mapBaseChange k A B)).comp
      (KltDP.Compatibility.ExteriorPowerBaseChange.map A B n (KaehlerDifferential k A)))

/-- Every original derivative wedge has its prescribed original image. -/
theorem map_one_tmul_D (v : Fin n → A) :
    map k φ n ((1 : B) ⊗ₜ[A,φ.toRingHom]
        exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D k A (v i))) =
      exteriorPower.ιMulti B n (fun i => KaehlerDifferential.D k B (φ (v i))) := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  change exteriorPower.map n (KaehlerDifferential.mapBaseChange k A B)
    (KltDP.Compatibility.ExteriorPowerBaseChange.map A B n (KaehlerDifferential k A)
      (1 ⊗ₜ[A] exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D k A (v i)))) = _
  refine (AffineModuleTildeTransposeNormalization.exteriorBaseChange_map_ιMulti n
    (KaehlerDifferential.mapBaseChange k A B)
    (fun i => KaehlerDifferential.D k A (v i))).trans ?_
  apply congrArg (exteriorPower.ιMulti B n)
  funext i
  rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]
  rfl

/-- An actual native differential basis supplies the actual top-wedge span.
This is used only to compare whole maps after the map itself is constructed. -/
theorem basis_wedge_spans (β : Basis (Fin n) A (KaehlerDifferential k A)) :
    Submodule.span A {exteriorPower.ιMulti A n β} = ⊤ := by
  apply top_unique
  intro ω _
  rw [← (determinantEquiv β).symm_apply_apply ω, determinantEquiv_symm_apply]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

end KltDP.Geometry.AffineNativeTopDifferential
