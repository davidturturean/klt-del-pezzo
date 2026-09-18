import KltDP.Geometry.AffineNativeTopDifferentialMap
import KltDP.Geometry.AffineDifferentialExteriorTildeMap
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport

/-!
# The original affine native and intrinsic top-differential maps

The original affine pullback adjunction compares the two whole sheaf maps.
Their transposes agree on every wedge of derivatives of original functions.
An actual coordinate differential basis then proves equality on the entire
native top module. The basis is used only to prove equality; both maps are
constructed independently from the original algebra homomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct ChangeOfRings

namespace KltDP.Geometry.AffineNativeTopDifferential

open AffineKaehlerTildeDerivation SchemeKaehlerSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

universe u

variable (k : Type u) [CommRing k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
variable (φ : A →ₐ[k] B) (n : ℕ)

/-- The actual original structure maps commute, by the algebra homomorphism law. -/
theorem spec_comp :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun ψ : k →+* B => Spec.map (CommRingCat.ofHom ψ))
  ext r
  exact φ.commutes r

/-- The actual intrinsic exterior of the original affine differential sheaf. -/
abbrev intrinsic (A : Type u) [CommRing A] [Algebra k A] (n : ℕ) :
    (Spec (CommRingCat.of A)).Modules :=
  SchemeExteriorPower.sheaf
    (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n

/-- Sheafify the original scalar-extended native map using the original
normalized affine pullback isomorphism. -/
def nativeSheafMap :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj
        ((differentialModule k A).exteriorPower n).tilde ⟶
      ((differentialModule k B).exteriorPower n).tilde :=
  (AffineModuleTilde.pullbackIso φ.toRingHom
    ((differentialModule k A).exteriorPower n)).hom ≫
      AffineModuleTilde.map (map k φ n)

/-- The original intrinsic differential map, with its actual field-map transport. -/
def intrinsicMap :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj
        (intrinsic k A n) ⟶ intrinsic k B n :=
  SchemeKaehlerExteriorPullbackTransport.map
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (Spec.map (CommRingCat.ofHom φ.toRingHom))
    (Spec.map (CommRingCat.ofHom (algebraMap k B))) (spec_comp k φ) n

private def native_transpose_D_proof (v : Fin n → A) :=
  AffineModuleTildeTransposeNormalization.native_transpose_eq φ.toRingHom
    ((differentialModule k A).exteriorPower n)
    ((differentialModule k B).exteriorPower n) (intrinsic k B n)
    (map k φ n) (AffineDifferentialExteriorTildeMap.map k B n)
    (exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D k A (v i))) _ _
    (map_one_tmul_D k φ n v)
    (AffineDifferentialExteriorTildeMap.map_toOpen_D k B n ⊤ (fun i => φ (v i)))

private def intrinsic_transpose_D_proof (v : Fin n → A) :=
  AffineModuleTildeTransposeNormalization.pullback_transpose_eq φ.toRingHom
    ((differentialModule k A).exteriorPower n) (intrinsic k A n) (intrinsic k B n)
    (AffineDifferentialExteriorTildeMap.map k A n) (intrinsicMap k φ n)
    (exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D k A (v i))) _ _
    (AffineDifferentialExteriorTildeMap.map_toOpen_D k A n ⊤ v)
    (SchemeKaehlerExteriorPullbackTransport.map_unit_wedge_toOpen
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) φ.toRingHom
      (Spec.map (CommRingCat.ofHom (algebraMap k B))) (spec_comp k φ) n v)

/-- Equality of the entire original native and intrinsic sheaf maps follows
from an actual basis consisting of differentials of actual source functions.
No comparison or differential-factorization equality is assumed. -/
theorem native_intrinsic_square_of_coordinate_basis
    (β : Basis (Fin n) A (KaehlerDifferential k A)) (x : Fin n → A)
    (hx : ∀ i, β i = KaehlerDifferential.D k A (x i)) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom φ.toRingHom))).map
        (AffineDifferentialExteriorTildeMap.map k A n) ≫ intrinsicMap k φ n =
      nativeSheafMap k φ n ≫ AffineDifferentialExteriorTildeMap.map k B n := by
  apply ((AffineModuleTilde.pulledTildeAdjunction φ.toRingHom).homEquiv
    ((differentialModule k A).exteriorPower n) (intrinsic k B n)).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on (basis_wedge_spans k n β)
  intro ω hω
  obtain rfl := Set.mem_singleton_iff.mp hω
  have h := (intrinsic_transpose_D_proof k φ n x).trans
    (native_transpose_D_proof k φ n x).symm
  have hv : (fun i => KaehlerDifferential.D k A (x i)) =
      (β : Fin n → KaehlerDifferential k A) := funext (fun i => (hx i).symm)
  rw [hv] at h
  exact h

end KltDP.Geometry.AffineNativeTopDifferential
