import KltDP.Geometry.AffineKaehlerPullbackComparison
import KltDP.Geometry.AffineDifferentialExteriorTildeMap
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport
import KltDP.LinearAlgebra.ExteriorPowerSemilinearMap
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# The original affine exterior differential restriction square

The two whole sheaf maps have the same original affine-adjunction transpose
on wedges of native derivatives. The pinned surjective presentation of the
Kähler module and alternating-map extensionality on the free-module basis
show that these wedges suffice. No smoothness or open-immersion premise is
needed, and both maps retain their original constructions.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace KltDP.Geometry.AffineDifferentialExteriorPullbackComparison

open AffineKaehlerTildeDerivation AffineModuleTildeSemilinearMap SchemeKaehlerSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem linearMap_ext_D (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (n : ℕ) {N : Type u} [AddCommGroup N] [Module A N]
    {a b : (⋀[A]^n (KaehlerDifferential R A)) →ₗ[A] N}
    (h : ∀ v : Fin n → A,
      a (exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D R A (v i))) =
        b (exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D R A (v i)))) : a = b := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.compLinearMap_injective
    (Finsupp.linearCombination A (KaehlerDifferential.D R A))
    (KaehlerDifferential.linearCombination_surjective R A)
  refine Basis.ext_alternating (Finsupp.basisSingleOne : Basis A A (A →₀ A)) ?_
  intro v _
  simpa only [AlternatingMap.compLinearMap_apply, LinearMap.compAlternatingMap_apply,
    Finsupp.coe_basisSingleOne, Finsupp.linearCombination_single, one_smul] using h v

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The original exterior map of the original semilinear differential map. -/
def nativeMap (n : ℕ) :
    (differentialModule R A).exteriorPower n →ₛₗ[algebraMap A B]
      (differentialModule R B).exteriorPower n :=
  KltDP.LinearAlgebra.ExteriorPowerSemilinearMap.map (algebraMap A B) n
    (AffineKaehlerPullbackComparison.differentialMap R A B)

/-- The original map sends each native derivative wedge to the derivative wedge of the images. -/
theorem nativeMap_D (n : ℕ) (v : Fin n → A) :
    nativeMap R A B n
        (exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D R A (v i))) =
      exteriorPower.ιMulti B n
        (fun i => KaehlerDifferential.D R B (algebraMap A B (v i))) := by
  refine (KltDP.LinearAlgebra.ExteriorPowerSemilinearMap.map_ιMulti
    (algebraMap A B) n (AffineKaehlerPullbackComparison.differentialMap R A B)
    (fun i => KaehlerDifferential.D R A (v i))).trans ?_
  apply congrArg (exteriorPower.ιMulti B n)
  funext i
  exact AffineKaehlerPullbackComparison.differentialMap_d R A B (v i)

/-- The original native exterior restriction on the actual scheme pullback. -/
def nativeSheafMap (n : ℕ) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        ((differentialModule R A).exteriorPower n).tilde ⟶
      ((differentialModule R B).exteriorPower n).tilde :=
  pullbackMap (algebraMap A B) (nativeMap R A B n)

/-- The original intrinsic exterior pullback map, transported along the proved base-map equality. -/
def intrinsicMap (n : ℕ) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (SchemeExteriorPower.sheaf
          (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A)))) n) ⟶
      SchemeExteriorPower.sheaf
        (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R B)))) n :=
  SchemeKaehlerExteriorPullbackTransport.map
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (AffineKaehlerPullbackComparison.baseMap_comp R A B) n

private def native_transpose_D (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (n : ℕ) (v : Fin n → A) :=
  AffineModuleTildeTransposeNormalization.native_transpose_eq (algebraMap A B)
    ((differentialModule R A).exteriorPower n) ((differentialModule R B).exteriorPower n)
    (SchemeExteriorPower.sheaf
      (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R B)))) n)
    (extendHom (algebraMap A B) (nativeMap R A B n))
    (AffineDifferentialExteriorTildeMap.map R B n)
    (exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D R A (v i))) _ _
    ((extendHom_one_tmul (algebraMap A B) (nativeMap R A B n) _).trans
      (nativeMap_D R A B n v))
    (AffineDifferentialExteriorTildeMap.map_toOpen_D R B n ⊤
      (fun i => algebraMap A B (v i)))

private def intrinsic_transpose_D (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (n : ℕ) (v : Fin n → A) :=
  AffineModuleTildeTransposeNormalization.pullback_transpose_eq (algebraMap A B)
    ((differentialModule R A).exteriorPower n)
    (SchemeExteriorPower.sheaf
      (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A)))) n)
    (SchemeExteriorPower.sheaf
      (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R B)))) n)
    (AffineDifferentialExteriorTildeMap.map R A n) (intrinsicMap R A B n)
    (exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D R A (v i))) _ _
    (AffineDifferentialExteriorTildeMap.map_toOpen_D R A n ⊤ v)
    (SchemeKaehlerExteriorPullbackTransport.map_unit_wedge_toOpen
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) (algebraMap A B)
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (AffineKaehlerPullbackComparison.baseMap_comp R A B) n v)

/-- The entire original native exterior restriction and original intrinsic map agree.
The equality is proved on native generators through the original affine adjunction. -/
theorem native_intrinsic_square (n : ℕ) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map
        (AffineDifferentialExteriorTildeMap.map R A n) ≫ intrinsicMap R A B n =
      nativeSheafMap R A B n ≫ AffineDifferentialExteriorTildeMap.map R B n := by
  apply ((AffineModuleTilde.pulledTildeAdjunction (algebraMap A B)).homEquiv
    ((differentialModule R A).exteriorPower n)
    (SchemeExteriorPower.sheaf
      (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R B)))) n)).injective
  apply ModuleCat.hom_ext
  apply linearMap_ext_D R A n
  intro v
  exact (intrinsic_transpose_D R A B n v).trans (native_transpose_D R A B n v).symm

end KltDP.Geometry.AffineDifferentialExteriorPullbackComparison
