import KltDP.Examples.FrobeniusBlowupIntrinsicDifferentialPullback
import KltDP.Geometry.AffineDifferentialExteriorTildeMap
import KltDP.Geometry.AffineModuleTildeSemilinearSections
import KltDP.Geometry.AffineModuleTildeTransposeNormalization

/-!
# The original first-chart native and intrinsic top differential maps agree

The actual affine pullback adjunction reduces equality to the native plane
module. Its original coordinate wedge spans that module. Both original maps
send this wedge to the wedge of the original Rees section images. The result
is equality of the whole actual sheaf maps, with no compatibility premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Examples.FrobeniusBlowupDifferentialIntrinsicLeft

open KltDP.Geometry KltDP.Geometry.SchemeKaehlerSheaf
open AffineModuleTildeSemilinearMap AffineModuleTildeTransposeNormalization
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupDifferential
open FrobeniusBlowupDifferentialMap FrobeniusBlowupDifferentialRestriction
open FrobeniusBlowupDifferentialPullback FrobeniusBlowupDifferentialPullbackComp
open FrobeniusCoordinateDifferentialFrame FrobeniusBlowupIntrinsicDifferentialWedge
open FrobeniusBlowupIntrinsicDifferentialPullback

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance : Algebra (planeRing k) (reesChartRing k) :=
  FrobeniusBlowupDifferentialMap.chartBaseAlgebra
local instance : Algebra k (reesChartRing k) :=
  FrobeniusBlowupDifferentialMap.chartFieldAlgebra

/-- The previously normalized original plane native-to-intrinsic map. -/
def planeNativeMap : (planeNativeModule k).tilde ⟶ planeExterior (k := k) :=
  AffineDifferentialExteriorTildeMap.map k (planeRing k) 2

/-- The previously normalized original Rees native-to-intrinsic map. -/
def leftNativeMap : (leftNativeModule k).tilde ⟶ leftExterior (k := k) :=
  AffineDifferentialExteriorTildeMap.map k (reesChartRing k) 2

/-- Retain the existing native differential as one original bundled map. -/
def nativeDifferential : planeChartModule k ⟶ leftNativeModule k :=
  @ModuleCat.ofHom (reesChartRing k) _ (planeChartModule k) (leftNativeModule k)
    (planeChartModule k).isAddCommGroup (planeChartModule k).isModule
    (leftNativeModule k).isAddCommGroup (leftNativeModule k).isModule
    (planeChartTopMap (k := k))

private def nativeDifferential_one_tmul_D_proof (k : Type u) [Field k]
    (v : Fin 2 → planeRing k) :=
  (exteriorBaseChange_map_ιMulti 2 (chartDifferentialMap (k := k))
    (fun i => KaehlerDifferential.D k (planeRing k) (v i))).trans
      (congrArg (exteriorPower.ιMulti (reesChartRing k) 2)
        (funext (fun i => chartDifferentialMap_one_tmul_D (v i))))

/-- The entire original native map preserves wedges of original derivatives. -/
theorem nativeDifferential_one_tmul_D (v : Fin 2 → planeRing k) :
    nativeDifferential (k := k)
        (1 ⊗ₜ[planeRing k] exteriorPower.ιMulti (planeRing k) 2
          (fun i => KaehlerDifferential.D k (planeRing k) (v i))) =
      exteriorPower.ιMulti (reesChartRing k) 2
        (fun i => KaehlerDifferential.D k (reesChartRing k) (baseMap (v i))) :=
  nativeDifferential_one_tmul_D_proof k v

/-- The native whole-map composite has its original affine transpose. -/
theorem native_transpose (ω : planeNativeModule k) :
    (AffineModuleTilde.pulledTildeAdjunction (baseMap (k := k))).homEquiv
        (planeNativeModule k) (leftExterior (k := k))
        (planeChartDifferentialSheafMap (k := k) ≫ leftNativeMap (k := k)) ω =
      (leftNativeMap (k := k)).val.app (op ⊤)
        (ModuleCat.Tilde.toOpen (leftNativeModule k) ⊤
          (nativeDifferential (k := k) (1 ⊗ₜ[planeRing k] ω))) :=
  AffineModuleTildeTransposeNormalization.native_transpose (baseMap (k := k)) (planeNativeModule k)
    (leftNativeModule k) (leftExterior (k := k))
    (nativeDifferential (k := k)) (leftNativeMap (k := k)) ω

private def planeNative_toOpen_D_proof (k : Type u) [Field k]
    (v : Fin 2 → planeRing k) :=
  AffineDifferentialExteriorTildeMap.map_toOpen_D k (planeRing k) 2 ⊤ v

private def leftNative_toOpen_D_proof (k : Type u) [Field k]
    (v : Fin 2 → reesChartRing k) :=
  AffineDifferentialExteriorTildeMap.map_toOpen_D k (reesChartRing k) 2 ⊤ v

private def native_transpose_D_proof (k : Type u) [Field k]
    (v : Fin 2 → planeRing k) :=
  AffineModuleTildeTransposeNormalization.native_transpose_eq
    (baseMap (k := k)) (planeNativeModule k) (leftNativeModule k)
    (leftExterior (k := k)) (nativeDifferential (k := k)) (leftNativeMap (k := k))
    (exteriorPower.ιMulti (planeRing k) 2
      (fun i => KaehlerDifferential.D k (planeRing k) (v i))) _ _
    (nativeDifferential_one_tmul_D v)
    (leftNative_toOpen_D_proof k (fun i => baseMap (v i)))

/-- Evaluate that transpose on wedges of the original plane derivatives. -/
theorem native_transpose_D (v : Fin 2 → planeRing k) :
    (AffineModuleTilde.pulledTildeAdjunction (baseMap (k := k))).homEquiv
        (planeNativeModule k) (leftExterior (k := k))
        (planeChartDifferentialSheafMap (k := k) ≫ leftNativeMap (k := k))
          (exteriorPower.ιMulti (planeRing k) 2
            (fun i => KaehlerDifferential.D k (planeRing k) (v i))) =
      SchemeExteriorPower.wedge (baseRingSheaf (leftStructure (k := k))) 2 ⊤
        (fun i => (baseRingDerivation (leftStructure (k := k))).d
          (StructureSheaf.toOpen (reesChartRing k) ⊤ (baseMap (v i)))) :=
  native_transpose_D_proof k v

private def intrinsic_transpose_D_proof (k : Type u) [Field k]
    (v : Fin 2 → planeRing k) :=
  AffineModuleTildeTransposeNormalization.pullback_transpose_eq
    (baseMap (k := k)) (planeNativeModule k) (planeExterior (k := k))
    (leftExterior (k := k)) (planeNativeMap (k := k)) (leftMap (k := k))
    (exteriorPower.ιMulti (planeRing k) 2
      (fun i => KaehlerDifferential.D k (planeRing k) (v i))) _ _
    (planeNative_toOpen_D_proof k v) (leftMap_unit_wedge_D v)

/-- The intrinsic whole-map composite has the same original derivative-wedge
transpose, by the actual pullback unit's naturality. -/
theorem intrinsic_transpose_D (v : Fin 2 → planeRing k) :
    (AffineModuleTilde.pulledTildeAdjunction (baseMap (k := k))).homEquiv
        (planeNativeModule k) (leftExterior (k := k))
        ((schemeModulePullback (planeChartMap (k := k))).map (planeNativeMap (k := k)) ≫
          leftMap (k := k))
          (exteriorPower.ιMulti (planeRing k) 2
            (fun i => KaehlerDifferential.D k (planeRing k) (v i))) =
      SchemeExteriorPower.wedge (baseRingSheaf (leftStructure (k := k))) 2 ⊤
        (fun i => (baseRingDerivation (leftStructure (k := k))).d
          (StructureSheaf.toOpen (reesChartRing k) ⊤ (baseMap (v i)))) :=
  intrinsic_transpose_D_proof k v

/-- Equality of the entire original first-chart sheaf maps, derived from the
actual spanning plane wedge and the actual affine pullback adjunction. -/
theorem native_intrinsic_square :
    (schemeModulePullback (planeChartMap (k := k))).map (planeNativeMap (k := k)) ≫
        leftMap (k := k) =
      planeChartDifferentialSheafMap (k := k) ≫ leftNativeMap (k := k) := by
  apply ((AffineModuleTilde.pulledTildeAdjunction (baseMap (k := k))).homEquiv
    (planeNativeModule k) (leftExterior (k := k))).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on (coordinateTopForm_spans (k := k))
  intro ω hω
  obtain rfl := Set.mem_singleton_iff.mp hω
  have h := (intrinsic_transpose_D (k := k) ![uCoord, vCoord]).trans
    (native_transpose_D (k := k) ![uCoord, vCoord]).symm
  have hv : (fun i : Fin 2 => KaehlerDifferential.D k (planeRing k) (![uCoord, vCoord] i)) =
      ![KaehlerDifferential.D k (planeRing k) uCoord,
        KaehlerDifferential.D k (planeRing k) vCoord] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at h
  exact h

end KltDP.Examples.FrobeniusBlowupDifferentialIntrinsicLeft
