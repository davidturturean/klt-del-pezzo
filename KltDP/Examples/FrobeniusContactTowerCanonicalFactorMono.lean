import KltDP.Examples.FrobeniusContactTowerCanonicalFactorFiniteTensor
import KltDP.Examples.FrobeniusContactTowerCanonicalFactorOffRange
import KltDP.Geometry.InvertibleTensorExact

/-!
# Monicity of the original finite tensor inclusion

Tensoring with each existing invertible line preserves monomorphisms by the
accepted tensor equivalence. Hence the ordered product of original monic
inclusions is monic. The original pullback-composition map also transfers
monicity from the literal composite inclusion to its iterated expression.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorMono

open KltDP.Geometry FrobeniusContactTowerCanonicalFactorTensor
open FrobeniusContactTowerCanonicalFactorFiniteTensor FrobeniusContactTowerCanonicalFactorOffRange

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance factorMonoModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- Tensoring the actual monic inclusion with the actual invertible line remains monic. -/
theorem tensorInclusion_mono {X : Scheme.{u}} {I : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) [Mono i]
    (L : InvertibleSheaf X) : Mono (schemeStructureTensorInclusion i L.obj) := by
  letI := L.tensorRight_preservesFiniteLimits
  haveI : Mono (i ≫ (SchemeModuleStructureUnit.iso X).hom) := inferInstance
  change Mono ((tensorRight L.obj).map (i ≫ (SchemeModuleStructureUnit.iso X).hom) ≫
    (λ_ L.obj).hom)
  infer_instance

/-- Multiplying the original monic inclusions of actual invertible lines remains monic. -/
theorem familyInclusion_mono {X : Scheme.{u}} (n : ℕ) (L : Fin n → InvertibleSheaf X)
    (i : (j : Fin n) → (L j).obj ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (h : ∀ j, Mono (i j)) : Mono (familyInclusion n L i) := by
  induction n with
  | zero =>
      change Mono (𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf))
      infer_instance
  | succ n ih =>
      letI := ih (fun j => L j.castSucc) (fun j => i j.castSucc) (fun j => h j.castSucc)
      letI := h (Fin.last n)
      letI := tensorInclusion_mono
        (familyInclusion n (fun j => L j.castSucc) (fun j => i j.castSucc)) (L (Fin.last n))
      change Mono (schemeStructureTensorInclusion
        (familyInclusion n (fun j => L j.castSucc) (fun j => i j.castSucc))
        (L (Fin.last n)).obj ≫ i (Fin.last n))
      infer_instance

/-- The original iterated pulled inclusion is monic whenever the actual composite is. -/
theorem iteratedPulledInclusion_mono {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) {I : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    [Mono ((schemeModulePullback (g ≫ f)).map i ≫
      (schemeModulePullbackUnitIso (g ≫ f)).hom)] :
    Mono ((schemeModulePullback g).map
      ((schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom) ≫
      (schemeModulePullbackUnitIso g).hom) := by
  rw [← pulledInclusion_comp f g i]
  infer_instance

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorMono
