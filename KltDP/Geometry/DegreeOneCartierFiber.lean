import KltDP.Geometry.DegreeOneCartierPullback
import KltDP.Geometry.CartierPullbackClosedFiber
import KltDP.Geometry.ClosedImmersionKerDegree

/-!
The degree of the original pulled line bundle computes H0 of the actual
scheme-theoretic fiber over the original Cartier point. The equality
of kernels is proved by the preceding original-map comparison.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open KltDP.Geometry.ModuleCohomology
universe u

namespace KltDP.Geometry.DegreeOneCartierFiber

/-- The original point fiber has H0 dimension one over the original base. -/
theorem cohomologyDimension_eq_one
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (σ : Y ⟶ Spec (CommRingCat.of k))
    (π : X ⟶ Y) [GenericPointPreserving π] [QuasiCompact π]
    (hπ : π ≫ σ = f) (hdim : topologicalKrullDim X ≤ 1)
    (L : InvertibleSheaf Y) (D : CartierDivisor Y)
    (hD : HasRegularCartierEquations Y D)
    (eD : cartierDivisorModule Y D ≅ L.obj)
    (i : Spec (CommRingCat.of k) ⟶ Y) [IsClosedImmersion i]
    (hi : i ≫ σ = 𝟙 _) 
    (hI : effectiveCartierIdealDataOfRegularEquations Y D hD = i.ker)
    (hdegree : eulerCharacteristic f (pullbackInvertibleSheaf π L).obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 1) :
    cohomologyDimension (pullback.snd π i)
      (_root_.SheafOfModules.unit (pullback π i).ringCatSheaf) 0 = 1 := by
  letI : IsClosedImmersion (pullback.fst π i) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let DP : CartierDivisor X := DominantCartierPullback.pullbackHom π D
  let hDP : HasRegularCartierEquations X DP :=
    DominantCartierPullback.pullbackHom_hasRegularEquations π D hD
  have hker : (effectiveCartierInclusion X DP hDP).ker = (pullback.fst π i).ker := by
    change (effectiveCartierIdealDataOfRegularEquations X DP hDP).gluedTo.ker = _
    rw [Scheme.IdealSheafData.ker_gluedTo]
    have hp : DP = pullbackDivisor π D hD :=
      DominantCartierPullback.pullbackHom_eq_pullbackDivisor π D hD
    simpa only [pullbackIdealData, ← hp] using
      CartierPullbackClosedFiber.ideal_eq_fiber_ker π D hD i hI
  have hc := cohomologyDimension_unit_eq_of_ker_eq
    (effectiveCartierInclusion X DP hDP) (pullback.fst π i) hker f
  have hd := DegreeOneCartierPullback.effectiveCartierDegree_eq_one
    f hdim π L D hD eD hdegree
  change cohomologyDimension (effectiveCartierInclusion X DP hDP ≫ f)
    (_root_.SheafOfModules.unit (effectiveCartierScheme X DP hDP).ringCatSheaf) 0 = 1 at hd
  rw [hc] at hd
  have hf : pullback.fst π i ≫ f = pullback.snd π i := by
    rw [← hπ, pullback.condition_assoc, hi, Category.comp_id]
  rwa [hf] at hd

#check KltDP.Geometry.DegreeOneCartierFiber.cohomologyDimension_eq_one
#print axioms KltDP.Geometry.DegreeOneCartierFiber.cohomologyDimension_eq_one

end KltDP.Geometry.DegreeOneCartierFiber
