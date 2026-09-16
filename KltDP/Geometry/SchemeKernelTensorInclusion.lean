import KltDP.Compatibility.SheafOverTensorNaturality
import KltDP.Geometry.KernelLinePullbackOffRange
import KltDP.Geometry.SheafPicard
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The original tensor ideal inclusion is locally an epimorphism off its support

On an open with empty preimage, the original restricted structural map
is zero. Kernel preservation proves that the restriction of its original
kernel inclusion is an isomorphism. The proved naturality of the actual
Over-site tensor comparison carries this to the original tensor-inclusion
map `M ⊗ I → M`, with the actual structure-module unit comparison.

The result applies to every actual module sheaf, and in particular to a
line-bundle twist of the actual closed-point ideal. The point corollary
has no supplied local epi, frame, or coherence witness. Vanishing of a
selected section at the point and the effective Cartier degree argument
remain subsequent obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeKernelTensor

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}}

local instance (Z : Scheme.{u}) : MonoidalCategory Z.Modules :=
  Scheme.Modules.monoidalCategory Z

/-- Empty preimage makes the original structural module map zero on
the original Over site. -/
theorem over_structure_eq_zero (f : X ⟶ Y) (U : Y.Opens)
    [IsEmpty (f ⁻¹ᵁ U).toScheme] :
    (_root_.SheafOfModules.overFunctor Y.ringCatSheaf U).map
      (structureToPushforwardUnit f) = 0 := by
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  have hpre : f ⁻¹ᵁ V.unop.left = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    exact (inferInstance : IsEmpty (f ⁻¹ᵁ U).toScheme).false
      ⟨x, V.unop.hom.le hx⟩
  haveI : Subsingleton Γ(X, f ⁻¹ᵁ V.unop.left) := by
    rw [hpre]
    infer_instance
  change f.app V.unop.left s = 0
  exact Subsingleton.elim _ _

/-- The actual kernel inclusion restricts to an isomorphism whenever
the original scheme morphism has empty preimage over that open. -/
theorem over_kernelIdealι_isIso (f : X ⟶ Y) (U : Y.Opens)
    [IsEmpty (f ⁻¹ᵁ U).toScheme] :
    IsIso ((_root_.SheafOfModules.overFunctor Y.ringCatSheaf U).map
      (schemeKernelIdealι f)) := by
  let F := _root_.SheafOfModules.overFunctor Y.ringCatSheaf U
  letI : F.IsRightAdjoint :=
    inferInstanceAs ((_root_.SheafOfModules.pushforward.{u} (F := Over.forget U)
      (J := (Opens.grothendieckTopology Y).over U)
      (K := Opens.grothendieckTopology Y)
      (𝟙 (Y.ringCatSheaf.over U))).IsRightAdjoint)
  have hzero : F.map (structureToPushforwardUnit f) = 0 := over_structure_eq_zero f U
  haveI : IsIso (kernel.ι (F.map (structureToPushforwardUnit f))) := by
    rw [hzero]
    infer_instance
  have he : (PreservesKernel.iso F (structureToPushforwardUnit f)).hom ≫
      kernel.ι (F.map (structureToPushforwardUnit f)) =
    F.map (kernel.ι (structureToPushforwardUnit f)) := by
    simpa only [PreservesKernel.iso_hom] using
      kernelComparison_comp_ι (structureToPushforwardUnit f) F
  change IsIso (F.map (kernel.ι (structureToPushforwardUnit f)))
  rw [← he]
  infer_instance

/-- The actual structure module is the tensor unit through the accepted
sheafification counit, followed by the original right unitor. -/
def actualUnitRightIso (M : Y.Modules) :
    M ⊗ _root_.SheafOfModules.unit Y.ringCatSheaf ≅ M :=
  tensorIso (Iso.refl M)
      (_root_.PresheafOfModules.sheafTensorUnitIso Y.sheaf.val Y.ringCatSheaf.cond).symm ≪≫
    (ρ_ M)

/-- Tensor the original ideal inclusion and then use the original
structure-module unit comparison. -/
def inclusion (f : X ⟶ Y) (M : Y.Modules) : M ⊗ schemeKernelIdeal f ⟶ M :=
  (𝟙 M ⊗ schemeKernelIdealι f) ≫ (actualUnitRightIso M).hom

set_option maxHeartbeats 800000 in
/-- The original tensor ideal inclusion restricts to an isomorphism
on every actual open with empty preimage. -/
theorem over_inclusion_isIso (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    [IsEmpty (f ⁻¹ᵁ U).toScheme] :
    IsIso ((_root_.SheafOfModules.overFunctor Y.ringCatSheaf U).map (inclusion f M)) := by
  letI : IsIso ((_root_.SheafOfModules.overFunctor
      (⟨Y.sheaf.val ⋙ forget₂ CommRingCat RingCat, Y.ringCatSheaf.cond⟩ :
        Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) U).map
      (schemeKernelIdealι f)) := over_kernelIdealι_isIso f U
  letI : IsIso ((_root_.SheafOfModules.overFunctor Y.ringCatSheaf U).map
      (𝟙 M ⊗ schemeKernelIdealι f)) :=
    KltDP.SheafOfModules.isIso_over_map_tensorHom Y.sheaf.val Y.ringCatSheaf.cond U
      (𝟙 M) (schemeKernelIdealι f)
  change IsIso ((_root_.SheafOfModules.overFunctor Y.ringCatSheaf U).map
    ((𝟙 M ⊗ schemeKernelIdealι f) ≫ (actualUnitRightIso M).hom))
  rw [Functor.map_comp]
  infer_instance

/-- Every actual open disjoint from the range of a closed immersion
has the original tensor ideal inclusion as a sheaf epimorphism. -/
theorem over_inclusion_epi_of_le_complement (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) (U : Y.Opens)
    (hU : U ≤ KernelLinePullbackOffRange.rangeComplement f) :
    Epi ((_root_.SheafOfModules.overFunctor Y.ringCatSheaf U).map (inclusion f M)) := by
  letI : IsEmpty (f ⁻¹ᵁ U).toScheme :=
    ⟨fun x => (hU x.2) ⟨x.1, rfl⟩⟩
  letI := over_inclusion_isIso f M U
  infer_instance

/-- Away from an actual point, its original residue-field ideal tensor
inclusion is an epimorphism on the actual Over site. -/
theorem point_over_inclusion_epi (Y : Scheme.{u}) (x : Y) (M : Y.Modules)
    (U : Y.Opens) (hx : x ∉ U) :
    Epi ((_root_.SheafOfModules.overFunctor Y.ringCatSheaf U).map
      (inclusion (Y.fromSpecResidueField x) M)) := by
  letI : IsEmpty ((Y.fromSpecResidueField x) ⁻¹ᵁ U).toScheme := by
    refine ⟨fun y => hx ?_⟩
    have hy : (Y.fromSpecResidueField x).base y.1 ∈ U := y.2
    simpa only [Y.fromSpecResidueField_apply x] using hy
  letI := over_inclusion_isIso (Y.fromSpecResidueField x) M U
  infer_instance

end KltDP.Geometry.SchemeKernelTensor
