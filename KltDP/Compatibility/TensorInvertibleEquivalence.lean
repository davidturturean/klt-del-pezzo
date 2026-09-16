import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Tensoring with a tensor-invertible object is an equivalence, hence exact

For an object `L` of a monoidal category with a tensor inverse `L'` (isomorphisms
`L ⊗ L' ≅ 𝟙_ C` and `L' ⊗ L ≅ 𝟙_ C`), the functor `− ⊗ L` is an equivalence of categories with
quasi-inverse `− ⊗ L'`: the unit and counit are assembled from the pinned natural isomorphisms
`rightUnitorNatIso` and `tensorRightTensor` and the natural isomorphism of right-tensoring functors
induced by the given object isomorphisms (`whisker_exchange`). Consequently `− ⊗ L` is both a left
and a right adjoint, so it preserves finite limits, finite colimits and zero morphisms, and carries
short exact sequences to short exact sequences (`ShortComplex.ShortExact.map_of_exact`).

No sheaf or scheme is involved; the scheme-module specialization (invertible sheaves, Cartier
modules) is in `KltDP.Geometry.InvertibleTensorExact`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace KltDP.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An isomorphism of objects induces a natural isomorphism of right-tensoring functors. -/
def tensorRightIsoOfIso {L L' : C} (e : L ≅ L') : tensorRight L ≅ tensorRight L' :=
  NatIso.ofComponents (fun M => whiskerLeftIso M e) (fun {M N} f => by
    show f ▷ L ≫ N ◁ e.hom = M ◁ e.hom ≫ f ▷ L'
    exact (whisker_exchange f e.hom).symm)

variable (L L' : C) (e : L ⊗ L' ≅ 𝟙_ C) (e' : L' ⊗ L ≅ 𝟙_ C)

/-- The unit `𝟭 ≅ (− ⊗ L) ⋙ (− ⊗ L')` of the tensor equivalence. -/
def tensorRightUnitIso : 𝟭 C ≅ tensorRight L ⋙ tensorRight L' :=
  (rightUnitorNatIso C).symm ≪≫ (tensorRightIsoOfIso e).symm ≪≫ tensorRightTensor L L'

/-- The counit `(− ⊗ L') ⋙ (− ⊗ L) ≅ 𝟭` of the tensor equivalence. -/
def tensorRightCounitIso : tensorRight L' ⋙ tensorRight L ≅ 𝟭 C :=
  (tensorRightTensor L' L).symm ≪≫ tensorRightIsoOfIso e' ≪≫ rightUnitorNatIso C

/-- **Tensoring with a tensor-invertible object is an equivalence** with quasi-inverse tensoring
with the inverse. -/
def tensorRightEquivalence : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorRight L) (tensorRight L') (tensorRightUnitIso L L' e)
    (tensorRightCounitIso L L' e')

/-- The adjunction `(− ⊗ L) ⊣ (− ⊗ L')`. -/
def tensorRightAdjunction : tensorRight L ⊣ tensorRight L' :=
  (tensorRightEquivalence L L' e e').toAdjunction

/-- The adjunction `(− ⊗ L') ⊣ (− ⊗ L)`. -/
def tensorRightAdjunction' : tensorRight L' ⊣ tensorRight L :=
  (tensorRightEquivalence L L' e e').symm.toAdjunction

include L' e e' in
/-- `− ⊗ L` preserves finite limits (it is a right adjoint). -/
theorem tensorRight_preservesFiniteLimits : PreservesFiniteLimits (tensorRight L) := by
  haveI : PreservesLimitsOfSize.{0, 0} (tensorRight L) :=
    (tensorRightAdjunction' L L' e e').rightAdjoint_preservesLimits
  exact PreservesLimitsOfSize.preservesFiniteLimits (tensorRight L)

include L' e e' in
/-- `− ⊗ L` preserves finite colimits (it is a left adjoint). -/
theorem tensorRight_preservesFiniteColimits : PreservesFiniteColimits (tensorRight L) := by
  haveI : PreservesColimitsOfSize.{0, 0} (tensorRight L) :=
    (tensorRightAdjunction L L' e e').leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits (tensorRight L)

include L' e e' in
/-- `− ⊗ L` preserves zero morphisms (it is a left adjoint). -/
theorem tensorRight_preservesZeroMorphisms [HasZeroMorphisms C] :
    (tensorRight L).PreservesZeroMorphisms := by
  haveI : (tensorRight L).IsLeftAdjoint := ⟨⟨tensorRight L', ⟨tensorRightAdjunction L L' e e'⟩⟩⟩
  infer_instance

include L' e e' in
/-- **Tensoring a short exact sequence with a tensor-invertible object gives a short exact
sequence.** -/
theorem shortExact_map_tensorRight [HasZeroMorphisms C] (S : ShortComplex C)
    (hS : S.ShortExact) :
    letI := tensorRight_preservesZeroMorphisms L L' e e'
    (S.map (tensorRight L)).ShortExact := by
  letI := tensorRight_preservesZeroMorphisms L L' e e'
  haveI := tensorRight_preservesFiniteLimits L L' e e'
  haveI := tensorRight_preservesFiniteColimits L L' e e'
  exact hS.map_of_exact (tensorRight L)

end KltDP.Monoidal
