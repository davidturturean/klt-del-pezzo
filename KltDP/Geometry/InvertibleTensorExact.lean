import KltDP.Compatibility.TensorInvertibleEquivalence
import KltDP.Compatibility.SheafModuleExactness
import KltDP.Geometry.CartierPrincipalPicard

/-!
# Tensoring with an invertible sheaf preserves short exact sequences

On a scheme `X`, an invertible sheaf `L` (accepted `InvertibleSheaf X`, locally free of rank one)
has the accepted tensor inverse `dual L` with `L ⊗ dual L ≅ 𝟙_` (`tensorDualIsoUnit`); the symmetric
structure of the accepted tensor product gives the other side. Hence `− ⊗ L` is an equivalence of
`X.Modules` (`KltDP.Monoidal.tensorRightEquivalence`) and carries short exact sequences of sheaves of
modules to short exact sequences. The Cartier modules `O_X(E)` are the special case
`cartierDivisorInvertibleSheaf`.

Nothing is checked on stalks or on an open cover: exactness follows from the equivalence.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance invertibleTensorExactMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance invertibleTensorExactSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

variable {X : Scheme.{u}}

/-- An invertible sheaf has a tensor inverse: the accepted sheaf dual, with the accepted
evaluation isomorphism on one side and its braiding on the other. -/
theorem InvertibleSheaf.exists_tensorInverse (L : InvertibleSheaf X) :
    ∃ L' : X.Modules, Nonempty (L.obj ⊗ L' ≅ 𝟙_ X.Modules) ∧
      Nonempty (L' ⊗ L.obj ≅ 𝟙_ X.Modules) :=
  ⟨_, ⟨KltDP.SheafOfModules.tensorDualIsoUnit X.sheaf.val X.ringCatSheaf.cond L.obj⟩,
    ⟨BraidedCategory.braiding _ L.obj ≪≫
      KltDP.SheafOfModules.tensorDualIsoUnit X.sheaf.val X.ringCatSheaf.cond L.obj⟩⟩

/-- `− ⊗ L` preserves zero morphisms for an invertible sheaf `L`. -/
theorem InvertibleSheaf.tensorRight_preservesZeroMorphisms (L : InvertibleSheaf X) :
    (tensorRight L.obj).PreservesZeroMorphisms := by
  obtain ⟨L', ⟨e⟩, ⟨e'⟩⟩ := L.exists_tensorInverse
  exact KltDP.Monoidal.tensorRight_preservesZeroMorphisms L.obj L' e e'

/-- **Tensoring a short exact sequence of sheaves of modules with an invertible sheaf gives a
short exact sequence.** -/
theorem InvertibleSheaf.shortExact_map_tensorRight (L : InvertibleSheaf X)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    letI := L.tensorRight_preservesZeroMorphisms
    (S.map (tensorRight L.obj)).ShortExact := by
  letI := L.tensorRight_preservesZeroMorphisms
  obtain ⟨L', ⟨e⟩, ⟨e'⟩⟩ := L.exists_tensorInverse
  exact KltDP.Monoidal.shortExact_map_tensorRight L.obj L' e e' S hS

/-- `− ⊗ L` preserves finite limits for an invertible sheaf `L`. -/
theorem InvertibleSheaf.tensorRight_preservesFiniteLimits (L : InvertibleSheaf X) :
    PreservesFiniteLimits (tensorRight L.obj) := by
  obtain ⟨L', ⟨e⟩, ⟨e'⟩⟩ := L.exists_tensorInverse
  exact KltDP.Monoidal.tensorRight_preservesFiniteLimits L.obj L' e e'

/-- `− ⊗ L` preserves finite colimits for an invertible sheaf `L`. -/
theorem InvertibleSheaf.tensorRight_preservesFiniteColimits (L : InvertibleSheaf X) :
    PreservesFiniteColimits (tensorRight L.obj) := by
  obtain ⟨L', ⟨e⟩, ⟨e'⟩⟩ := L.exists_tensorInverse
  exact KltDP.Monoidal.tensorRight_preservesFiniteColimits L.obj L' e e'

/-- The Cartier module `O_X(E)` has a tensor inverse (`cartierDivisorInvertibleSheaf`). -/
theorem cartierDivisorModule_exists_tensorInverse [IsIntegral X] (E : CartierDivisor X) :
    ∃ L' : X.Modules, Nonempty (cartierDivisorModule X E ⊗ L' ≅ 𝟙_ X.Modules) ∧
      Nonempty (L' ⊗ cartierDivisorModule X E ≅ 𝟙_ X.Modules) :=
  (cartierDivisorInvertibleSheaf X E).exists_tensorInverse

/-- **Tensoring a short exact sequence with `O_X(E)` gives a short exact sequence.** -/
theorem shortExact_map_tensorRight_cartierDivisorModule [IsIntegral X] (E : CartierDivisor X)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    letI : (tensorRight (cartierDivisorModule X E)).PreservesZeroMorphisms :=
      (cartierDivisorInvertibleSheaf X E).tensorRight_preservesZeroMorphisms
    (S.map (tensorRight (cartierDivisorModule X E))).ShortExact :=
  (cartierDivisorInvertibleSheaf X E).shortExact_map_tensorRight S hS

end KltDP.Geometry
