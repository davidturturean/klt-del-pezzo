import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Maps.Basic

/-!
# Krull dimension of subspaces

An inducing map sends an irreducible closed subset to the closure of its
image. Taking the preimage recovers the original closed subset, so this
construction is an order embedding. Consequently topological Krull dimension
cannot increase on a subspace, including an open subspace.

No separation, Noetherianity, or scheme hypotheses are required.
-/

open TopologicalSpace Topology

universe u v

namespace KltDP.Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Closure of the image of an irreducible closed subset under a continuous
map is an irreducible closed subset of the target. -/
def irreducibleClosedsClosureMap (f : X → Y) (hf : Continuous f)
    (c : IrreducibleCloseds X) : IrreducibleCloseds Y where
  carrier := closure (f '' (c : Set X))
  is_irreducible' := (c.isIrreducible.image f hf.continuousOn).closure
  is_closed' := isClosed_closure

/-- An inducing map recovers a closed subset by pulling back the closure
of its image. This makes closure of images reflect inclusion. -/
theorem irreducibleClosedsClosureMap_le_iff (f : X → Y) (hf : IsInducing f)
    (c d : IrreducibleCloseds X) :
    irreducibleClosedsClosureMap f hf.continuous c ≤
      irreducibleClosedsClosureMap f hf.continuous d ↔ c ≤ d := by
  change closure (f '' (c : Set X)) ⊆ closure (f '' (d : Set X)) ↔
    (c : Set X) ⊆ (d : Set X)
  constructor
  · intro h
    calc
      (c : Set X) = f ⁻¹' closure (f '' (c : Set X)) :=
        c.isClosed.closure_eq.symm.trans (hf.closure_eq_preimage_closure_image _)
      _ ⊆ f ⁻¹' closure (f '' (d : Set X)) := Set.preimage_mono h
      _ = (d : Set X) :=
        (hf.closure_eq_preimage_closure_image _).symm.trans d.isClosed.closure_eq
  · intro h
    exact closure_mono (Set.image_mono h)

/-- Irreducible closed subsets of an induced topology embed in those of
the target by taking closure of images. -/
def irreducibleClosedsClosureOrderEmbedding (f : X → Y) (hf : IsInducing f) :
    IrreducibleCloseds X ↪o IrreducibleCloseds Y :=
  OrderEmbedding.ofMapLEIff (irreducibleClosedsClosureMap f hf.continuous)
    (irreducibleClosedsClosureMap_le_iff f hf)

/-- Topological Krull dimension is monotone under inducing maps. -/
theorem topologicalKrullDim_le_of_isInducing (f : X → Y) (hf : IsInducing f) :
    topologicalKrullDim X ≤ topologicalKrullDim Y :=
  Order.krullDim_le_of_strictMono (irreducibleClosedsClosureOrderEmbedding f hf)
    (irreducibleClosedsClosureOrderEmbedding f hf).strictMono

/-- In particular, a topological embedding cannot increase Krull dimension. -/
theorem topologicalKrullDim_le_of_isEmbedding (f : X → Y) (hf : IsEmbedding f) :
    topologicalKrullDim X ≤ topologicalKrullDim Y :=
  topologicalKrullDim_le_of_isInducing f hf.isInducing

/-- The Krull dimension bound for an open embedding. -/
theorem topologicalKrullDim_le_of_isOpenEmbedding (f : X → Y)
    (hf : IsOpenEmbedding f) :
    topologicalKrullDim X ≤ topologicalKrullDim Y :=
  topologicalKrullDim_le_of_isEmbedding f hf.isEmbedding

/-- The subspace topology on any subset has dimension at most the ambient
space. Openness is unnecessary for this inequality. -/
theorem topologicalKrullDim_subspace_le (s : Set X) :
    topologicalKrullDim s ≤ topologicalKrullDim X :=
  topologicalKrullDim_le_of_isInducing (Subtype.val : s → X) IsInducing.subtypeVal

/-- An open subset has dimension at most the ambient space. -/
theorem topologicalKrullDim_opens_le (U : Opens X) :
    topologicalKrullDim U ≤ topologicalKrullDim X :=
  topologicalKrullDim_subspace_le (U : Set X)

end KltDP.Topology
