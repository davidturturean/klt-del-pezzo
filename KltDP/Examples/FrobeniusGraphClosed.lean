import KltDP.Examples.FrobeniusProjectiveMorphism
import KltDP.Geometry.ProjectiveProper
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The actual closed graph and its projective-line isomorphism

The graph scheme is the categorical equalizer, inside the actual product
over `k`, of `fst ≫ projectivePowerMorphism` and `snd`. The pin already
proves that this equalizer inclusion is a closed immersion when its target
projective line is separated. Properness of the existing projective-line
structure morphism supplies that property here.

The inverse maps of the graph/projective-line isomorphism are the actual
first projection and the equalizer lift of the constructed graph morphism.
Their identities are proved with the pullback and equalizer universal
properties. No graph-existence or graph-isomorphism hypothesis is supplied.

Reuse: pinned `Morphisms/Separated.lean` (the separated-target equalizer
closed immersion) and `Limits/Shapes/Equalizers` (the equalizer lift and
its inclusion identity). The modern scheme-theoretic-image API is not
needed. This file does not calculate divisor classes or intersection lengths.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusGraphClosed

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusProjectiveMorphism

variable {k : Type u} [Field k]

abbrev firstProjection : projectiveProduct k ⟶ projectiveSpace k 1 :=
  pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)

abbrev secondProjection : projectiveProduct k ⟶ projectiveSpace k 1 :=
  pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)

theorem projectiveGraphMorphism_fst (p : ℕ) :
    projectiveGraphMorphism (k := k) p ≫ firstProjection = 𝟙 (projectiveSpace k 1) :=
  pullback.lift_fst _ _ _

theorem projectiveGraphMorphism_snd (p : ℕ) :
    projectiveGraphMorphism (k := k) p ≫ secondProjection = projectivePowerMorphism p :=
  pullback.lift_snd _ _ _

/-- The actual equalizer subscheme expressing `y=F(x)` in the product. -/
def graph (p : ℕ) : Scheme.{u} :=
  equalizer (firstProjection ≫ projectivePowerMorphism (k := k) p) secondProjection

/-- Its actual inclusion into the product. -/
def graphι (p : ℕ) : graph (k := k) p ⟶ projectiveProduct k :=
  equalizer.ι (firstProjection ≫ projectivePowerMorphism p) secondProjection

/-- The first projection restricted to the equalizer. -/
def graphToLine (p : ℕ) : graph (k := k) p ⟶ projectiveSpace k 1 :=
  graphι p ≫ firstProjection

/-- The actual graph morphism factors through the defining equalizer. -/
def lineToGraph (p : ℕ) : projectiveSpace k 1 ⟶ graph (k := k) p :=
  equalizer.lift (projectiveGraphMorphism p) (by
    rw [← Category.assoc, projectiveGraphMorphism_fst,
      Category.id_comp, projectiveGraphMorphism_snd])

theorem lineToGraph_ι (p : ℕ) :
    lineToGraph (k := k) p ≫ graphι p = projectiveGraphMorphism p :=
  equalizer.lift_ι _ _

theorem lineToGraph_graphToLine (p : ℕ) :
    lineToGraph (k := k) p ≫ graphToLine p = 𝟙 (projectiveSpace k 1) := by
  rw [graphToLine, ← Category.assoc, lineToGraph_ι, projectiveGraphMorphism_fst]

theorem graphToLine_lineToGraph (p : ℕ) :
    graphToLine (k := k) p ≫ lineToGraph p = 𝟙 (graph p) := by
  letI : Mono (graphι (k := k) p) := by
    change Mono
      (equalizer.ι (firstProjection ≫ projectivePowerMorphism (k := k) p) secondProjection)
    infer_instance
  apply (cancel_mono (graphι p)).mp
  rw [Category.id_comp, Category.assoc, lineToGraph_ι]
  apply pullback.hom_ext
  · simp only [Category.assoc, projectiveGraphMorphism_fst, Category.comp_id, graphToLine]
  · rw [Category.assoc, projectiveGraphMorphism_snd]
    simpa only [graphToLine, graphι, Category.assoc] using
      equalizer.condition (firstProjection ≫ projectivePowerMorphism (k := k) p)
        secondProjection

/-- The equalizer graph is isomorphic to the actual projective line. -/
def graphIsoProjectiveLine (p : ℕ) : graph (k := k) p ≅ projectiveSpace k 1 where
  hom := graphToLine p
  inv := lineToGraph p
  hom_inv_id := graphToLine_lineToGraph p
  inv_hom_id := lineToGraph_graphToLine p

/-- The existing projective-line structure map implies absolute separatedness. -/
theorem projectiveLine_isSeparated : (projectiveSpace k 1).IsSeparated := by
  constructor
  rw [← terminal.comp_from (projectiveSpaceToSpec k 1)]
  infer_instance

/-- The equalizer is an actual closed subscheme of the product. -/
instance graphι_isClosedImmersion (p : ℕ) : IsClosedImmersion (graphι (k := k) p) := by
  letI := projectiveLine_isSeparated (k := k)
  change IsClosedImmersion
    (equalizer.ι (firstProjection ≫ projectivePowerMorphism (k := k) p) secondProjection)
  infer_instance

/-- Under its explicit isomorphism with the projective line, the inclusion is
exactly the previously constructed graph morphism. -/
theorem graphIso_inv_ι (p : ℕ) :
    (graphIsoProjectiveLine (k := k) p).inv ≫ graphι p = projectiveGraphMorphism p :=
  lineToGraph_ι p

/-- The constructed global graph morphism itself is a closed immersion. -/
instance projectiveGraphMorphism_isClosedImmersion (p : ℕ) :
    IsClosedImmersion (projectiveGraphMorphism (k := k) p) := by
  rw [← graphIso_inv_ι p]
  infer_instance

/-- Its underlying graph is a genuinely closed subset of the scheme product. -/
theorem projectiveGraphMorphism_isClosed_range (p : ℕ) :
    IsClosed (Set.range (projectiveGraphMorphism (k := k) p).base) :=
  (projectiveGraphMorphism p).isClosedEmbedding.isClosed_range

end KltDP.Examples.FrobeniusGraphClosed
