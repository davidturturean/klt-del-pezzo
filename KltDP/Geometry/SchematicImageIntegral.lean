import KltDP.Geometry.SchematicImageGlued
import KltDP.Geometry.SchematicImageDenseOpen
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The actual schematic image of an integral source

For a quasi-compact original morphism the kernel support is the closure
of its actual range. That closure is irreducible. The original closed
inclusion identifies the quotient-glued scheme with this topological
subspace, and the existing radical-kernel theorem supplies reducedness.
The source morphism need not be proper, as required for rational maps
on their actual non-base opens.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.SchematicImageIntegral

variable {X Y : Scheme.{u}} [IsIntegral X] (g : X ⟶ Y) [QuasiCompact g]

/-- The original closed image inclusion has the closure of the original range. -/
theorem range_inclusion :
    Set.range (SchematicImageGlued.inclusion g).base = closure (Set.range g.base) := by
  rw [Scheme.IdealSheafData.range_gluedTo, Scheme.Hom.support_ker]

/-- The support of the original quotient-glued image is irreducible. -/
theorem range_inclusion_isIrreducible :
    IsIrreducible (Set.range (SchematicImageGlued.inclusion g).base) := by
  rw [range_inclusion g]
  have h := (IrreducibleSpace.isIrreducible_univ X).image g.base g.continuous.continuousOn
  simpa only [Set.image_univ] using h.closure

/-- The original schematic image is integral without a properness assumption on the map. -/
theorem image_isIntegral : IsIntegral (SchematicImageGlued.image g) := by
  letI : IsReduced (SchematicImageGlued.image g) :=
    SchematicImageDenseOpen.image_glued_isReduced g
  letI : IrreducibleSpace (Set.range (SchematicImageGlued.inclusion g).base) :=
    Subtype.irreducibleSpace (range_inclusion_isIrreducible g)
  let e := (SchematicImageGlued.inclusion g).isClosedEmbedding.isEmbedding.toHomeomorph
  haveI : IrreducibleSpace (SchematicImageGlued.image g) := by
    apply (irreducibleSpace_def (SchematicImageGlued.image g)).mpr
    have h := (IrreducibleSpace.isIrreducible_univ
      (Set.range (SchematicImageGlued.inclusion g).base)).image
        e.symm e.symm.continuous.continuousOn
    simpa only [Set.image_univ, e.symm.surjective.range_eq] using h
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end KltDP.Geometry.SchematicImageIntegral
