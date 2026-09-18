import KltDP.Geometry.GenericFiberStalkIso
import KltDP.Geometry.DominantGenericPoint

/-! Ordinary integrality of the actual generic fiber of a dominant map
between integral schemes. The fiber is the original pullback over the
original residue field, with its original fiber-to-Spec structure map. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.GenericFiberIntegral

variable {X Y : Scheme.{u}} [IsIntegral Y]

theorem isReduced (f : X ⟶ Y) [IsReduced X] :
    IsReduced (f.fiber (genericPoint Y)) := by
  letI (x : f.fiber (genericPoint Y)) :
      _root_.IsReduced ((f.fiber (genericPoint Y)).presheaf.stalk x) :=
    isReduced_of_injective (GenericFiberStalkIso.stalkIso f x).inv.hom
      (GenericFiberStalkIso.stalkIso f x).symm.commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

theorem irreducibleSpace (f : X ⟶ Y) [IsIntegral X] [IsDominant f] :
    IrreducibleSpace (f.fiber (genericPoint Y)) := by
  have hη : genericPoint X ∈ Set.range (f.fiberι (genericPoint Y)).base := by
    rw [f.range_fiberι]
    change f.base (genericPoint X) = genericPoint Y
    exact (genericPointPreserving_of_isDominant f).base_genericPoint
  obtain ⟨z, hz⟩ := hη
  have hg : IsGenericPoint z (Set.univ : Set (f.fiber (genericPoint Y))) := by
    apply isGenericPoint_iff_specializes.mpr
    intro w
    simp only [Set.mem_univ, iff_true]
    apply (f.fiberι (genericPoint Y)).isEmbedding.isInducing.specializes_iff.mp
    rw [hz]
    exact (genericPoint_spec X).specializes trivial
  exact (irreducibleSpace_def _).mpr hg.isIrreducible

theorem isIntegral (f : X ⟶ Y) [IsIntegral X] [IsDominant f] :
    IsIntegral (f.fiber (genericPoint Y)) := by
  letI := isReduced f
  letI := irreducibleSpace f
  exact isIntegral_of_irreducibleSpace_of_isReduced _

#print axioms isIntegral

end KltDP.Geometry.GenericFiberIntegral
