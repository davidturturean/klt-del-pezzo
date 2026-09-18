import Mathlib.AlgebraicGeometry.RationalMap

/-! The original generic restriction of a partial map is the restriction
of its original stalk map along the canonical generization. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.PartialMapStalkGenerization

theorem fromFunctionField {X Y : Scheme.{u}} [IrreducibleSpace X]
    (f : X.PartialMap Y) {x : X} (hx : x ∈ f.domain) :
    Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        f.fromSpecStalkOfMem hx = f.fromFunctionField := by
  have hgeneric : genericPoint X ∈ f.domain :=
    (genericPoint_specializes x).mem_open f.domain.isOpen hx
  have h :
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
          f.domain.fromSpecStalkOfMem x hx =
        f.domain.fromSpecStalkOfMem (genericPoint X) hgeneric := by
    apply (cancel_mono f.domain.ι).mp
    simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    change Spec.map (X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes trivial)) ≫ X.fromSpecStalk x = _
    exact Scheme.Spec_map_stalkSpecializes_fromSpecStalk _
  simpa only [Scheme.PartialMap.fromSpecStalkOfMem, ← Category.assoc]
    using congrArg (fun q => q ≫ f.hom) h

end KltDP.Geometry.PartialMapStalkGenerization
