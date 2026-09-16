import KltDP.Geometry.SchematicImageDenseOpen
import KltDP.Geometry.SchematicImageGlued
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Kernels of reduced-source morphisms and their base change along open immersions

For a quasi-compact morphism `f : Y ⟶ X` from a reduced scheme, the kernel ideal sheaf is radical
(accepted `ker_radical`) with support the closure of the range (pinned `support_ker`), hence it is the
vanishing ideal of that closure (`ker_eq_vanishingIdeal_rangeClosure`). Consequently two such morphisms
with the same closure of range have the same kernel and literally the same glued schematic image
(`ker_eq_of_closure_range_eq`, `imageIsoOfKerEq`, compatible with the inclusions).

For an open immersion `j : U ⟶ X`, the base change `openBaseChange f j = pullback.fst j f : U ×_X Y ⟶ U`
has range `j⁻¹(range f)` (pinned `Scheme.Pullback.range_fst`) and, `j` being an open embedding, closure of
range `j⁻¹(closure (range f))`; so its kernel is the vanishing ideal of the preimage of the support of
`f.ker` (`ker_openBaseChange`, `support_ker_openBaseChange`): the schematic image commutes with open
base change at the level of (radical) ideal sheaves. Two base changes with equal preimage closures have
equal kernels (`ker_openBaseChange_eq`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Geometry.SchematicImageOpenBaseChange

variable {X X' Y Y' U : Scheme.{u}}

/-- The closure of the range of a morphism, as a closed subset. -/
def rangeClosure (f : Y ⟶ X) : Closeds X := ⟨closure (Set.range f.base), isClosed_closure⟩

theorem coe_rangeClosure (f : Y ⟶ X) : (rangeClosure f : Set X) = closure (Set.range f.base) := rfl

theorem ker_support_eq (f : Y ⟶ X) [QuasiCompact f] : f.ker.support = rangeClosure f :=
  Closeds.ext (Scheme.Hom.support_ker f)

/-- **Reduced-source kernels are vanishing ideals**: the kernel of a quasi-compact morphism from a
reduced scheme is the vanishing ideal of the closure of its range. -/
theorem ker_eq_vanishingIdeal_rangeClosure (f : Y ⟶ X) [QuasiCompact f] [IsReduced Y] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (rangeClosure f) := by
  rw [← ker_support_eq f, Scheme.IdealSheafData.vanishingIdeal_support,
    SchematicImageDenseOpen.ker_radical]

/-- Two quasi-compact morphisms from reduced schemes with the same closure of range have the same
kernel. -/
theorem ker_eq_of_closure_range_eq (f : Y ⟶ X) (g : Y' ⟶ X) [QuasiCompact f] [QuasiCompact g]
    [IsReduced Y] [IsReduced Y'] (h : closure (Set.range f.base) = closure (Set.range g.base)) :
    f.ker = g.ker := by
  rw [ker_eq_vanishingIdeal_rangeClosure f, ker_eq_vanishingIdeal_rangeClosure g]
  exact congrArg _ (Closeds.ext h)

theorem gluedTo_eqToHom {I J : X.IdealSheafData} (h : I = J) :
    eqToHom (congrArg (fun K : X.IdealSheafData => K.glueData.glued) h) ≫ J.gluedTo = I.gluedTo := by
  subst h
  exact Category.id_comp _

/-- Equal kernels give literally the same glued image. -/
def imageIsoOfKerEq (f : Y ⟶ X) (g : Y' ⟶ X) (h : f.ker = g.ker) :
    SchematicImageGlued.image f ≅ SchematicImageGlued.image g :=
  eqToIso (congrArg (fun I : X.IdealSheafData => I.glueData.glued) h)

@[reassoc] theorem imageIsoOfKerEq_hom_inclusion (f : Y ⟶ X) (g : Y' ⟶ X) (h : f.ker = g.ker) :
    (imageIsoOfKerEq f g h).hom ≫ SchematicImageGlued.inclusion g =
      SchematicImageGlued.inclusion f :=
  gluedTo_eqToHom h

/-! ## Base change along an open immersion -/

variable (f : Y ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]

/-- The base change of `f` along the open immersion `j`. -/
abbrev openBaseChange : pullback j f ⟶ U := pullback.fst j f

omit [IsOpenImmersion j] in
theorem range_openBaseChange :
    Set.range (openBaseChange f j).base = j.base ⁻¹' Set.range f.base :=
  Scheme.Pullback.range_fst j f

theorem closure_range_openBaseChange :
    closure (Set.range (openBaseChange f j).base) = j.base ⁻¹' closure (Set.range f.base) := by
  rw [range_openBaseChange]
  exact (j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    j.isOpenEmbedding.continuous _).symm

/-- The preimage of a closed subset along the open immersion. -/
def preimageCloseds (Z : Closeds X) : Closeds U :=
  ⟨j.base ⁻¹' Z, Z.isClosed.preimage j.isOpenEmbedding.continuous⟩

theorem rangeClosure_openBaseChange :
    rangeClosure (openBaseChange f j) = preimageCloseds j (rangeClosure f) :=
  Closeds.ext (closure_range_openBaseChange f j)

instance openBaseChange_source_isReduced [IsReduced Y] : IsReduced (pullback j f) :=
  isReduced_of_isOpenImmersion (pullback.snd j f)

/-- **Kernel of the base change**: for a reduced source, the kernel of `f ×_X U ⟶ U` is the vanishing
ideal of the preimage of the closure of the range of `f`. -/
theorem ker_openBaseChange [QuasiCompact f] [IsReduced Y] :
    (openBaseChange f j).ker =
      Scheme.IdealSheafData.vanishingIdeal (preimageCloseds j (rangeClosure f)) := by
  rw [ker_eq_vanishingIdeal_rangeClosure, rangeClosure_openBaseChange]

/-- The support of the kernel of the base change is the preimage of the support of the kernel. -/
theorem support_ker_openBaseChange [QuasiCompact f] [IsReduced Y] :
    (openBaseChange f j).ker.support = preimageCloseds j f.ker.support := by
  rw [ker_support_eq, ker_support_eq, rangeClosure_openBaseChange]

/-- Two base changes along open immersions into a common open scheme, with the same preimage of the
closure of range, have the same kernel. -/
theorem ker_openBaseChange_eq (g : Y' ⟶ X') (j' : U ⟶ X') [IsOpenImmersion j'] [QuasiCompact f]
    [QuasiCompact g] [IsReduced Y] [IsReduced Y']
    (h : j.base ⁻¹' closure (Set.range f.base) = j'.base ⁻¹' closure (Set.range g.base)) :
    (openBaseChange f j).ker = (openBaseChange g j').ker := by
  rw [ker_openBaseChange, ker_openBaseChange]
  exact congrArg _ (Closeds.ext h)

end KltDP.Geometry.SchematicImageOpenBaseChange
