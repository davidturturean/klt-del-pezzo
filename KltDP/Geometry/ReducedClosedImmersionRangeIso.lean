import KltDP.Geometry.SchematicImageToImageIso

/-!
# The actual isomorphism of two reduced closed subschemes with the same range

Reducedness identifies each original kernel with the vanishing ideal of
its support. Equal ranges therefore give equal actual kernel ideal sheaves,
and the accepted schematic-image comparison supplies the isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ReducedClosedImmersionRangeIso

variable {X Y Z : Scheme.{u}} [IsReduced X] [IsReduced Y]
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion f] [IsClosedImmersion g]
    (h : Set.range f.base = Set.range g.base)

include h in
theorem ker_eq : f.ker = g.ker := by
  have hs : f.ker.support = g.ker.support := by
    apply SetLike.coe_injective
    simpa only [Scheme.Hom.support_ker] using congrArg closure h
  calc
    f.ker = f.ker.radical := (SchematicImageDenseOpen.ker_radical f).symm
    _ = Scheme.IdealSheafData.vanishingIdeal f.ker.support :=
      Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = Scheme.IdealSheafData.vanishingIdeal g.ker.support := by rw [hs]
    _ = g.ker.radical := Scheme.IdealSheafData.vanishingIdeal_support
    _ = g.ker := SchematicImageDenseOpen.ker_radical g

/-- The actual reduced closed subschemes are isomorphic over the same ambient scheme. -/
def iso : X ≅ Y := SchematicImageToImageIso.isoOfKerEq f g (ker_eq f g h)

/-- The original inclusions, rather than just their underlying ranges, agree. -/
theorem iso_hom_comp : (iso f g h).hom ≫ g = f :=
  SchematicImageToImageIso.isoOfKerEq_hom f g (ker_eq f g h)

end KltDP.Geometry.ReducedClosedImmersionRangeIso
