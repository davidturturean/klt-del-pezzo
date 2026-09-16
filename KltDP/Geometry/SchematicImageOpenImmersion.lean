import KltDP.Geometry.SchematicImageDenseOpen

/-!
# Schematic image kernels and actual open-immersion source charts

The pinned open-immersion isomorphism onto its open range reduces the
statement to the existing nonempty-open kernel theorem. Precomposition
by that actual isomorphism does not change the kernel because each of
its section maps is an isomorphism. No quasi-compactness or schematic
density hypothesis is inserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchematicImageOpenImmersion

variable {X Y Z : Scheme.{u}}

/-- An actual source isomorphism leaves the kernel ideal sheaf unchanged. -/
theorem ker_precompose_iso (e : Z ≅ X) (f : X ⟶ Y) :
    (e.hom ≫ f).ker = f.ker := by
  unfold Scheme.Hom.ker
  apply congrArg Scheme.IdealSheafData.ofIdeals
  funext V
  rw [Scheme.comp_app, CommRingCat.hom_comp]
  exact RingHom.ker_comp_of_injective (f.app V).hom
    (asIso (e.hom.app (f ⁻¹ᵁ V))).commRingCatIsoToRingEquiv.injective

/-- An actual nonempty open-immersion source chart of an integral scheme
has precisely the same kernel ideal sheaf after any morphism. -/
theorem ker_precompose_openImmersion [IsIntegral X] (j : Z ⟶ X)
    [IsOpenImmersion j] [Nonempty Z] (f : X ⟶ Y) :
    (j ≫ f).ker = f.ker := by
  let z : Z := Classical.choice inferInstance
  letI : Nonempty j.opensRange := ⟨⟨j.base z, ⟨z, rfl⟩⟩⟩
  calc
    (j ≫ f).ker = (j.isoOpensRange.hom ≫ (j.opensRange.ι ≫ f)).ker := by
      rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    _ = (j.opensRange.ι ≫ f).ker := ker_precompose_iso _ _
    _ = f.ker := SchematicImageDenseOpen.ker_precompose_open _ _

end KltDP.Geometry.SchematicImageOpenImmersion
