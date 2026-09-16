import KltDP.Geometry.OpenImmersionFunctionField
import KltDP.Geometry.CartierPrincipalModule

/-!
# Actual fractional coordinates under open restriction

The actual generic-stalk map identifies `g⁻¹ O_X(f(V))` with
`φ(g)⁻¹ O_Y(V)`. Both directions follow from the defining regular-section
criterion and the actual section-ring isomorphism of the open immersion.
The statement uses the existing principal fractional submodules and the
existing sign convention. No Cartier or line-bundle comparison is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : Y ⟶ X) [IsOpenImmersion f]

/-- The actual field map preserves and reflects the defining regular
section condition for a principal fractional module on an image open. -/
theorem functionFieldIso_mem_principalEquationSubmodule_image_iff
    (V : Y.Opens) [Nonempty V] (g : X.functionFieldˣ) (s : X.functionField) :
    letI := nonempty_image f V
    (functionFieldIso f).hom s ∈ principalEquationSubmodule Y V
        (Units.map (functionFieldIso f).hom.hom.toMonoidHom g) ↔
      s ∈ principalEquationSubmodule X (f ''ᵁ V) g := by
  letI := nonempty_image f V
  rw [mem_principalEquationSubmodule_iff, mem_principalEquationSubmodule_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(f.appIso V).inv a, ?_⟩
    apply (functionFieldIso f).commRingCatIsoToRingEquiv.injective
    change (functionFieldIso f).hom
        (X.germToFunctionField (f ''ᵁ V) ((f.appIso V).inv a)) =
      (functionFieldIso f).hom ((g : X.functionField) * s)
    rw [functionFieldIso_image_germ, Iso.inv_hom_id_apply, map_mul]
    exact ha
  · rintro ⟨a, ha⟩
    refine ⟨(f.appIso V).hom a, ?_⟩
    change Y.germToFunctionField V ((f.appIso V).hom a) =
      (functionFieldIso f).hom (g : X.functionField) * (functionFieldIso f).hom s
    rw [← functionFieldIso_image_germ, ha, map_mul]

end KltDP.Geometry.OpenImmersionRational
