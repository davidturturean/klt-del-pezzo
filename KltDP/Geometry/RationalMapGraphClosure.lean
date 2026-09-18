import KltDP.Geometry.SchematicImageGenericPoint
import KltDP.Geometry.DominantOpenSection
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.RationalMap

/-!
# A proper graph modification for an original partial map

For an actual partial map from an integral Noetherian `T` to a scheme proper
over `X`, its graph in `T ×[X] V` has the existing quotient-glued kernel image.
The first projection from this actual image is proper and is an isomorphism
over the original domain. The second projection extends precisely the given
partial map and the original equation over `X`.

The input equation only says that the supplied partial map is over `X`.
The graph, its modification, and all their compatibilities are constructed.
No finite bad locus or point-blowup domination is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.RationalMapGraphClosure

variable {T V X : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
  (t : T ⟶ X) (v : V ⟶ X) [IsProper v]
  (φ : T.PartialMap V) (hφ : φ.hom ≫ v = φ.domain.ι ≫ t)

private instance domain_nonempty : Nonempty φ.domain := by
  obtain ⟨x, hx⟩ := φ.dense_domain.nonempty
  exact ⟨⟨x, hx⟩⟩

private instance domain_integral : IsIntegral φ.domain.toScheme :=
  isIntegral_of_isOpenImmersion φ.domain.ι

private instance domain_noetherianSpace : NoetherianSpace φ.domain.toScheme :=
  φ.domain.ι.isOpenEmbedding.isInducing.noetherianSpace

/-- The original partial graph in the original fibre product. -/
def graphMap : φ.domain.toScheme ⟶ pullback t v :=
  pullback.lift φ.domain.ι φ.hom hφ.symm

private instance graphMap_quasiCompact : QuasiCompact (graphMap t v φ hφ) :=
  quasiCompact_of_noetherianSpace_source _

@[reassoc]
theorem graphMap_fst : graphMap t v φ hφ ≫ pullback.fst t v = φ.domain.ι :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem graphMap_snd : graphMap t v φ hφ ≫ pullback.snd t v = φ.hom :=
  pullback.lift_snd _ _ _

/-- The actual closed kernel image of the original partial graph. -/
abbrev model : Scheme.{u} := SchematicImageGlued.image (graphMap t v φ hφ)

instance model_isIntegral : IsIntegral (model t v φ hφ) :=
  SchematicImageIntegral.image_isIntegral (graphMap t v φ hφ)

/-- Projection to the original source. -/
def projection : model t v φ hφ ⟶ T :=
  SchematicImageGlued.inclusion (graphMap t v φ hφ) ≫ pullback.fst t v

/-- The actual extension to the original target. -/
def extension : model t v φ hφ ⟶ V :=
  SchematicImageGlued.inclusion (graphMap t v φ hφ) ≫ pullback.snd t v

/-- The original domain maps to its graph image. -/
def domainLift : φ.domain.toScheme ⟶ model t v φ hφ :=
  SchematicImageGlued.toImage (graphMap t v φ hφ)

instance projection_isProper : IsProper (projection t v φ hφ) := by
  letI : IsClosedImmersion (SchematicImageGlued.inclusion (graphMap t v φ hφ)) :=
    SchematicImageGlued.inclusion_isClosedImmersion (graphMap t v φ hφ)
  letI : IsProper (SchematicImageGlued.inclusion (graphMap t v φ hφ)) := inferInstance
  letI : IsProper (pullback.fst t v) :=
    MorphismProperty.pullback_fst (P := @IsProper) t v inferInstance
  exact MorphismProperty.comp_mem (@IsProper)
    (SchematicImageGlued.inclusion (graphMap t v φ hφ)) (pullback.fst t v)
    inferInstance inferInstance

theorem extension_comp : extension t v φ hφ ≫ v = projection t v φ hφ ≫ t := by
  dsimp only [extension, projection]
  rw [Category.assoc, Category.assoc, pullback.condition]

@[reassoc]
theorem domainLift_projection : domainLift t v φ hφ ≫ projection t v φ hφ = φ.domain.ι := by
  dsimp only [domainLift, projection]
  rw [← Category.assoc, SchematicImageGlued.toImage_inclusion, graphMap_fst]

@[reassoc]
theorem domainLift_extension : domainLift t v φ hφ ≫ extension t v φ hφ = φ.hom := by
  dsimp only [domainLift, extension]
  rw [← Category.assoc, SchematicImageGlued.toImage_inclusion, graphMap_snd]

/-- The original domain is dense in its actual graph image. -/
instance domainLift_isDominant : IsDominant (domainLift t v φ hφ) := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff,
    ← (genericPoint_spec (model t v φ hφ)).def]
  apply closure_mono
  rw [Set.singleton_subset_iff]
  exact ⟨genericPoint φ.domain.toScheme,
    SchematicImageIntegral.toImage_map_genericPoint (graphMap t v φ hφ)⟩

/-- The proper graph projection is an isomorphism over the original domain. -/
theorem projection_restrict_isIso : IsIso (projection t v φ hφ ∣_ φ.domain) :=
  DominantOpenSection.isIso_restrict_of_dominant_section (projection t v φ hφ)
    φ.domain (domainLift t v φ hφ) (domainLift_projection t v φ hφ)

/-- The original domain lift, with codomain restricted to that domain's preimage. -/
def domainComparison : φ.domain.toScheme ⟶ ((projection t v φ hφ) ⁻¹ᵁ φ.domain).toScheme :=
  (isPullback_morphismRestrict (projection t v φ hφ) φ.domain).lift
    (𝟙 _) (domainLift t v φ hφ)
    (by simpa only [Category.id_comp] using (domainLift_projection t v φ hφ).symm)

theorem domainComparison_restrict :
    domainComparison t v φ hφ ≫ (projection t v φ hφ ∣_ φ.domain) = 𝟙 _ :=
  (isPullback_morphismRestrict (projection t v φ hφ) φ.domain).lift_fst _ _ _

@[reassoc]
theorem domainComparison_inclusion :
    domainComparison t v φ hφ ≫ ((projection t v φ hφ) ⁻¹ᵁ φ.domain).ι =
      domainLift t v φ hφ :=
  (isPullback_morphismRestrict (projection t v φ hφ) φ.domain).lift_snd _ _ _

/-- The restriction isomorphism retains the original domain lift. -/
def domainIso : φ.domain.toScheme ≅ ((projection t v φ hφ) ⁻¹ᵁ φ.domain).toScheme := by
  letI := projection_restrict_isIso t v φ hφ
  letI : IsIso (domainComparison t v φ hφ ≫ (projection t v φ hφ ∣_ φ.domain)) := by
    rw [domainComparison_restrict]
    infer_instance
  letI : IsIso (domainComparison t v φ hφ) :=
    IsIso.of_isIso_comp_right (domainComparison t v φ hφ) (projection t v φ hφ ∣_ φ.domain)
  exact asIso (domainComparison t v φ hφ)

/-- Under the constructed domain isomorphism, the extension is the original partial map. -/
theorem domainIso_hom_extension :
    (domainIso t v φ hφ).hom ≫ ((projection t v φ hφ) ⁻¹ᵁ φ.domain).ι ≫
      extension t v φ hφ = φ.hom := by
  change domainComparison t v φ hφ ≫ _ ≫ _ = _
  rw [domainComparison_inclusion_assoc, domainLift_extension]

include hφ in
/-- An actual proper modification and extension, with all original equations. -/
theorem exists_proper_extension :
    ∃ (G : Scheme.{u}) (p : G ⟶ T) (q : G ⟶ V) (j : φ.domain.toScheme ⟶ G),
      IsIntegral G ∧ IsProper p ∧ IsIso (p ∣_ φ.domain) ∧
      j ≫ p = φ.domain.ι ∧ j ≫ q = φ.hom ∧ q ≫ v = p ≫ t :=
  ⟨model t v φ hφ, projection t v φ hφ, extension t v φ hφ, domainLift t v φ hφ,
    inferInstance, inferInstance, projection_restrict_isIso t v φ hφ,
    domainLift_projection t v φ hφ, domainLift_extension t v φ hφ,
    extension_comp t v φ hφ⟩

end KltDP.Geometry.RationalMapGraphClosure
