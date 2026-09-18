import KltDP.Geometry.ClosedPoints
import KltDP.Geometry.PrimeCurveOfClosedImmersion
import KltDP.Geometry.PrimeCurveInclusionLift
import KltDP.Geometry.ProjectiveProper
import Mathlib.AlgebraicGeometry.Fiber

/-!
# The original section and closed fibres of a ruled surface

The section and scheme-theoretic fibres are represented by the actual prime
curves of the original surface, with isomorphisms commuting with their
inclusions. No representation of a section or fibre is assumed. Properness
of the original base follows from the original projective-source surjection.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RuledSurfaceSourceGeometry

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    (π : X.toScheme ⟶ C) (hbase : π ≫ c = X.structureMorphism)

include hbase in
/-- The original projection is proper over the separated original base. -/
theorem projection_isProper [IsSeparated c] : IsProper π := by
  letI : IsProper (π ≫ c) := by
    rw [hbase]
    infer_instance
  exact IsProper.of_comp_of_isSeparated π c

include hbase in
/-- A finite-type separated target of the original projective-source
surjection is proper over the original field. -/
theorem base_isProper [LocallyOfFiniteType c] [IsSeparated c]
    (hsurj : Function.Surjective π.base) : IsProper c := by
  letI : Surjective π := ⟨hsurj⟩
  letI : UniversallyClosed (π ≫ c) := by
    rw [hbase]
    infer_instance
  letI : UniversallyClosed c := UniversallyClosed.of_comp_surjective π c
  exact ⟨⟩

include hbase in
/-- The specified section is an actual closed immersion. -/
theorem section_isClosedImmersion [IsSeparated c]
    (σ : C ⟶ X.toScheme) (hσ : σ ≫ π = 𝟙 C) : IsClosedImmersion σ := by
  letI : IsProper π := projection_isProper X c π hbase
  letI : IsClosedImmersion (σ ≫ π) := by
    rw [hσ]
    infer_instance
  exact IsClosedImmersion.of_comp σ π

include hbase in
/-- The original section embeds the original base in the same projective
space as the surface. This supplies the source's projective-curve dictionary. -/
theorem base_isProjective [IsSeparated c]
    (σ : C ⟶ X.toScheme) (hσ : σ ≫ π = 𝟙 C) : IsProjectiveOverField c := by
  letI : IsClosedImmersion σ := section_isClosedImmersion X c π hbase σ hσ
  obtain ⟨n, i, hi, hfactor⟩ := X.projective
  letI : IsClosedImmersion i := hi
  refine ⟨n, σ ≫ i, inferInstance, ?_⟩
  rw [Category.assoc, hfactor, ← hbase, ← Category.assoc, hσ, Category.id_comp]

/-- The literal scheme-theoretic fibre inclusion at a closed point is closed. -/
theorem fiberInclusion_isClosedImmersion (y : C) (hy : IsClosed ({y} : Set C)) :
    IsClosedImmersion (π.fiberι y) := by
  letI : IsClosedImmersion (C.fromSpecResidueField y) :=
    fromSpecResidueField_isClosedImmersion C y hy
  exact MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

include hbase in
/-- The specified section has its original prime-curve representation. Both
the inclusion and the structure map commute with the constructed isomorphism. -/
theorem exists_sectionPrimeCurve [IsIntegral C] [IsSeparated c]
    (hCdim : topologicalKrullDim C = 1)
    (σ : C ⟶ X.toScheme) (hσ : σ ≫ π = 𝟙 C) :
    ∃ (S₀ : X.PrimeCurve) (e₀ : S₀.toScheme ≅ C),
      e₀.inv ≫ S₀.inclusion = σ ∧
      e₀.hom ≫ c = S₀.inclusion ≫ X.structureMorphism ∧
      (S₀ : Set X.toScheme) = Set.range σ.base := by
  letI : IsClosedImmersion σ := section_isClosedImmersion X c π hbase σ hσ
  have hdim : topologicalKrullDim (Set.range σ.base) = 1 := by
    calc
      topologicalKrullDim (Set.range σ.base) = topologicalKrullDim C :=
        (IsHomeomorph.topologicalKrullDim_eq _
          σ.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm
      _ = 1 := hCdim
  let S₀ : X.PrimeCurve :=
    ⟨⟨Set.range σ.base, PrimeCurveOfClosedImmersion.range_isIrreducible X σ,
      PrimeCurveOfClosedImmersion.range_isClosed X σ⟩, hdim⟩
  let e₀ : S₀.toScheme ≅ C :=
    (asIso (PrimeCurveInclusionLift.lift S₀ σ rfl)).symm
  have hinv : e₀.inv ≫ S₀.inclusion = σ :=
    PrimeCurveInclusionLift.lift_inclusion S₀ σ rfl
  have hhom : e₀.hom ≫ σ = S₀.inclusion :=
    (PrimeCurveInclusionLift.inclusion_eq_inv_lift S₀ σ rfl).symm
  have hσbase : σ ≫ X.structureMorphism = c := by
    rw [← hbase, ← Category.assoc, hσ, Category.id_comp]
  refine ⟨S₀, e₀, hinv, ?_, rfl⟩
  calc
    e₀.hom ≫ c = e₀.hom ≫ (σ ≫ X.structureMorphism) := by rw [hσbase]
    _ = S₀.inclusion ≫ X.structureMorphism := by rw [← Category.assoc, hhom]

/-- A specified original closed scheme fibre is represented by its original
prime curve. The fibre isomorphism over `k` and literal point-fibre support
are preserved. -/
theorem exists_fiberPrimeCurve (y : C) (hy : IsClosed ({y} : Set C))
    (e : π.fiber y ≅ projectiveSpace k 1)
    (he : e.hom ≫ projectiveSpaceToSpec k 1 = π.fiberι y ≫ X.structureMorphism) :
    ∃ (F : X.PrimeCurve) (eF : F.toScheme ≅ π.fiber y),
      eF.hom ≫ π.fiberι y = F.inclusion ∧
      (eF ≪≫ e).hom ≫ projectiveSpaceToSpec k 1 =
        F.inclusion ≫ X.structureMorphism ∧
      (F : Set X.toScheme) = π.base ⁻¹' {y} := by
  letI : IsClosedImmersion (π.fiberι y) := fiberInclusion_isClosedImmersion X π y hy
  letI : IsIntegral (π.fiber y) := PrimeCurveOfClosedImmersion.isIntegral_of_iso_projectiveLine e
  let F := PrimeCurveOfClosedImmersion.primeCurveOfIsoProjectiveLine X (π.fiberι y) e
  let eF : F.toScheme ≅ π.fiber y :=
    (asIso (PrimeCurveInclusionLift.lift F (π.fiberι y) rfl)).symm
  have hF : eF.hom ≫ π.fiberι y = F.inclusion :=
    (PrimeCurveInclusionLift.inclusion_eq_inv_lift F (π.fiberι y) rfl).symm
  refine ⟨F, eF, hF, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, he, ← Category.assoc, hF]
  · exact π.range_fiberι y

end KltDP.Geometry.RuledSurfaceSourceGeometry
