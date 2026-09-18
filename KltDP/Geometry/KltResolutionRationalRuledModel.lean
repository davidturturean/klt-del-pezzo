import KltDP.Geometry.KltResolutionNegativeCanonical
import KltDP.Geometry.NegativeNefMinimalClassification
import KltDP.Geometry.ResolutionRationality
import KltDP.Geometry.ProjectiveSpaceAffineRationality
import KltDP.Geometry.RuledSurfaceSourceGeometry
import KltDP.Geometry.PointBlowupSequenceSurjective

/-!
# An original klt del Pezzo resolution produces a rational or ruled model

The original del Pezzo class supplies canonical negativity. Classification
of the resulting actual minimal model either proves rationality of the
original resolution source, or gives a ruling of the same target over a
proper projective regular curve. The literal composite from the original
resolution source is proper, surjective and over the unchanged base field.
No rationality or genus-zero assertion about the ruled base is assumed.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsResolution

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

/-- The same constructed model retains the original maps, actual ruled
fibres and section, and derived proper/projective geometry of its base. -/
theorem exists_rational_or_ruled_model_of_kltDelPezzo
    (hres : IsResolution S X π) (hDP : IsKltDelPezzo X) :
    ∃ (V : NormalProjectiveSurface k)
      (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
      (b : S.toScheme ⟶ V.toScheme),
      IsPointBlowupSequence S V b ∧
      b ≫ V.structureMorphism = S.structureMorphism ∧
      IsSmoothOfRelativeDimension 2 V.structureMorphism ∧
      V.picardRank ≤ S.picardRank ∧
      (Scheme.BirationalOver S.structureMorphism
          (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) ∨
        ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)),
          IsIntegral C ∧ LocallyOfFiniteType c ∧ QuasiCompact c ∧ IsSeparated c ∧
          IsProper c ∧ IsProjectiveOverField c ∧
          topologicalKrullDim C = 1 ∧ (∀ y : C, RegularPoint C y) ∧
          ∃ q : V.toScheme ⟶ C,
            q ≫ c = V.structureMorphism ∧ IsProper q ∧ Function.Surjective q.base ∧
            (∀ y : C, IsClosed ({y} : Set C) →
              ∃ e : q.fiber y ≅ projectiveSpace k 1,
                e.hom ≫ projectiveSpaceToSpec k 1 = q.fiberι y ≫ V.structureMorphism) ∧
            (b ≫ q) ≫ c = S.structureMorphism ∧ IsProper (b ≫ q) ∧
            Function.Surjective (b ≫ q).base ∧
            ∃ σ : C ⟶ V.toScheme, σ ≫ q = 𝟙 C) := by
  obtain ⟨K, eK, H, hH, hnegative⟩ := hres.exists_nef_canonical_negative_of_kltDelPezzo hDP
  obtain ⟨V, hV, b, hseq, hover, hsmooth, hrank, hclassification⟩ :=
    S.exists_rational_or_ruled_minimalModel_of_negative_nef hres.regular K eK H hH hnegative
  refine ⟨V, hV, b, hseq, hover, hsmooth, hrank, ?_⟩
  rcases hclassification with hrational | hruled
  · left
    have hresb : IsResolution S V b :=
      ⟨hover, hres.regular, (isBirational_iff_isBirationalScheme b).mpr hseq.isBirationalScheme⟩
    exact (ProjectiveChart.birationalOver_projectiveSpace_iff k 2 S.structureMorphism).mp
      (hresb.birationalOver.trans hrational)
  · right
    obtain ⟨C, c, hCintegral, hCfiniteType, hCquasiCompact, hCseparated,
      hCdim, hCregular, q, hbase, hsurj, hfibers, σ, hsection⟩ := hruled
    letI : IsIntegral C := hCintegral
    letI : LocallyOfFiniteType c := hCfiniteType
    letI : QuasiCompact c := hCquasiCompact
    letI : IsSeparated c := hCseparated
    have hproper : IsProper c := RuledSurfaceSourceGeometry.base_isProper V c q hbase hsurj
    have hprojective : IsProjectiveOverField c :=
      RuledSurfaceSourceGeometry.base_isProjective V c q hbase σ hsection
    letI : IsProper q := RuledSurfaceSourceGeometry.projection_isProper V c q hbase
    letI : IsProper b := hseq.isProper
    have hcomp : (b ≫ q) ≫ c = S.structureMorphism := by
      rw [Category.assoc, hbase, hover]
    have hsurjComp : Function.Surjective (b ≫ q).base := hsurj.comp hseq.surjective_base
    exact ⟨C, c, hCintegral, hCfiniteType, hCquasiCompact, hCseparated,
      hproper, hprojective, hCdim, hCregular, q, hbase, inferInstance, hsurj,
      hfibers, hcomp, inferInstance, hsurjComp, σ, hsection⟩

end KltDP.Geometry.IsResolution

#check @KltDP.Geometry.IsResolution.exists_rational_or_ruled_model_of_kltDelPezzo
#print axioms KltDP.Geometry.IsResolution.exists_rational_or_ruled_model_of_kltDelPezzo
