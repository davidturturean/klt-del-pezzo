import KltDP.Examples.FrobeniusMultiCentreNormal

/-!
# `S_{p,n}` is integral, of dimension two, and a normal projective surface (given projectivity)

For distinct parameters `a` over an algebraically closed field, lane F's multi-centre surface
`multiSurface p m a` is integral (`multiSurface_isIntegral`) and has Krull dimension two
(`multiSurface_topologicalKrullDim`); with the explicit projectivity hypothesis `hproj` it is a
`NormalProjectiveSurface k` (`multiSurfaceSurface`).

Route (the same two-open base-change cover as lane F's smoothness and this lane's normality): each
piece is an open subscheme of the earlier surface or of the tower, hence integral once nonempty; the
two pieces meet over a point of the product avoiding all centres (a graph point `(c, c^p)` with `c`
outside the finite parameter set — an algebraically closed field is infinite), which lifts to both
factors (`multiProjection`, `selectedProjection` are isomorphisms over the respective complements)
and hence to the fibre product (pinned `exists_preimage_pullback`). Reducedness descends stalkwise
along the cover, irreducibility is the union of two irreducible opens with a common point
(`irreducibleSpace_of_two_irreducible_opens`). Dimension two then follows from the accepted
`topologicalKrullDim_eq_of_proper_isomorphism_open` for the proper `multiProjection`, an isomorphism
over the nonempty complement of all centres.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreIntegral

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGlobalBlowupStages
open FrobeniusStageComplement FrobeniusStageComplement.PlaneChartedScheme
open FrobeniusBlowupChartIteration FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint FrobeniusMultiCentreSurface
open FrobeniusStageNormal FrobeniusStageDimension FrobeniusSelectedStageSurface
open FrobeniusMultiCentreNormal FrobeniusTowerFunctionField.PlaneChartedScheme

/-- A space covered by two irreducible open subsets with a common point is irreducible. -/
theorem irreducibleSpace_of_two_irreducible_opens {X : Type*} [TopologicalSpace X]
    {R₁ R₂ : Set X} (h₁ : IsIrreducible R₁) (h₂ : IsIrreducible R₂) (ho₁ : IsOpen R₁)
    (ho₂ : IsOpen R₂) (hcover : ∀ x, x ∈ R₁ ∨ x ∈ R₂) {z : X} (hz₁ : z ∈ R₁) (hz₂ : z ∈ R₂) :
    IrreducibleSpace X := by
  apply (irreducibleSpace_def X).mpr
  refine ⟨⟨z, trivial⟩, ?_⟩
  intro O₁ O₂ hO₁ hO₂ hn₁ hn₂
  obtain ⟨x, _, hx⟩ := hn₁
  obtain ⟨y, _, hy⟩ := hn₂
  have key : ∀ (R R' : Set X), IsIrreducible R → IsIrreducible R' → IsOpen R' →
      z ∈ R → z ∈ R' → x ∈ R → y ∈ R' → (Set.univ ∩ (O₁ ∩ O₂)).Nonempty := by
    intro R R' hR hR' hoR' hzR hzR' hxR hyR'
    obtain ⟨t, htR, htO₁, htR'⟩ := hR.2 O₁ R' hO₁ hoR' ⟨x, hxR, hx⟩ ⟨z, hzR, hzR'⟩
    obtain ⟨w, _, hwO₁, hwO₂⟩ := hR'.2 O₁ O₂ hO₁ hO₂ ⟨t, htR', htO₁⟩ ⟨y, hyR', hy⟩
    exact ⟨w, trivial, hwO₁, hwO₂⟩
  rcases hcover x with hx₁ | hx₂ <;> rcases hcover y with hy₁ | hy₂
  · exact key R₁ R₁ h₁ h₁ ho₁ hz₁ hz₁ hx₁ hy₁
  · exact key R₁ R₂ h₁ h₂ ho₂ hz₁ hz₂ hx₁ hy₂
  · exact key R₂ R₁ h₂ h₁ ho₁ hz₂ hz₁ hx₂ hy₁
  · exact key R₂ R₂ h₂ h₂ ho₂ hz₂ hz₂ hx₂ hy₂

variable {k : Type u} [Field k]

section pieces

variable {S T : Scheme.{u}} (f : S ⟶ projectiveProduct k) (g : T ⟶ projectiveProduct k)

/-- A point of the fibre product lying over `U` is in the image of the base-change piece over `U`. -/
theorem mem_range_pieceMap (U : (projectiveProduct k).Opens) (z : (pullback f g : Scheme.{u}))
    (hz : f.base ((pullback.fst f g).base z) ∈ U) :
    z ∈ Set.range (pullback.map (pullback.snd f U.ι) (pullback.snd g U.ι) f g
      (pullback.fst _ _) (pullback.fst _ _) U.ι
      pullback.condition.symm pullback.condition.symm).base := by
  have hg : g.base ((pullback.snd f g).base z) ∈ U := by
    have h := congrArg (fun φ : (pullback f g : Scheme.{u}) ⟶ projectiveProduct k => φ.base z)
      (pullback.condition (f := f) (g := g))
    simp only [Scheme.comp_base_apply] at h
    rw [← h]
    exact hz
  rw [Scheme.Pullback.range_map]
  refine ⟨?_, ?_⟩
  · change (pullback.fst f g).base z ∈ Set.range (pullback.fst f U.ι).base
    rw [IsOpenImmersion.range_pullback_fst_of_right]
    change f.base ((pullback.fst f g).base z) ∈ Set.range U.ι.base
    rw [Scheme.Opens.range_ι]
    exact hz
  · change (pullback.snd f g).base z ∈ Set.range (pullback.fst g U.ι).base
    rw [IsOpenImmersion.range_pullback_fst_of_right]
    change g.base ((pullback.snd f g).base z) ∈ Set.range U.ι.base
    rw [Scheme.Opens.range_ι]
    exact hg

/-- The base-change piece over an open where the second factor is an isomorphism is integral once
nonempty (open in the integral first factor). -/
theorem pieceLeft_isIntegral (U : (projectiveProduct k).Opens) [IsIso (pullback.snd g U.ι)]
    [IsIntegral S] [Nonempty ((pullback (pullback.snd f U.ι) (pullback.snd g U.ι) : Scheme.{u}))] :
    IsIntegral (pullback (pullback.snd f U.ι) (pullback.snd g U.ι)) :=
  isIntegral_of_isOpenImmersion
    (pullback.fst (pullback.snd f U.ι) (pullback.snd g U.ι) ≫ pullback.fst f U.ι)

/-- The base-change piece over an open where the first factor is an isomorphism is integral once
nonempty (open in the integral second factor). -/
theorem pieceRight_isIntegral (V : (projectiveProduct k).Opens) [IsIso (pullback.snd f V.ι)]
    [IsIntegral T] [Nonempty ((pullback (pullback.snd f V.ι) (pullback.snd g V.ι) : Scheme.{u}))] :
    IsIntegral (pullback (pullback.snd f V.ι) (pullback.snd g V.ι)) :=
  isIntegral_of_isOpenImmersion
    (pullback.snd (pullback.snd f V.ι) (pullback.snd g V.ι) ≫ pullback.fst g V.ι)

end pieces

section step

variable [IsAlgClosed k] (p m : ℕ) (a : Fin (m + 1) → k)

/-- The complement of the new centre. -/
abbrev newPuncture : (projectiveProduct k).Opens :=
  initialPuncture (translatedInitial p (a (Fin.last m)))

/-- The complement of the earlier centres. -/
abbrev earlier : (projectiveProduct k).Opens := earlierComplement p m (fun i => a i.castSucc)

/-- The projection of the earlier surface. -/
abbrev leftProj : multiSurface p m (fun i => a i.castSucc) ⟶ projectiveProduct k :=
  multiProjection p m (fun i => a i.castSucc)

/-- The projection of the new tower. -/
abbrev rightProj : selectedStage (k := k) p (a (Fin.last m)) p ⟶ projectiveProduct k :=
  selectedProjection p (a (Fin.last m)) p

/-- Lane F's two-open base-change cover of the next multi-centre surface. -/
abbrev stepCover (ha : Function.Injective a) :
    Scheme.OpenCover.{u} (pullback (leftProj p m a) (rightProj p m a)) :=
  Scheme.Pullback.openCoverOfBase
    (twoOpenCover (newPuncture p m a) (earlier p m a) (cover_of_injective p m a ha))
    (leftProj p m a) (rightProj p m a)

/-- A graph point avoiding all the selected centres (the field is infinite). -/
theorem exists_graphPoint_avoiding :
    ∃ c : k, graphPoint p c ∈ newPuncture p m a ∧ graphPoint p c ∈ earlier p m a := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset (Finset.univ.image a)
  refine ⟨c, ?_, ?_⟩
  · change graphPoint p c ≠ (translatedInitial p (a (Fin.last m))).chart.base (originPoint (k := k))
    rw [selected_center]
    intro h
    exact hc (Finset.mem_image.mpr ⟨Fin.last m, Finset.mem_univ _, (graphPoint_injective p h).symm⟩)
  · rw [mem_earlierComplement_iff]
    intro i h
    exact hc (Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, (graphPoint_injective p h).symm⟩)

end step

local instance multiIntegralInitialIsIntegral (p : ℕ) (a : k) :
    IsIntegral (translatedInitial (k := k) p a).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- **`S_{p,n}` is integral** for distinct selected parameters over an algebraically closed field. -/
theorem multiSurface_isIntegral [IsAlgClosed k] (p : ℕ) :
    ∀ (m : ℕ) (a : Fin m → k), Function.Injective a → IsIntegral (multiSurface p m a)
  | 0, _, _ => FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  | m + 1, a, ha => by
      have ha' : Function.Injective (fun i : Fin m => a i.castSucc) :=
        fun i j h => Fin.castSucc_injective m (ha h)
      letI hS : IsIntegral (multiSurface p m (fun i => a i.castSucc)) :=
        multiSurface_isIntegral p m _ ha'
      letI hT : IsIntegral (selectedStage (k := k) p (a (Fin.last m)) p) :=
        instStageIsIntegral (translatedInitial p (a (Fin.last m))) p
      letI hgU : IsIso (rightProj p m a ∣_ newPuncture p m a) :=
        toInitial_restrict_isIso (translatedInitial p (a (Fin.last m))) p
      letI hfV : IsIso (leftProj p m a ∣_ earlier p m a) :=
        multiProjection_restrict_isIso p m _ _
          (not_mem_earlierComplement p m (fun i => a i.castSucc))
      letI : IsIso (pullback.snd (rightProj p m a) (newPuncture p m a).ι) :=
        isIso_pullback_snd_ι_of_restrict _ _
      letI : IsIso (pullback.snd (leftProj p m a) (earlier p m a).ι) :=
        isIso_pullback_snd_ι_of_restrict _ _
      -- a common point of the two pieces
      obtain ⟨c, hcU, hcV⟩ := exists_graphPoint_avoiding p m a
      obtain ⟨s', hs'⟩ := (inferInstance : Surjective (leftProj p m a ∣_ earlier p m a)).surj
        ⟨graphPoint p c, hcV⟩
      have hs : (leftProj p m a).base s'.1 = graphPoint p c := by
        rw [← morphismRestrict_base_coe, hs']
        rfl
      obtain ⟨t', ht'⟩ := (inferInstance : Surjective (rightProj p m a ∣_ newPuncture p m a)).surj
        ⟨graphPoint p c, hcU⟩
      have ht : (rightProj p m a).base t'.1 = graphPoint p c := by
        rw [← morphismRestrict_base_coe, ht']
        rfl
      obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := leftProj p m a)
        (g := rightProj p m a) s'.1 t'.1 (hs.trans ht.symm)
      have hzU : z ∈ Set.range ((stepCover p m a ha).map ⟨true⟩).base := by
        rw [Scheme.Pullback.openCoverOfBase_map]
        exact mem_range_pieceMap (leftProj p m a) (rightProj p m a) (newPuncture p m a) z
          (by rw [hz₁, hs]; exact hcU)
      have hzV : z ∈ Set.range ((stepCover p m a ha).map ⟨false⟩).base := by
        rw [Scheme.Pullback.openCoverOfBase_map]
        exact mem_range_pieceMap (leftProj p m a) (rightProj p m a) (earlier p m a) z
          (by rw [hz₁, hs]; exact hcV)
      -- the pieces are integral
      have hpiece : ∀ i, IsIntegral ((stepCover p m a ha).obj i) := by
        rintro ⟨b⟩
        cases b
        · obtain ⟨y, _⟩ := hzV
          letI : Nonempty ((pullback (pullback.snd (leftProj p m a) (earlier p m a).ι)
              (pullback.snd (rightProj p m a) (earlier p m a).ι) : Scheme.{u})) := ⟨y⟩
          exact pieceRight_isIntegral (leftProj p m a) (rightProj p m a) (earlier p m a)
        · obtain ⟨y, _⟩ := hzU
          letI : Nonempty ((pullback (pullback.snd (leftProj p m a) (newPuncture p m a).ι)
              (pullback.snd (rightProj p m a) (newPuncture p m a).ι) : Scheme.{u})) := ⟨y⟩
          exact pieceLeft_isIntegral (leftProj p m a) (rightProj p m a) (newPuncture p m a)
      change IsIntegral (pullback (leftProj p m a) (rightProj p m a) : Scheme.{u})
      haveI hred : IsReduced (pullback (leftProj p m a) (rightProj p m a) : Scheme.{u}) := by
        haveI : ∀ x : (pullback (leftProj p m a) (rightProj p m a) : Scheme.{u}),
            _root_.IsReduced ((pullback (leftProj p m a) (rightProj p m a) : Scheme.{u}).presheaf.stalk x) := by
          intro x
          obtain ⟨y, hy⟩ := (stepCover p m a ha).covers x
          haveI := (stepCover p m a ha).map_prop ((stepCover p m a ha).f x)
          letI := hpiece ((stepCover p m a ha).f x)
          rw [← hy]
          exact isReduced_of_injective (((stepCover p m a ha).map ((stepCover p m a ha).f x)).stalkMap y).hom
            (asIso (((stepCover p m a ha).map ((stepCover p m a ha).f x)).stalkMap y)).commRingCatIsoToRingEquiv.injective
        exact isReduced_of_isReduced_stalk _
      haveI hirr : IrreducibleSpace (pullback (leftProj p m a) (rightProj p m a) : Scheme.{u}) := by
        have hrange : ∀ i, IsIrreducible (Set.range ((stepCover p m a ha).map i).base) := by
          intro i
          letI := hpiece i
          have h := (IrreducibleSpace.isIrreducible_univ ((stepCover p m a ha).obj i)).image
            ((stepCover p m a ha).map i).base ((stepCover p m a ha).map i).continuous.continuousOn
          simpa only [Set.image_univ] using h
        refine irreducibleSpace_of_two_irreducible_opens (hrange ⟨true⟩) (hrange ⟨false⟩)
          ?_ ?_ ?_ hzU hzV
        · haveI := (stepCover p m a ha).map_prop ⟨true⟩
          exact ((stepCover p m a ha).map ⟨true⟩).isOpenEmbedding.isOpen_range
        · haveI := (stepCover p m a ha).map_prop ⟨false⟩
          exact ((stepCover p m a ha).map ⟨false⟩).isOpenEmbedding.isOpen_range
        · intro x
          rcases cover_of_injective p m a ha
            ((leftProj p m a).base ((pullback.fst (leftProj p m a) (rightProj p m a)).base x)) with
            hx | hx
          · left
            rw [Scheme.Pullback.openCoverOfBase_map]
            exact mem_range_pieceMap (leftProj p m a) (rightProj p m a) (newPuncture p m a) x hx
          · right
            rw [Scheme.Pullback.openCoverOfBase_map]
            exact mem_range_pieceMap (leftProj p m a) (rightProj p m a) (earlier p m a) x hx
      exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The complement of all the selected centres is nonempty. -/
theorem earlierComplement_nonempty [IsAlgClosed k] (p m : ℕ) (a : Fin m → k) :
    Nonempty (earlierComplement p m a) := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset (Finset.univ.image a)
  refine ⟨⟨graphPoint p c, ?_⟩⟩
  rw [mem_earlierComplement_iff]
  intro i h
  exact hc (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (graphPoint_injective p h).symm⟩)

/-- **`S_{p,n}` has dimension two**: its proper projection to `P¹ ×_k P¹` is an isomorphism over the
nonempty complement of the centres. -/
theorem multiSurface_topologicalKrullDim [IsAlgClosed k] (p m : ℕ) (a : Fin m → k)
    (ha : Function.Injective a) : topologicalKrullDim (multiSurface p m a) = 2 := by
  letI : IsIntegral (multiSurface p m a) := multiSurface_isIntegral p m a ha
  letI : IsIntegral (projectiveProduct k) :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  letI : IsIso (multiProjection p m a ∣_ earlierComplement p m a) :=
    multiProjection_restrict_isIso p m a _ (not_mem_earlierComplement p m a)
  letI : Nonempty (earlierComplement p m a) := earlierComplement_nonempty p m a
  exact (topologicalKrullDim_eq_of_proper_isomorphism_open (multiProjection p m a)
    projectiveProductToSpec (earlierComplement p m a)).trans projectiveProduct_topologicalKrullDim

/-- **`S_{p,n}` as a normal projective surface**, given a closed projective embedding `hproj` of it
over `k`; integrality, normality and dimension two are proved. -/
def multiSurfaceSurface [IsAlgClosed k] (p m : ℕ) (a : Fin m → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure p m a)) : NormalProjectiveSurface k where
  toScheme := multiSurface p m a
  structureMorphism := multiStructure p m a
  integral := multiSurface_isIntegral p m a ha
  normal := multiSurface_isNormalScheme p m a ha
  projective := hproj
  dimension_two := multiSurface_topologicalKrullDim p m a ha

@[simp] theorem multiSurfaceSurface_toScheme [IsAlgClosed k] (p m : ℕ) (a : Fin m → k)
    (ha : Function.Injective a) (hproj : IsProjectiveOverField (multiStructure p m a)) :
    (multiSurfaceSurface p m a ha hproj).toScheme = multiSurface p m a := rfl

end KltDP.Examples.FrobeniusMultiCentreIntegral
