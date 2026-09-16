import KltDP.Examples.FrobeniusSelectedStageSurface
import KltDP.Examples.FrobeniusMultiCentreSurface

/-!
# Normality of the multi-centre surface `S_{p,n}`

Lane F's `multiSurface p n a` (the iterated fibre product over `P¹ ×_k P¹` of the towers
`selectedStage p (a i) p`) is a normal scheme for distinct parameters `a` over an algebraically closed
field (`multiSurface_isNormalScheme`). The proof follows lane F's smoothness proof: the fibre product
`S_m ×_X T` is covered (`Scheme.Pullback.openCoverOfBase` of lane F's `twoOpenCover`) by the piece over
the complement of the new centre, where `T → X` is an isomorphism, so the piece is an open subscheme of
`S_m`, and the piece over the complement of the earlier centres, where `S_m → X` is an isomorphism, so
the piece is an open subscheme of `T` (`pieceLeft_isNormalScheme`, `pieceRight_isNormalScheme`; pinned
`pullback_snd_iso_of_left_iso`/`pullback_snd_iso_of_right_iso`, `pullback_fst_of_right`). Normality
is a stalk property transported along these open immersions (accepted
`normal_stalk_at_image_of_isOpenImmersion`); `S_m` is normal by induction and every tower stage is
normal (`selectedStage_isNormalScheme`).

Integrality, dimension two and projectivity of `S_{p,n}` are not treated here (integrality of the
fibre product is not in the accepted tree; dimension two needs it for the accepted proper-isomorphism
transfer), so `S_{p,n}` is not packaged as a `NormalProjectiveSurface`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreNormal

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGlobalBlowupStages
open FrobeniusStageComplement FrobeniusStageComplement.PlaneChartedScheme
open FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint FrobeniusMultiCentreSurface
open FrobeniusStageNormal FrobeniusSelectedStageSurface

variable {k : Type u} [Field k]

section pieces

variable {S T : Scheme.{u}} (f : S ⟶ projectiveProduct k) (g : T ⟶ projectiveProduct k)

/-- The base-change piece over an open where the second factor is an isomorphism is an open piece of
the first factor, hence normal if the first factor is. -/
theorem pieceLeft_isNormalScheme (U : (projectiveProduct k).Opens) [IsIso (pullback.snd g U.ι)]
    (hS : IsNormalScheme S) :
    IsNormalScheme (pullback (pullback.snd f U.ι) (pullback.snd g U.ι)) :=
  isNormalScheme_of_isOpenImmersion
    (pullback.fst (pullback.snd f U.ι) (pullback.snd g U.ι) ≫ pullback.fst f U.ι) hS

/-- The base-change piece over an open where the first factor is an isomorphism is an open piece of
the second factor, hence normal if the second factor is. -/
theorem pieceRight_isNormalScheme (V : (projectiveProduct k).Opens) [IsIso (pullback.snd f V.ι)]
    (hT : IsNormalScheme T) :
    IsNormalScheme (pullback (pullback.snd f V.ι) (pullback.snd g V.ι)) :=
  isNormalScheme_of_isOpenImmersion
    (pullback.snd (pullback.snd f V.ι) (pullback.snd g V.ι) ≫ pullback.fst g V.ι) hT

end pieces

/-- **`S_{p,n}` is normal** for distinct selected parameters over an algebraically closed field. -/
theorem multiSurface_isNormalScheme [IsAlgClosed k] (p : ℕ) :
    ∀ (m : ℕ) (a : Fin m → k), Function.Injective a → IsNormalScheme (multiSurface p m a)
  | 0, _, _ => projectiveProduct_isNormalScheme
  | m + 1, a, ha => by
      have ha' : Function.Injective (fun i : Fin m => a i.castSucc) :=
        fun i j h => Fin.castSucc_injective m (ha h)
      have hS : IsNormalScheme (multiSurface p m (fun i => a i.castSucc)) :=
        multiSurface_isNormalScheme p m _ ha'
      have hT : IsNormalScheme (selectedStage (k := k) p (a (Fin.last m)) p) :=
        selectedStage_isNormalScheme p (a (Fin.last m)) p
      letI hgU : IsIso (selectedProjection p (a (Fin.last m)) p ∣_
          initialPuncture (translatedInitial p (a (Fin.last m)))) :=
        toInitial_restrict_isIso (translatedInitial p (a (Fin.last m))) p
      letI hfV : IsIso (multiProjection p m (fun i => a i.castSucc) ∣_
          earlierComplement p m (fun i => a i.castSucc)) :=
        multiProjection_restrict_isIso p m _ _
          (not_mem_earlierComplement p m (fun i => a i.castSucc))
      letI : IsIso (pullback.snd (selectedProjection p (a (Fin.last m)) p)
          (initialPuncture (translatedInitial p (a (Fin.last m)))).ι) :=
        isIso_pullback_snd_ι_of_restrict _ _
      letI : IsIso (pullback.snd (multiProjection p m (fun i => a i.castSucc))
          (earlierComplement p m (fun i => a i.castSucc)).ι) :=
        isIso_pullback_snd_ι_of_restrict _ _
      let 𝒰 := Scheme.Pullback.openCoverOfBase
        (twoOpenCover (initialPuncture (translatedInitial p (a (Fin.last m))))
          (earlierComplement p m (fun i => a i.castSucc)) (cover_of_injective p m a ha))
        (multiProjection p m (fun i => a i.castSucc)) (selectedProjection p (a (Fin.last m)) p)
      have hpiece : ∀ i, IsNormalScheme (𝒰.obj i) := by
        rintro ⟨b⟩
        cases b
        · -- index `false`: the piece over the complement of the earlier centres, open in the tower
          exact pieceRight_isNormalScheme (multiProjection p m (fun i => a i.castSucc))
            (selectedProjection p (a (Fin.last m)) p)
            (earlierComplement p m (fun i => a i.castSucc)) hT
        · -- index `true`: the piece over the complement of the new centre, open in `S_m`
          exact pieceLeft_isNormalScheme (multiProjection p m (fun i => a i.castSucc))
            (selectedProjection p (a (Fin.last m)) p)
            (initialPuncture (translatedInitial p (a (Fin.last m)))) hS
      change IsNormalScheme (pullback (multiProjection p m (fun i => a i.castSucc))
        (selectedProjection p (a (Fin.last m)) p))
      intro x
      obtain ⟨y, hy⟩ := 𝒰.covers x
      haveI : IsOpenImmersion (𝒰.map (𝒰.f x)) := 𝒰.map_prop (𝒰.f x)
      rw [← hy]
      exact normal_stalk_at_image_of_isOpenImmersion (𝒰.map (𝒰.f x)) (hpiece (𝒰.f x)) y

end KltDP.Examples.FrobeniusMultiCentreNormal
