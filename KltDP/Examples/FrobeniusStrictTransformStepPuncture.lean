import KltDP.Examples.FrobeniusStrictTransformStepProjection
import KltDP.Examples.FrobeniusStageComplement
import KltDP.Geometry.SchemeConormalSourceIso
import KltDP.Geometry.SchemeConormalOpenImmersion
import KltDP.Geometry.SchemeKernelOpenPullback

/-!
# The original strict kernels on the actual one-step center complement

The constructed surjective morphism between the original strict curves
restricts to an isomorphism away from the actual current blowup center.
Its original ambient square commutes, the ambient restricted projection
is the already proved puncture isomorphism, and the source comparison is
a surjective closed immersion into the original reduced open strict curve.

The actual source and target isomorphisms then compare the original
categorical kernels and their original inclusions. No replacement strict
curve, complement isomorphism, or kernel comparison is an input premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStrictTransformStepPuncture

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformStepProjection
open FrobeniusStageComplement.PlaneChartedScheme

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The pointwise range check is independent of the concrete stage construction. -/
private theorem restrictSquare_range {A B X Y : Scheme.{u}}
    (a : A ⟶ X) (b : B ⟶ Y) (p : X ⟶ Y) (s : A ⟶ B)
    (h : s ≫ b = a ≫ p) (U : Y.Opens) :
    Set.range ((a ⁻¹ᵁ (p ⁻¹ᵁ U)).ι ≫ s).base ⊆
      Set.range (b ⁻¹ᵁ U).ι.base := by
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨s.base x.val, ?_⟩, rfl⟩
  change (s ≫ b).base x.val ∈ U
  rw [h]
  exact x.property

/-- Restriction of a proved ambient square preserves its chosen factored map. -/
private theorem restrictSquare_comm {A B X Y : Scheme.{u}}
    (a : A ⟶ X) (b : B ⟶ Y) (p : X ⟶ Y) (s : A ⟶ B)
    (h : s ≫ b = a ≫ p) (U : Y.Opens)
    (t : (a ⁻¹ᵁ (p ⁻¹ᵁ U)).toScheme ⟶ (b ⁻¹ᵁ U).toScheme)
    (ht : t ≫ (b ⁻¹ᵁ U).ι = (a ⁻¹ᵁ (p ⁻¹ᵁ U)).ι ≫ s) :
    (a ∣_ (p ⁻¹ᵁ U)) ≫ (p ∣_ U) = t ≫ (b ∣_ U) := by
  apply (cancel_mono U.ι).mp
  calc
    _ = (a ⁻¹ᵁ (p ⁻¹ᵁ U)).ι ≫ a ≫ p := by
      simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc]
    _ = (a ⁻¹ᵁ (p ⁻¹ᵁ U)).ι ≫ s ≫ b := by rw [h]
    _ = (t ≫ (b ⁻¹ᵁ U).ι) ≫ b := by
      simpa only [Category.assoc] using (congrArg (fun f => f ≫ b) ht).symm
    _ = _ := by simp only [Category.assoc, morphismRestrict_ι]

/-- Surjectivity restricts along the two literal inverse-image opens of a square. -/
private theorem restrictSquare_surjective {A B X Y : Scheme.{u}}
    (a : A ⟶ X) (b : B ⟶ Y) (p : X ⟶ Y) (s : A ⟶ B)
    (h : s ≫ b = a ≫ p) (U : Y.Opens)
    (t : (a ⁻¹ᵁ (p ⁻¹ᵁ U)).toScheme ⟶ (b ⁻¹ᵁ U).toScheme)
    (ht : t ≫ (b ⁻¹ᵁ U).ι = (a ⁻¹ᵁ (p ⁻¹ᵁ U)).ι ≫ s)
    (hs : Surjective s) : Surjective t := by
  constructor
  intro y
  obtain ⟨x, hx⟩ := hs.1 y.val
  have hmem : x ∈ a ⁻¹ᵁ (p ⁻¹ᵁ U) := by
    change (a ≫ p).base x ∈ U
    rw [← h]
    change b.base (s.base x) ∈ U
    rw [hx]
    exact y.property
  refine ⟨⟨x, hmem⟩, (b ⁻¹ᵁ U).ι.isOpenEmbedding.injective ?_⟩
  change (t ≫ (b ⁻¹ᵁ U).ι).base ⟨x, hmem⟩ = (b ⁻¹ᵁ U).ι.base y
  rw [ht]
  exact hx

variable {k : Type u} [Field k]

/-- The complement of the actual current center in the entire previous stage. -/
def currentPuncture (n : ℕ) : (projectiveContactStage (k := k) n).Opens :=
  initialPuncture ((projectiveProductInitial (k := k)).stage n)

/-- Its actual inverse image under the original one-step blowdown. -/
def nextPuncture (n : ℕ) : (projectiveContactStage (k := k) (n + 1)).Opens :=
  (projectiveProductInitial (k := k)).stepProjection n ⁻¹ᵁ currentPuncture n

instance stepProjection_puncture_isIso (n : ℕ) :
    IsIso ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n) :=
  nextProjection_restrict_isIso ((projectiveProductInitial (k := k)).stage n)

/-- The actual previous strict curve restricted to the current center complement. -/
abbrev previousStrictPuncture (n m : ℕ) :
    (strictTransform (k := k) n ((m + 1) + n)).Opens :=
  strictTransformι n ((m + 1) + n) ⁻¹ᵁ currentPuncture n

/-- The actual successor strict curve restricted to the inverse-image complement. -/
abbrev successorStrictPuncture (n m : ℕ) :
    (strictTransform (k := k) (n + 1) (m + (n + 1))).Opens :=
  strictTransformι (n + 1) (m + (n + 1)) ⁻¹ᵁ nextPuncture n

private theorem strictStep_puncture_range (n m : ℕ) :
    Set.range ((successorStrictPuncture (k := k) n m).ι ≫
      strictStepProjection n m).base ⊆ Set.range (previousStrictPuncture n m).ι.base :=
  restrictSquare_range
    (strictTransformι (k := k) (n + 1) (m + (n + 1)))
    (strictTransformι n ((m + 1) + n))
    ((projectiveProductInitial (k := k)).stepProjection n)
    (strictStepProjection n m) (strictStepProjection_inclusion n m) (currentPuncture n)

/-- The original strict-step morphism factored through the two original opens. -/
def strictStepOnPuncture (n m : ℕ) :
    (successorStrictPuncture (k := k) n m).toScheme ⟶
      (previousStrictPuncture (k := k) n m).toScheme :=
  IsOpenImmersion.lift (previousStrictPuncture n m).ι
    ((successorStrictPuncture (k := k) n m).ι ≫ strictStepProjection n m)
    (strictStep_puncture_range n m)

@[reassoc] theorem strictStepOnPuncture_ι (n m : ℕ) :
    strictStepOnPuncture (k := k) n m ≫ (previousStrictPuncture n m).ι =
      (successorStrictPuncture n m).ι ≫ strictStepProjection n m :=
  IsOpenImmersion.lift_fac _ _ _

/-- Both sides use the original restricted inclusions and original restricted blowdown. -/
theorem strictStepOnPuncture_square (n m : ℕ) :
    (strictTransformι (k := k) (n + 1) (m + (n + 1)) ∣_ nextPuncture n) ≫
        ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n) =
      strictStepOnPuncture n m ≫
        (strictTransformι n ((m + 1) + n) ∣_ currentPuncture n) :=
  restrictSquare_comm
    (strictTransformι (k := k) (n + 1) (m + (n + 1)))
    (strictTransformι n ((m + 1) + n))
    ((projectiveProductInitial (k := k)).stepProjection n)
    (strictStepProjection n m) (strictStepProjection_inclusion n m) (currentPuncture n)
    (strictStepOnPuncture n m) (strictStepOnPuncture_ι n m)

/-- Restriction of the original previous closed immersion, using the pinned locality theorem. -/
instance previousStrictPuncture_inclusion_isClosedImmersion (n m : ℕ) :
    IsClosedImmersion (strictTransformι (k := k) n ((m + 1) + n) ∣_ currentPuncture n) :=
  IsLocalAtTarget.restrict (P := @IsClosedImmersion)
    (inferInstance : IsClosedImmersion (strictTransformι n ((m + 1) + n))) _

/-- Restriction of the original successor closed immersion to the actual inverse-image open. -/
instance successorStrictPuncture_inclusion_isClosedImmersion (n m : ℕ) :
    IsClosedImmersion
      (strictTransformι (k := k) (n + 1) (m + (n + 1)) ∣_ nextPuncture n) :=
  IsLocalAtTarget.restrict (P := @IsClosedImmersion)
    (inferInstance : IsClosedImmersion (strictTransformι (n + 1) (m + (n + 1)))) _

/-- Over the actual complement the morphism is a closed immersion, using the ambient isomorphism. -/
instance strictStepOnPuncture_isClosedImmersion (n m : ℕ) :
    IsClosedImmersion (strictStepOnPuncture (k := k) n m) := by
  letI : IsClosedImmersion (strictStepOnPuncture (k := k) n m ≫
      (strictTransformι n ((m + 1) + n) ∣_ currentPuncture n)) := by
    rw [← strictStepOnPuncture_square]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion (strictStepOnPuncture n m)
    (strictTransformι n ((m + 1) + n) ∣_ currentPuncture n)

/-- Surjectivity restricts to these actual inverse-image opens by the original ambient square. -/
theorem strictStepOnPuncture_surjective (n m : ℕ) :
    Surjective (strictStepOnPuncture (k := k) n m) :=
  restrictSquare_surjective
    (strictTransformι (k := k) (n + 1) (m + (n + 1)))
    (strictTransformι n ((m + 1) + n))
    ((projectiveProductInitial (k := k)).stepProjection n)
    (strictStepProjection n m) (strictStepProjection_inclusion n m) (currentPuncture n)
    (strictStepOnPuncture n m) (strictStepOnPuncture_ι n m)
    (strictStepProjection_surjective n m)

/-- The actual restricted map is an isomorphism; reducedness comes from the original strict curve. -/
instance strictStepOnPuncture_isIso (n m : ℕ) :
    IsIso (strictStepOnPuncture (k := k) n m) := by
  letI : IsIntegral (strictTransform (k := k) n ((m + 1) + n)) :=
    strictTransform_isIntegral n (m + 1)
  letI : IsReduced (previousStrictPuncture (k := k) n m).toScheme :=
    isReduced_of_isOpenImmersion (previousStrictPuncture n m).ι
  letI := strictStepOnPuncture_surjective (k := k) n m
  exact isIso_of_isClosedImmersion_of_surjective (strictStepOnPuncture n m)

/-- The original strict inclusions form the actual pullback square on the current center complement. -/
theorem strictStepOnPuncture_isPullback (n m : ℕ) :
    IsPullback
      (strictTransformι (k := k) (n + 1) (m + (n + 1)) ∣_ nextPuncture n)
      (strictStepOnPuncture n m)
      ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)
      (strictTransformι n ((m + 1) + n) ∣_ currentPuncture n) :=
  IsPullback.of_vert_isIso ⟨strictStepOnPuncture_square n m⟩

/-- On every actual affine open of the successor puncture, the original
restricted strict ideal is the pullback of the original previous one. -/
theorem strictStepOnPuncture_ideal (n m : ℕ)
    (U : (nextPuncture (k := k) n).toScheme.affineOpens) :
    (strictTransformι (n + 1) (m + (n + 1)) ∣_ nextPuncture n).ker.ideal U =
      ((strictTransformι n ((m + 1) + n) ∣_ currentPuncture n).ker.ideal
        ⟨((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n) ''ᵁ U.1,
          U.2.image_of_isOpenImmersion _⟩).comap
        ((((projectiveProductInitial (k := k)).stepProjection n ∣_
          currentPuncture n).appIso U.1).inv.hom) :=
  Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (strictTransformι n ((m + 1) + n) ∣_ currentPuncture n)
    (strictTransformι (n + 1) (m + (n + 1)) ∣_ nextPuncture n)
    (strictStepOnPuncture n m)
    ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)
    (strictStepOnPuncture_isPullback n m) U

private theorem kernel_eqToIso_hom_ι {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (eqToIso (congrArg schemeKernelIdeal h)).hom ≫ schemeKernelIdealι g =
      schemeKernelIdealι f := by
  subst g
  exact Category.id_comp _

/-- Expose the original precomposition inclusion with an abstract isomorphism morphism. -/
private theorem precompKernel_asIso_inv_ι {A B Y : Scheme.{u}}
    (s : A ⟶ B) [IsIso s] (b : B ⟶ Y) :
    (schemeKernelPrecompIso (asIso s) b).inv ≫ schemeKernelIdealι (s ≫ b) =
      schemeKernelIdealι b :=
  schemeKernelPrecompIso_inv_ι (asIso s) b

/-- Check the exact chosen local-kernel comparison while the ambient square is abstract. -/
private theorem localKernelSquareIso_inclusion {A B X Y : Scheme.{u}}
    (a : A ⟶ X) (b : B ⟶ Y) (p : X ⟶ Y) [IsOpenImmersion p]
    (s : A ⟶ B) [IsIso s] (h : a ≫ p = s ≫ b) :
    ((schemeModulePullback p).mapIso
        ((schemeKernelPrecompIso (asIso s) b).symm ≪≫
          eqToIso (congrArg schemeKernelIdeal h.symm)) ≪≫
        schemeKernelPostcompOpenIso a p).hom ≫ schemeKernelIdealι a =
      (schemeModulePullback p).map (schemeKernelIdealι b) ≫
        (schemeModulePullbackUnitIso p).hom := by
  rw [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    schemeKernelPostcompOpenIso_hom_ι, ← Category.assoc, ← Functor.map_comp]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    kernel_eqToIso_hom_ι h.symm, precompKernel_asIso_inv_ι]

/-- Original local-to-global kernel comparisons preserve a normalized open-square isomorphism. -/
private theorem localToGlobalKernelIso_inclusion {A B X Y : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (p : V.toScheme ⟶ U.toScheme)
    (e : (schemeModulePullback p).obj (schemeKernelIdeal (f ∣_ U)) ≅
      schemeKernelIdeal (g ∣_ V))
    (he : e.hom ≫ schemeKernelIdealι (g ∣_ V) =
      (schemeModulePullback p).map (schemeKernelIdealι (f ∣_ U)) ≫
        (schemeModulePullbackUnitIso p).hom) :
    ((schemeModulePullback p).mapIso (localKernelToGlobalPullbackIso f U).symm ≪≫
        e ≪≫ localKernelToGlobalPullbackIso g V).hom ≫ pulledKernelInclusion g V.ι =
      (schemeModulePullback p).map (pulledKernelInclusion f U.ι) ≫
        (schemeModulePullbackUnitIso p).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    localKernelToGlobalPullbackIso_inclusion, he]
  rw [← Category.assoc, ← Functor.map_comp,
    ← localKernelToGlobalPullbackIso_inclusion f U,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The original local kernels are compared through the actual source and ambient isomorphisms. -/
def strictLocalPunctureKernelIso (n m : ℕ) :
    (schemeModulePullback
      ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).obj
        (schemeKernelIdeal (strictTransformι n ((m + 1) + n) ∣_ currentPuncture n)) ≅
      schemeKernelIdeal
        (strictTransformι (n + 1) (m + (n + 1)) ∣_ nextPuncture n) :=
  (schemeModulePullback
      ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).mapIso
    ((schemeKernelPrecompIso (asIso (strictStepOnPuncture n m))
        (strictTransformι n ((m + 1) + n) ∣_ currentPuncture n)).symm ≪≫
      eqToIso (congrArg schemeKernelIdeal (strictStepOnPuncture_square n m).symm)) ≪≫
    schemeKernelPostcompOpenIso
      (strictTransformι (n + 1) (m + (n + 1)) ∣_ nextPuncture n)
      ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)

/-- The local comparison preserves the actual prior inclusion under the canonical pullback unit. -/
theorem strictLocalPunctureKernelIso_inclusion (n m : ℕ) :
    (strictLocalPunctureKernelIso (k := k) n m).hom ≫
        schemeKernelIdealι (strictTransformι (n + 1) (m + (n + 1)) ∣_ nextPuncture n) =
      (schemeModulePullback
        ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).map
          (schemeKernelIdealι (strictTransformι n ((m + 1) + n) ∣_ currentPuncture n)) ≫
        (schemeModulePullbackUnitIso
          ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).hom :=
  localKernelSquareIso_inclusion
    (strictTransformι (k := k) (n + 1) (m + (n + 1)) ∣_ nextPuncture n)
    (strictTransformι n ((m + 1) + n) ∣_ currentPuncture n)
    ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)
    (strictStepOnPuncture n m) (strictStepOnPuncture_square n m)

/-- Both kernels are the literal pullbacks of the original whole-stage strict kernels. -/
def strictPunctureKernelIso (n m : ℕ) :
    (schemeModulePullback
      ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).obj
        ((schemeModulePullback (currentPuncture n).ι).obj
          (schemeKernelIdeal (strictTransformι n ((m + 1) + n)))) ≅
      (schemeModulePullback (nextPuncture n).ι).obj
        (schemeKernelIdeal (strictTransformι (n + 1) (m + (n + 1)))) :=
  (schemeModulePullback
      ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).mapIso
      (localKernelToGlobalPullbackIso (strictTransformι n ((m + 1) + n))
        (currentPuncture n)).symm ≪≫
    strictLocalPunctureKernelIso n m ≪≫
      localKernelToGlobalPullbackIso (strictTransformι (n + 1) (m + (n + 1))) (nextPuncture n)

/-- The whole-kernel comparison still preserves both original ambient inclusions. -/
theorem strictPunctureKernelIso_inclusion (n m : ℕ) :
    (strictPunctureKernelIso (k := k) n m).hom ≫
        pulledKernelInclusion (strictTransformι (n + 1) (m + (n + 1))) (nextPuncture n).ι =
      (schemeModulePullback
        ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).map
          (pulledKernelInclusion (strictTransformι n ((m + 1) + n)) (currentPuncture n).ι) ≫
        (schemeModulePullbackUnitIso
          ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).hom :=
  localToGlobalKernelIso_inclusion
    (strictTransformι (k := k) n ((m + 1) + n))
    (strictTransformι (n + 1) (m + (n + 1))) (currentPuncture n) (nextPuncture n)
    ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)
    (strictLocalPunctureKernelIso n m) (strictLocalPunctureKernelIso_inclusion n m)

/-- The existing pullback composition comparison retains the original ideal inclusion. -/
private theorem kernelPullbackCompIso_inclusion {A X Y Z : Scheme.{u}}
    (f : A ⟶ Y) (i : X ⟶ Y) (g : Z ⟶ X) :
    (schemeModulePullbackCompIso g i).hom.app (schemeKernelIdeal f) ≫
        pulledKernelInclusion f (g ≫ i) =
      (schemeModulePullback g).map (pulledKernelInclusion f i) ≫
        (schemeModulePullbackUnitIso g).hom := by
  simp only [pulledKernelInclusion, Category.assoc]
  rw [← Category.assoc ((schemeModulePullbackCompIso g i).hom.app (schemeKernelIdeal f)),
    ← (schemeModulePullbackCompIso g i).hom.naturality (schemeKernelIdealι f),
    Category.assoc, schemeModulePullbackCompIso_unit]
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc]

/-- Equality transport and the original composition comparison preserve the actual total inclusion. -/
private theorem totalKernelTransport_inclusion {A B X Y U V : Scheme.{u}}
    (f : A ⟶ Y) (g : B ⟶ X) (i : V ⟶ Y) (j : U ⟶ X)
    (p : U ⟶ V) (q : U ⟶ Y) (h : q = p ≫ i)
    (e : (schemeModulePullback p).obj ((schemeModulePullback i).obj (schemeKernelIdeal f)) ≅
      (schemeModulePullback j).obj (schemeKernelIdeal g))
    (he : e.hom ≫ pulledKernelInclusion g j =
      (schemeModulePullback p).map (pulledKernelInclusion f i) ≫
        (schemeModulePullbackUnitIso p).hom) :
    ((eqToIso (congrArg schemeModulePullback h)).app (schemeKernelIdeal f) ≪≫
        ((schemeModulePullbackCompIso p i).app (schemeKernelIdeal f)).symm ≪≫ e).hom ≫
      pulledKernelInclusion g j = pulledKernelInclusion f q := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [he, ← kernelPullbackCompIso_inclusion f i p, Iso.inv_hom_id_app_assoc]
  exact pulledKernelInclusion_congr f h

/-- Reassociate the actual total pullback through the original open square. -/
def strictTotalPunctureKernelIso (n m : ℕ) :
    (schemeModulePullback ((nextPuncture (k := k) n).ι ≫
      (projectiveProductInitial (k := k)).stepProjection n)).obj
        (schemeKernelIdeal (strictTransformι n ((m + 1) + n))) ≅
      (schemeModulePullback (nextPuncture n).ι).obj
        (schemeKernelIdeal (strictTransformι (n + 1) (m + (n + 1)))) :=
  (eqToIso (congrArg schemeModulePullback
    (morphismRestrict_ι ((projectiveProductInitial (k := k)).stepProjection n)
      (currentPuncture n)).symm)).app _ ≪≫
    ((schemeModulePullbackCompIso
      ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)
      (currentPuncture n).ι).app _).symm ≪≫
    strictPunctureKernelIso n m

/-- Expose the chosen total isomorphism before taking its hom projection. -/
private theorem strictTotalPunctureKernelIso_eq (n m : ℕ) :
    strictTotalPunctureKernelIso (k := k) n m =
      (eqToIso (congrArg schemeModulePullback
        (morphismRestrict_ι ((projectiveProductInitial (k := k)).stepProjection n)
          (currentPuncture (k := k) n)).symm)).app
          (schemeKernelIdeal (strictTransformι (k := k) n ((m + 1) + n))) ≪≫
        ((schemeModulePullbackCompIso
          ((projectiveProductInitial (k := k)).stepProjection n ∣_
            currentPuncture (k := k) n)
          (currentPuncture (k := k) n).ι).app
            (schemeKernelIdeal (strictTransformι (k := k) n ((m + 1) + n)))).symm ≪≫
        strictPunctureKernelIso (k := k) n m :=
  rfl

/-- The comparison is over O with the original total inclusion, not only an abstract line isomorphism. -/
theorem strictTotalPunctureKernelIso_inclusion (n m : ℕ) :
    (strictTotalPunctureKernelIso (k := k) n m).hom ≫
        pulledKernelInclusion (strictTransformι (n + 1) (m + (n + 1))) (nextPuncture n).ι =
      pulledKernelInclusion (strictTransformι n ((m + 1) + n))
        ((nextPuncture n).ι ≫ (projectiveProductInitial (k := k)).stepProjection n) := by
  rw [strictTotalPunctureKernelIso_eq]
  exact totalKernelTransport_inclusion
    (strictTransformι (k := k) n ((m + 1) + n))
    (strictTransformι (n + 1) (m + (n + 1))) (currentPuncture n).ι (nextPuncture n).ι
    ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)
    ((nextPuncture n).ι ≫ (projectiveProductInitial (k := k)).stepProjection n)
    (morphismRestrict_ι ((projectiveProductInitial (k := k)).stepProjection n)
      (currentPuncture n)).symm
    (strictPunctureKernelIso n m) (strictPunctureKernelIso_inclusion n m)

/-- The literal one-step pullback of the previous whole strict kernel agrees
with the original successor strict kernel on the actual exceptional complement. -/
def strictPulledPreviousPunctureIso (n m : ℕ) :
    (schemeModulePullback (nextPuncture (k := k) n).ι).obj
      ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
        (schemeKernelIdeal (strictTransformι n ((m + 1) + n)))) ≅
      (schemeModulePullback (nextPuncture n).ι).obj
        (schemeKernelIdeal (strictTransformι (n + 1) (m + (n + 1)))) :=
  (schemeModulePullbackCompIso (nextPuncture (k := k) n).ι
    ((projectiveProductInitial (k := k)).stepProjection n)).app _ ≪≫
    strictTotalPunctureKernelIso n m

/-- The literal total and strict ideal inclusions agree through that actual open isomorphism. -/
theorem strictPulledPreviousPunctureIso_inclusion (n m : ℕ) :
    (strictPulledPreviousPunctureIso (k := k) n m).hom ≫
        pulledKernelInclusion (strictTransformι (n + 1) (m + (n + 1))) (nextPuncture n).ι =
      (schemeModulePullback (nextPuncture n).ι).map
        (pulledKernelInclusion (strictTransformι n ((m + 1) + n))
          ((projectiveProductInitial (k := k)).stepProjection n)) ≫
        (schemeModulePullbackUnitIso (nextPuncture n).ι).hom := by
  rw [strictPulledPreviousPunctureIso, Iso.trans_hom, Category.assoc,
    strictTotalPunctureKernelIso_inclusion]
  exact kernelPullbackCompIso_inclusion (strictTransformι n ((m + 1) + n))
    ((projectiveProductInitial (k := k)).stepProjection n) (nextPuncture n).ι

end KltDP.Examples.FrobeniusStrictTransformStepPuncture
