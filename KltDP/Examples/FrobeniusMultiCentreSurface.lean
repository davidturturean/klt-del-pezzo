import KltDP.Geometry.SchemePullbackRestrictIso
import KltDP.Geometry.PointBlowupExceptionalIdeal
import KltDP.Examples.FrobeniusUnaffectedFibers
import KltDP.Examples.FrobeniusExceptionalFinalConfiguration
import KltDP.Examples.FrobeniusGraphPicardClassFiberClasses

/-!
# The multi-centre surface `S_{p,n}` as an actual scheme

Given `n` selected parameters `a : Fin n → k`, the towers `T_i := selectedStage p (a i) p` (the
whole schemes after `p` contact blowups at the graph points `(a i, (a i)^p)`) are proper over the
projective product `X := P¹ ×_k P¹` and isomorphisms away from their own centre. The surface
`S_{p,n}` is defined as the iterated fibre product `T_0 ×_X T_1 ×_X ⋯ ×_X T_{n-1}`; this is the
surface obtained by blowing up all `n·p` centres, because over the complement of the other centres
each factor `T_j` is an isomorphism onto its image.

Proved here for every field and every `p`:

* `multiSurface p n a` is an actual scheme with projection `multiProjection p n a` to `X`, proper;
  the structure morphism `multiStructure p n a` over `k` is proper;
* over any open of `X` avoiding all the selected centres the projection is an isomorphism
  (`multiProjection_restrict_isIso`), by the generic restriction-of-base-change lemma;
* for distinct selected parameters over an algebraically closed field the surface is smooth of
  relative dimension two over `k` (`multiStructure_smoothTwo`): `X` is covered by the two opens
  "away from the new centre" and "away from the earlier centres", and the base-change cover of the
  fibre product over these opens exhibits it locally as an open piece of the earlier surface or of
  the new tower;
* the projections `towerProjection p n a i : S_{p,n} ⟶ T_i` onto each tower, compatible with the
  projections to `X`;
* the total-transform classes: the graph class satisfies `−[Π^*O(B_0)] = p • a + b` in the actual
  Picard group of `S_{p,n}`, and for every `i : Fin n`, `j : Fin p` the class `E_{ij}` is defined as
  the pullback along `towerProjection i` of the exceptional ideal line of the `j`-th blowup of `T_i`,
  itself pulled back to the final stage of `T_i`.

No surface, smoothness, isomorphism, or class relation is assumed; the strict-transform classes
`B`, `F_i`, `C_ij`, `P_i` on `S_{p,n}` are not treated here (lane A2).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusMultiCentreSurface

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusBlowupChartIteration
  FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupSmooth FrobeniusTranslatedCharts
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusContactTowerSelectedPoint
  FrobeniusExceptionalFinalConfiguration FrobeniusGraphPicardClassFrames
  FrobeniusGraphPicardClassFiberClasses

variable {k : Type u} [Field k]

local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

instance projectiveProductToSpec_isProper : IsProper (projectiveProductToSpec (k := k)) :=
  projectiveProductInitial_structure_isProper

/-- A scheme together with a morphism to the projective product. -/
structure TowerData (k : Type u) [Field k] where
  carrier : Scheme.{u}
  projection : carrier ⟶ projectiveProduct k

/-- The iterated fibre product over `X` of the towers at the selected points `a 0, …, a (m-1)`. -/
def multiTower (p : ℕ) : (m : ℕ) → (Fin m → k) → TowerData k
  | 0, _ => ⟨projectiveProduct k, 𝟙 _⟩
  | m + 1, a =>
    ⟨pullback (multiTower p m (fun i => a i.castSucc)).projection
        (selectedProjection p (a (Fin.last m)) p),
      pullback.fst _ _ ≫ (multiTower p m (fun i => a i.castSucc)).projection⟩

/-- The multi-centre surface `S_{p,n}` for the selected parameters `a`. -/
abbrev multiSurface (p n : ℕ) (a : Fin n → k) : Scheme.{u} := (multiTower p n a).carrier

/-- Its projection to the projective product. -/
def multiProjection (p n : ℕ) (a : Fin n → k) : multiSurface p n a ⟶ projectiveProduct k :=
  (multiTower p n a).projection

/-- Its structure morphism over `k`. -/
def multiStructure (p n : ℕ) (a : Fin n → k) : multiSurface p n a ⟶ Spec (CommRingCat.of k) :=
  multiProjection p n a ≫ projectiveProductToSpec

theorem multiProjection_zero (p : ℕ) (a : Fin 0 → k) :
    multiProjection p 0 a = 𝟙 (projectiveProduct k) := rfl

theorem multiProjection_succ (p m : ℕ) (a : Fin (m + 1) → k) :
    multiProjection p (m + 1) a =
      pullback.fst (multiProjection p m (fun i => a i.castSucc))
          (selectedProjection p (a (Fin.last m)) p) ≫
        multiProjection p m (fun i => a i.castSucc) := rfl

theorem multiStructure_succ (p m : ℕ) (a : Fin (m + 1) → k) :
    multiStructure p (m + 1) a =
      (pullback.fst (multiProjection p m (fun i => a i.castSucc))
          (selectedProjection p (a (Fin.last m)) p) ≫
        multiProjection p m (fun i => a i.castSucc)) ≫ projectiveProductToSpec := rfl

theorem multiProjection_isProper (p : ℕ) :
    ∀ (m : ℕ) (a : Fin m → k), IsProper (multiProjection p m a)
  | 0, _ => by
      change IsProper (𝟙 (projectiveProduct k))
      infer_instance
  | m + 1, a => by
      letI := multiProjection_isProper p m (fun i => a i.castSucc)
      letI : IsProper (pullback.fst (multiProjection p m (fun i => a i.castSucc))
          (selectedProjection p (a (Fin.last m)) p)) :=
        MorphismProperty.pullback_fst (P := @IsProper) _ _ inferInstance
      rw [multiProjection_succ]
      infer_instance

instance multiProjection_isProper' (p n : ℕ) (a : Fin n → k) :
    IsProper (multiProjection p n a) :=
  multiProjection_isProper p n a

instance multiStructure_isProper (p n : ℕ) (a : Fin n → k) :
    IsProper (multiStructure p n a) := by
  unfold multiStructure
  infer_instance

/-- An open avoiding the selected centre lies in the accepted centre complement. -/
theorem le_initialPuncture_of_not_mem (p : ℕ) (c : k) (V : (projectiveProduct k).Opens)
    (hV : graphPoint p c ∉ V) : V ≤ initialPuncture (translatedInitial p c) := by
  intro x hx
  change x ≠ (translatedInitial p c).chart.base (originPoint (k := k))
  rw [selected_center]
  intro hxc
  apply hV
  rw [← hxc]
  exact hx

/-- The tower projection is an isomorphism over any open avoiding its centre. -/
theorem selectedProjection_restrict_isIso (p : ℕ) (c : k) (V : (projectiveProduct k).Opens)
    (hV : graphPoint p c ∉ V) : IsIso (selectedProjection p c p ∣_ V) := by
  letI : IsIso (selectedProjection p c p ∣_ initialPuncture (translatedInitial p c)) :=
    toInitial_restrict_isIso (translatedInitial p c) p
  exact FrobeniusStageComplement.restrict_isIso_of_le (selectedProjection p c p)
    (le_initialPuncture_of_not_mem p c V hV)

/-- Over an open avoiding every selected centre the projection is an isomorphism. -/
theorem multiProjection_restrict_isIso (p : ℕ) :
    ∀ (m : ℕ) (a : Fin m → k) (V : (projectiveProduct k).Opens),
      (∀ i, graphPoint p (a i) ∉ V) → IsIso (multiProjection p m a ∣_ V)
  | 0, _, V, _ => by
      change IsIso ((𝟙 (projectiveProduct k)) ∣_ V)
      exact (morphismRestrict_id V).symm ▸ (inferInstance : IsIso (𝟙 V.toScheme))
  | m + 1, a, V, hV => by
      letI := multiProjection_restrict_isIso p m (fun i => a i.castSucc) V
        (fun i => hV i.castSucc)
      letI := selectedProjection_restrict_isIso p (a (Fin.last m)) V (hV (Fin.last m))
      letI := isIso_pullback_fst_restrict (multiProjection p m (fun i => a i.castSucc))
        (selectedProjection p (a (Fin.last m)) p) V
      rw [multiProjection_succ, morphismRestrict_comp]
      infer_instance

section Cover

/-- The two opens of a two-open cover, indexed by a lifted Boolean. -/
def coverOpen (U V : (projectiveProduct k).Opens) : ULift.{u} Bool → (projectiveProduct k).Opens
  | ⟨true⟩ => U
  | ⟨false⟩ => V

open Classical in
/-- Two opens covering the projective product, as an actual open cover. -/
def twoOpenCover (U V : (projectiveProduct k).Opens) (hUV : ∀ x, x ∈ U ∨ x ∈ V) :
    Scheme.OpenCover.{u} (projectiveProduct k) where
  J := ULift.{u} Bool
  obj b := (coverOpen U V b).toScheme
  map b := (coverOpen U V b).ι
  f x := if x ∈ U then ⟨true⟩ else ⟨false⟩
  covers x := by
    by_cases hx : x ∈ U
    · rw [if_pos hx]
      exact ⟨⟨x, hx⟩, rfl⟩
    · rw [if_neg hx]
      exact ⟨⟨x, (hUV x).resolve_left hx⟩, rfl⟩

end Cover

section Pieces

variable {S T Y : Scheme.{u}} (f : S ⟶ projectiveProduct k) (g : T ⟶ projectiveProduct k)
  (σ : projectiveProduct k ⟶ Y)

/-- The base-change piece over an open where the second factor is an isomorphism is an open
piece of the first factor; smoothness of relative dimension two is inherited. -/
theorem pieceLeft_smoothTwo (U : (projectiveProduct k).Opens) [IsIso (pullback.snd g U.ι)]
    [IsSmoothOfRelativeDimension 2 (f ≫ σ)] :
    IsSmoothOfRelativeDimension 2
      (pullback.map (pullback.snd f U.ι) (pullback.snd g U.ι) f g
          (pullback.fst _ _) (pullback.fst _ _) U.ι
          pullback.condition.symm pullback.condition.symm ≫
        (pullback.fst f g ≫ f) ≫ σ) := by
  rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _),
    pullback.map, pullback.lift_fst]
  exact inferInstanceAs (IsSmoothOfRelativeDimension ((0 + 0) + 2)
    ((pullback.fst (pullback.snd f U.ι) (pullback.snd g U.ι) ≫ pullback.fst f U.ι) ≫ (f ≫ σ)))

/-- The base-change piece over an open where the first factor is an isomorphism is an open
piece of the second factor. -/
theorem pieceRight_smoothTwo (V : (projectiveProduct k).Opens) [IsIso (pullback.snd f V.ι)]
    [IsSmoothOfRelativeDimension 2 (g ≫ σ)] :
    IsSmoothOfRelativeDimension 2
      (pullback.map (pullback.snd f V.ι) (pullback.snd g V.ι) f g
          (pullback.fst _ _) (pullback.fst _ _) V.ι
          pullback.condition.symm pullback.condition.symm ≫
        (pullback.fst f g ≫ f) ≫ σ) := by
  have hc : (pullback.fst f g ≫ f) ≫ σ = (pullback.snd f g ≫ g) ≫ σ := by
    rw [pullback.condition]
  rw [hc, Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _),
    pullback.map, pullback.lift_snd]
  exact inferInstanceAs (IsSmoothOfRelativeDimension ((0 + 0) + 2)
    ((pullback.snd (pullback.snd f V.ι) (pullback.snd g V.ι) ≫ pullback.fst g V.ι) ≫ (g ≫ σ)))

end Pieces

/-- The complement of the selected centres `a 0, …, a (m-1)`, as a finite meet of the accepted
centre complements. -/
def earlierComplement (p : ℕ) : (m : ℕ) → (Fin m → k) → (projectiveProduct k).Opens
  | 0, _ => ⊤
  | m + 1, a =>
    earlierComplement p m (fun i => a i.castSucc) ⊓
      initialPuncture (translatedInitial p (a (Fin.last m)))

theorem mem_earlierComplement_iff (p : ℕ) :
    ∀ (m : ℕ) (a : Fin m → k) (x : projectiveProduct k),
      x ∈ earlierComplement p m a ↔ ∀ i, x ≠ graphPoint p (a i)
  | 0, a, x => by
      change x ∈ (⊤ : (projectiveProduct k).Opens) ↔ ∀ i : Fin 0, x ≠ graphPoint p (a i)
      exact ⟨fun _ i => i.elim0, fun _ => TopologicalSpace.Opens.mem_top x⟩
  | m + 1, a, x => by
      rw [earlierComplement, TopologicalSpace.Opens.mem_inf, mem_earlierComplement_iff p m,
        Fin.forall_fin_succ']
      apply and_congr Iff.rfl
      change x ≠ (translatedInitial p (a (Fin.last m))).chart.base (originPoint (k := k)) ↔ _
      rw [selected_center]

theorem not_mem_earlierComplement (p m : ℕ) (a : Fin m → k) (i : Fin m) :
    graphPoint p (a i) ∉ earlierComplement p m a := fun h =>
  (mem_earlierComplement_iff p m a _).mp h i rfl

/-- For distinct parameters, the complement of the new centre and the complement of the earlier
centres cover the product. -/
theorem cover_of_injective [IsAlgClosed k] (p m : ℕ) (a : Fin (m + 1) → k)
    (ha : Function.Injective a) (x : projectiveProduct k) :
    x ∈ initialPuncture (translatedInitial p (a (Fin.last m))) ∨
      x ∈ earlierComplement p m (fun i => a i.castSucc) := by
  by_cases hx : x = graphPoint p (a (Fin.last m))
  · right
    rw [mem_earlierComplement_iff]
    intro i hxi
    have hai : a (Fin.last m) = a i.castSucc := graphPoint_injective p (hx.symm.trans hxi)
    exact absurd (ha hai) (Fin.castSucc_lt_last i).ne'
  · left
    change x ≠ (translatedInitial p (a (Fin.last m))).chart.base (originPoint (k := k))
    rw [selected_center]
    exact hx

/-- For distinct selected parameters over an algebraically closed field, the multi-centre surface
is smooth of relative dimension two over `k`. -/
theorem multiStructure_smoothTwo [IsAlgClosed k] (p : ℕ) :
    ∀ (m : ℕ) (a : Fin m → k), Function.Injective a →
      IsSmoothOfRelativeDimension 2 (multiStructure p m a)
  | 0, _, _ => by
      change IsSmoothOfRelativeDimension 2 (𝟙 (projectiveProduct k) ≫ projectiveProductToSpec)
      rw [Category.id_comp]
      exact projectiveProduct_structure_smoothTwo
  | m + 1, a, ha => by
      have ha' : Function.Injective (fun i : Fin m => a i.castSucc) :=
        fun i j h => Fin.castSucc_injective m (ha h)
      letI hS : IsSmoothOfRelativeDimension 2
          (multiProjection p m (fun i => a i.castSucc) ≫ projectiveProductToSpec) :=
        multiStructure_smoothTwo p m _ ha'
      letI hT : IsSmoothOfRelativeDimension 2
          (selectedProjection p (a (Fin.last m)) p ≫ projectiveProductToSpec) := by
        rw [selectedProjection_structure]
        infer_instance
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
      rw [multiStructure_succ]
      apply IsLocalAtSource.of_openCover (P := @IsSmoothOfRelativeDimension 2)
        (Scheme.Pullback.openCoverOfBase
          (twoOpenCover (initialPuncture (translatedInitial p (a (Fin.last m))))
            (earlierComplement p m (fun i => a i.castSucc)) (cover_of_injective p m a ha))
          (multiProjection p m (fun i => a i.castSucc)) (selectedProjection p (a (Fin.last m)) p))
      rintro ⟨b⟩
      cases b
      · -- index `false`: the piece over the complement of the earlier centres
        rw [Scheme.Pullback.openCoverOfBase_map]
        exact pieceRight_smoothTwo (multiProjection p m (fun i => a i.castSucc))
          (selectedProjection p (a (Fin.last m)) p) projectiveProductToSpec
          (earlierComplement p m (fun i => a i.castSucc))
      · -- index `true`: the piece over the complement of the new centre
        rw [Scheme.Pullback.openCoverOfBase_map]
        exact pieceLeft_smoothTwo (multiProjection p m (fun i => a i.castSucc))
          (selectedProjection p (a (Fin.last m)) p) projectiveProductToSpec
          (initialPuncture (translatedInitial p (a (Fin.last m))))

/-- The projection of the multi-centre surface onto the tower at the `i`-th selected point. -/
def towerProjection (p : ℕ) :
    (m : ℕ) → (a : Fin m → k) → (i : Fin m) → (multiSurface p m a ⟶ selectedStage p (a i) p)
  | 0, _, i => i.elim0
  | m + 1, a, i =>
    Fin.lastCases (motive := fun i => multiSurface p (m + 1) a ⟶ selectedStage p (a i) p)
      (pullback.snd _ _)
      (fun i' => pullback.fst _ _ ≫ towerProjection p m (fun j => a j.castSucc) i') i

theorem towerProjection_last (p m : ℕ) (a : Fin (m + 1) → k) :
    towerProjection p (m + 1) a (Fin.last m) =
      pullback.snd (multiProjection p m (fun i => a i.castSucc))
        (selectedProjection p (a (Fin.last m)) p) :=
  Fin.lastCases_last

theorem towerProjection_castSucc (p m : ℕ) (a : Fin (m + 1) → k) (i : Fin m) :
    towerProjection p (m + 1) a i.castSucc =
      pullback.fst (multiProjection p m (fun i => a i.castSucc))
          (selectedProjection p (a (Fin.last m)) p) ≫
        towerProjection p m (fun j => a j.castSucc) i :=
  Fin.lastCases_castSucc i

/-- The tower projections are compatible with the projections to the projective product. -/
theorem towerProjection_projection (p : ℕ) :
    ∀ (m : ℕ) (a : Fin m → k) (i : Fin m),
      towerProjection p m a i ≫ selectedProjection p (a i) p = multiProjection p m a
  | 0, _, i => i.elim0
  | m + 1, a, i => by
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · rw [towerProjection_last]
        exact pullback.condition.symm
      · rw [towerProjection_castSucc, Category.assoc, towerProjection_projection p m _ i']
        rfl

section Classes

/-- The exceptional ideal line of the `j`-th blowup of the tower at `c`, pulled back to its final
stage `p`. Its inverse class is the total transform `E_j` on that tower. -/
def towerExceptionalLine (p : ℕ) (c : k) (j : Fin p) : InvertibleSheaf (selectedStage p c p) :=
  pullbackInvertibleSheaf (between (translatedInitial p c) (show j.val + 1 ≤ p from j.isLt))
    (PointBlowupGluing.globalCenterFiberIdealLine
      ((translatedInitial p c).stage j.val).chart (originPoint (k := k))
      ((translatedInitial p c).stage j.val).center_closed)

/-- The total-transform class `E_{ij}` on the multi-centre surface. -/
def exceptionalClass (p n : ℕ) (a : Fin n → k) (i : Fin n) (j : Fin p) :
    Additive (multiSurface p n a).Pic :=
  -Additive.ofMul
    (pullbackInvertibleSheaf (towerProjection p n a i) (towerExceptionalLine p (a i) j)).toPic

/-- The total transform of the graph ideal on the multi-centre surface. -/
def multiGraphTotalIdealLine (p n : ℕ) (a : Fin n → k) : InvertibleSheaf (multiSurface p n a) :=
  pullbackInvertibleSheaf (multiProjection p n a) (graphIdealLine p)

/-- The total transform `a` of the class of the fibre `x = 1`. -/
def multiFirstFiberClass (p n : ℕ) (a : Fin n → k) : Additive (multiSurface p n a).Pic :=
  -Additive.ofMul
    (pullbackInvertibleSheaf (multiProjection p n a) (verticalFiberIdealLine (k := k))).toPic

/-- The total transform `b` of the class of the fibre `y = 1`. -/
def multiSecondFiberClass (p n : ℕ) (a : Fin n → k) : Additive (multiSurface p n a).Pic :=
  -Additive.ofMul (pullbackInvertibleSheaf (multiProjection p n a) (graphIdealLine 0)).toPic

/-- The graph relation `[π^*B_0] = p • a + b` in the actual Picard group of `S_{p,n}`. -/
theorem inverse_multiGraphTotalIdeal_picard (p n : ℕ) (a : Fin n → k) :
    -Additive.ofMul (multiGraphTotalIdealLine p n a).toPic =
      p • multiFirstFiberClass p n a + multiSecondFiberClass p n a := by
  let P := schemePicardPullbackHom (multiProjection p n a)
  have h := congrArg P.toAdditive (inverse_graphIdeal_picard_eq_actual_fibers (k := k) p)
  simp only [firstFiberClass, secondFiberClass, map_neg, map_add, map_nsmul] at h
  change -Additive.ofMul (P (graphIdealLine p).toPic) =
    p • (-Additive.ofMul (P (verticalFiberIdealLine (k := k)).toPic)) +
      (-Additive.ofMul (P (graphIdealLine 0).toPic)) at h
  simpa only [P, schemePicardPullbackHom_toPic, multiGraphTotalIdealLine,
    multiFirstFiberClass, multiSecondFiberClass] using h

end Classes

end KltDP.Examples.FrobeniusMultiCentreSurface
