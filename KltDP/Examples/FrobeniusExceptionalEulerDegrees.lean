import KltDP.Geometry.RationalTreePicardIdentificationsOverBase
import KltDP.Geometry.RationalTreePicardWitnesses
import KltDP.Examples.FrobeniusExceptionalBaseField
import KltDP.Examples.FrobeniusMultiCentreLocusPicard

/-!
# The concrete identifications are over `k`: Lemma 2.2 in Euler-degree form for the witnesses, the
exceptional chains and the exceptional locus of `S_{p,n}`

BRIEF25, task 1 (concrete part). For every configuration of projective lines built in the lane the
curves `c j : P¹ ⟶ X` are `k`-morphisms, `c j ≫ f = projectiveSpaceToSpec k 1`, so the
identifications `lineIdentification` are over `k` (`RationalTreePicardIdentificationsOverBase`) and
Lemma 2.2 holds in Euler-degree terms — with the manuscript's degree `deg L|_C = χ(L|_C) − χ(O_C)`
on each exceptional curve:

* witness (a), the single line (`singleLine_rationalTreePicard_degrees`) and witness (b), the two
  fibres `x = 0 ∪ y = 0` of `P¹ × P¹` (`twoFibres_rationalTreePicard_degrees`,
  `twoFibres_halfClass_trivial_of_eulerDegree`): the fibres are sections of the projections of the
  product over `k` (`fibre_comp_structure`);
* the exceptional chain `C_1 ∪ ⋯ ∪ C_q ∪ P` of a contact tower over a charted plane `A`
  (`chain_rationalTreePicard_degrees`, `chain_trivial_of_eulerDegree_zero`,
  `chain_halfClass_trivial_of_eulerDegree`): the newest fibre is over `k` because the accepted
  identification `previousFiberIso` with `P¹` is (`previousFiberι_comp_structure`, from lane A2's
  `exceptionalFiberProjectiveLineIso_hom_structure` and the pasted pullback square of the centre
  fibre), the older curves because lane F's blowdown `strictToFiber` is compatible with the
  projections (`previousStrictι_comp_structure`) and the stage projections are over `k`
  (`between_comp_structure`); hence `chainCurve idx ≫ chainInclusion ≫ structureMap =
  projectiveSpaceToSpec k 1` (`chainCurve_comp_structure`);
* the exceptional chains of the multi-centre surface `S_{p,n}` (`towerChain_rationalTreePicard_degrees`,
  `towerChain_halfClass_trivial_of_eulerDegree`; `chainCurve_comp_multiStructure`, through the base
  change to the tower at the selected point and `selectedProjection_structure`), and the **whole
  exceptional locus**: the Euler multidegrees of the restrictions to the `n` chains
  (`locusEulerMultidegree : Pic(locus) → ∏ᵢ ℤ^{components of the i-th chain}`) form a bijection
  (`locusEulerMultidegree_bijective`, from the clopen decomposition of task 23), a class of Euler
  degree zero on every exceptional curve is trivial (`locus_eq_one_of_eulerDegree_zero`) and the
  half-class clause holds in Euler-degree form (`locus_halfClass_trivial_of_eulerDegree`).

The hypotheses are those of the underlying multidegree statements: `k` algebraically closed, and
for the towers lane F's single-point and transversality hypotheses (`ChainSinglePoints`,
`ChainTransversal`; `SinglePoints`, `TowerTransversal`); witness (b) is unconditional (task 21).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusExceptionalEulerDegrees

open KltDP.Geometry KltDP.Geometry.RationalTreePicard

/-! ## Witness (a): the single line -/

section SingleLine

variable (k : Type u) [Field k] [IsAlgClosed k]

local instance singleLine_noetherianSpace' : NoetherianSpace (projectiveSpace k 1) :=
  projectiveSpace_noetherianSpace k 1

omit [IsAlgClosed k] in
theorem singleLineCurve_comp_structure (j : PUnit.{u + 1}) :
    singleLineCurve k j ≫ projectiveSpaceToSpec k 1 = projectiveSpaceToSpec k 1 :=
  Category.id_comp _

/-- **Witness (a) in Euler-degree form**: the Euler multidegree of `P¹` over `k` is bijective. -/
theorem singleLine_rationalTreePicard_degrees :
    Function.Bijective (eulerMultidegree (projectiveSpace k 1) (projectiveSpaceToSpec k 1)) :=
  bijective_eulerMultidegree_of_configuration (projectiveSpace k 1) (singleLineCurve k)
    (singleLine_cover k) (singleLine_distinct k) (projectiveSpaceToSpec k 1)
    (singleLineCurve_comp_structure k) (singleLine_rationalTreePicard k)

end SingleLine

/-! ## Witness (b): the two fibres of `P¹ × P¹` -/

section TwoFibres

open KltDP.Examples.RationalTreePicardWitnessTwoFibres FrobeniusProjectivePoints
  FrobeniusGraphClosed FrobeniusGraphPicardClassZeroFiber FrobeniusUnaffectedFibers

variable {k : Type u} [Field k]

/-- The two fibres are `k`-morphisms: sections of the projections of the product over `k`. -/
theorem fibre_comp_structure (i : Fin 2) :
    fibre (k := k) i ≫ projectiveProductToSpec = projectiveSpaceToSpec k 1 := by
  fin_cases i
  · show horizontalFiberMorphism (0 : k) ≫ firstProjection ≫ projectiveSpaceToSpec k 1 = _
    rw [← Category.assoc, horizontalFiberMorphism_fst, Category.id_comp]
  · show verticalFiberMorphismAt (0 : k) ≫ firstProjection ≫ projectiveSpaceToSpec k 1 = _
    rw [← Category.assoc, verticalFiberMorphismAt_fst, Category.assoc, pointMorphism_over_base,
      Category.comp_id]

theorem twoFibresCurve_comp_structure (i : ULift.{u} (Fin 2)) :
    twoFibresCurve (k := k) i ≫ twoFibresInclusion ≫ projectiveProductToSpec =
      projectiveSpaceToSpec k 1 := by
  rw [← Category.assoc, twoFibresCurve_comp, fibre_comp_structure]

variable [IsAlgClosed k]

/-- **Witness (b) in Euler-degree form**: the Euler multidegree of `x = 0 ∪ y = 0` over `k` is
bijective (unconditionally, by the crossing of task 21). -/
theorem twoFibres_rationalTreePicard_degrees :
    Function.Bijective (eulerMultidegree (twoFibresScheme (k := k))
      (twoFibresInclusion ≫ projectiveProductToSpec)) :=
  bijective_eulerMultidegree_of_configuration (twoFibresScheme (k := k)) twoFibresCurve
    twoFibresCurve_cover twoFibresCurve_distinct (twoFibresInclusion ≫ projectiveProductToSpec)
    twoFibresCurve_comp_structure (twoFibres_rationalTreePicard' (k := k))

/-- The half-class clause on witness (b) in Euler-degree form: a class of `P¹ × P¹` whose double has
Euler degree zero on both fibres restricts trivially to `x = 0 ∪ y = 0`. -/
theorem twoFibres_halfClass_trivial_of_eulerDegree (M : (projectiveProduct k).Pic)
    (h : eulerMultidegree (twoFibresScheme (k := k)) (twoFibresInclusion ≫ projectiveProductToSpec)
      (schemePicardPullbackHom (twoFibresInclusion (k := k)) (M ^ 2)) = 0) :
    schemePicardPullbackHom (twoFibresInclusion (k := k)) M = 1 :=
  pullback_eq_one_of_eulerMultidegree_sq_eq_zero_of_configuration (twoFibresScheme (k := k))
    twoFibresCurve twoFibresCurve_cover twoFibresCurve_distinct
    (twoFibresInclusion ≫ projectiveProductToSpec) twoFibresInclusion
    twoFibresCurve_comp_structure (twoFibres_rationalTreePicard' (k := k)) M h

end TwoFibres

/-! ## The exceptional chain of a contact tower -/

section Tower

open KltDP.Geometry.AffineBlowup KltDP.Geometry.PointBlowupGluing
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
  FrobeniusExceptionalCharts FrobeniusExceptionalProjectiveLine FrobeniusExceptionalBaseField
  FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalSuccessor FrobeniusPreviousStrictBlowdown
  FrobeniusPreviousStrictIsoProjectiveLine FrobeniusExceptionalFinalConfiguration
  FrobeniusExceptionalChainPicard FrobeniusStageNoetherianFiniteType

variable {k : Type u} [Field k]

local instance originPoint_asIdeal_isMaximal' : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The closed centre of the plane is over `k`: the quotient by the origin ideal followed by the
plane's structure map is the field structure of the centre. -/
theorem centerInclusion_comp_planeStructure :
    centerInclusion (originPoint (k := k)).asIdeal ≫ planeStructure = centerToField := by
  rw [centerInclusion, planeStructure, centerToField, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun g : k →+* planeRing k ⧸ centerIdeal => Spec.map (CommRingCat.ofHom g))
  apply RingHom.ext
  intro r
  exact (originQuotientEquiv_symm r).symm

variable (A : PlaneChartedScheme k)

/-- **The newest exceptional fibre is over `k`**: its closed inclusion followed by the structure map
of the blown-up stage is the accepted identification with `P¹` followed by the structure map of
`P¹`. -/
theorem previousFiberι_comp_structure :
    previousFiberι A ≫ A.next.structureMap =
      (previousFiberIso A).hom ≫ projectiveSpaceToSpec k 1 := by
  have haff : (affineCenterFiberIso A.chart originPoint A.center_closed).inv ≫
      centerFiberToCenter (centerIdeal (k := k)) =
        globalCenterFiberToCenter A.chart originPoint A.center_closed :=
    (Iso.inv_comp_eq _).mpr
      (affineCenterFiberIso_hom_toCenter A.chart originPoint A.center_closed).symm
  have hR : (previousFiberIso A).hom ≫ projectiveSpaceToSpec k 1 =
      globalCenterFiberToCenter A.chart originPoint A.center_closed ≫ centerToField := by
    rw [previousFiberIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      exceptionalFiberProjectiveLineIso_hom_structure, fiberStructure, ← Category.assoc, haff]
  have hL : previousFiberι A ≫ A.next.structureMap =
      globalCenterFiberToCenter A.chart originPoint A.center_closed ≫
        closedCenterInclusion A.chart originPoint ≫ A.structureMap := by
    show pullback.fst _ _ ≫ projection A.chart originPoint A.center_closed ≫ A.structureMap =
      pullback.snd _ _ ≫ closedCenterInclusion A.chart originPoint ≫ A.structureMap
    rw [← Category.assoc, ← Category.assoc, pullback.condition]
  rw [hL, hR, closedCenterInclusion, Category.assoc, A.chart_structure,
    centerInclusion_comp_planeStructure]

/-- **The older exceptional curves are over `k`**: the strict transform of the previous fibre,
followed by the structure map of the next stage, is lane F's identification with `P¹` followed by
the structure map of `P¹`. -/
theorem previousStrictι_comp_structure :
    previousStrictι A ≫ A.next.next.structureMap =
      (previousStrictIsoProjectiveLine A).hom ≫ projectiveSpaceToSpec k 1 := by
  rw [previousStrictIsoProjectiveLine, Iso.trans_hom, asIso_hom, Category.assoc,
    ← previousFiberι_comp_structure, ← Category.assoc, strictToFiber_ι, Category.assoc]
  rfl

/-- The composite stage projections are over `k`. -/
theorem between_comp_structure {i j : ℕ} (h : i ≤ j) :
    between A h ≫ (A.stage i).structureMap = (A.stage j).structureMap := by
  induction j, h using Nat.le_induction with
  | base => rw [between_refl, Category.id_comp]
  | succ j hij ih =>
    rw [between_succ A hij, Category.assoc, ih]
    rfl

/-- Every final exceptional component is over `k`, through its identification with `P¹`. -/
theorem finalComponentι_comp_structure (q : ℕ) (idx : FinalIndex.{u} q) :
    finalComponentι A q idx ≫ (A.stage (q + 1)).structureMap =
      (chainCurveIso q A idx).hom ≫ projectiveSpaceToSpec k 1 := by
  cases idx with
  | inl j =>
    have hb : between A (show j.val + 2 ≤ q + 1 by omega) ≫
        (A.stage j.val).next.next.structureMap = (A.stage (q + 1)).structureMap :=
      between_comp_structure A _
    show finalOldMap A (q + 1) j.val (by omega) ≫ (A.stage (q + 1)).structureMap =
      (previousStrictIsoProjectiveLine (A.stage j.val)).hom ≫ projectiveSpaceToSpec k 1
    rw [← previousStrictι_comp_structure, ← finalOldMap_projection A (q + 1) j.val (by omega),
      Category.assoc, hb]
  | inr _ =>
    exact previousFiberι_comp_structure (A.stage q)

/-- **The curves of the exceptional chain are `k`-morphisms.** -/
theorem chainCurve_comp_structure (q : ℕ) (idx : FinalIndex.{u} q) :
    chainCurve q A idx ≫ chainInclusion q A ≫ (A.stage (q + 1)).structureMap =
      projectiveSpaceToSpec k 1 := by
  rw [← Category.assoc, chainCurve_comp, Category.assoc, finalComponentι_comp_structure,
    Iso.inv_hom_id_assoc]

variable [IsAlgClosed k] [NoetherianSpace A.carrier] [IsLocallyNoetherian A.carrier]
  [IsProper A.structureMap] (q : ℕ) (hyp : ChainSinglePoints q A) (htrans : ChainTransversal q A hyp)

include hyp htrans in
/-- **Lemma 2.2 in Euler-degree form for the exceptional chain of a contact tower**: the Euler
multidegree of `C_1 ∪ ⋯ ∪ C_q ∪ P` over `k` is bijective (modulo lane F's chain hypotheses). -/
theorem chain_rationalTreePicard_degrees :
    Function.Bijective (eulerMultidegree (chainScheme q A)
      (chainInclusion q A ≫ (A.stage (q + 1)).structureMap)) :=
  bijective_eulerMultidegree_of_configuration (chainScheme q A) (chainCurve q A)
    (chainCurve_cover q A) (chainCurve_distinct q A hyp) _ (chainCurve_comp_structure A q)
    (chain_rationalTreePicard_of_tower A q hyp htrans)

include hyp htrans in
/-- A line bundle on the exceptional chain of Euler degree zero on every curve is trivial. -/
theorem chain_trivial_of_eulerDegree_zero (L : InvertibleSheaf (chainScheme q A))
    (hL : ∀ C : ↥(irreducibleComponents (chainScheme q A)),
      eulerDegree (componentUnionInclusion (chainScheme q A) {C} ≫ chainInclusion q A ≫
        (A.stage (q + 1)).structureMap) (componentUnionRestriction (chainScheme q A) {C} L) = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit (chainScheme q A).ringCatSheaf) :=
  trivial_of_eulerDegree_zero_of_bijective (chainScheme q A) _
    (chain_rationalTreePicard_degrees A q hyp htrans) L hL

include hyp htrans in
/-- **The half-class clause on the exceptional chain in Euler-degree form**: a class of the stage
whose double has Euler degree zero on every exceptional curve restricts trivially to the chain. -/
theorem chain_halfClass_trivial_of_eulerDegree (M : (chainStage q A).Pic)
    (h : eulerMultidegree (chainScheme q A) (chainInclusion q A ≫ (A.stage (q + 1)).structureMap)
      (schemePicardPullbackHom (chainInclusion q A) (M ^ 2)) = 0) :
    schemePicardPullbackHom (chainInclusion q A) M = 1 :=
  pullback_eq_one_of_eulerMultidegree_sq_eq_zero_of_configuration (chainScheme q A) (chainCurve q A)
    (chainCurve_cover q A) (chainCurve_distinct q A hyp) _ (chainInclusion q A)
    (chainCurve_comp_structure A q) (chain_rationalTreePicard_of_tower A q hyp htrans) M h

end Tower

/-! ## The exceptional chains and the exceptional locus of `S_{p,n}` -/

section MultiCentre

open KltDP.Geometry.RationalTreePicard
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusPreviousStrictIsoProjectiveLine FrobeniusGlobalExceptionalSuccessor
  FrobeniusTranslatedCharts FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional
  FrobeniusMultiCentreChainPicard FrobeniusMultiCentreLocusPicard FrobeniusMultiCentreHalfClass
  FrobeniusContactTowerSelectedPoint

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

/-- The final components of the `i`-th tower are over `k`, through their identifications with
`P¹`. -/
theorem componentIso_hom_comp_structure (i : Fin n) (idx : FinalIndex.{0} q) :
    finalComponentι (translatedInitial (q + 1) (a i)) q idx ≫
        ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap =
      (componentIso q n a i idx).hom ≫ projectiveSpaceToSpec k 1 := by
  cases idx with
  | inl j =>
    have hb : between (translatedInitial (q + 1) (a i)) (show j.val + 2 ≤ q + 1 by omega) ≫
        ((translatedInitial (q + 1) (a i)).stage j.val).next.next.structureMap =
          ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap :=
      between_comp_structure _ _
    show finalOldMap (translatedInitial (q + 1) (a i)) (q + 1) j.val (by omega) ≫
        ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap =
      (previousStrictIsoProjectiveLine ((translatedInitial (q + 1) (a i)).stage j.val)).hom ≫
        projectiveSpaceToSpec k 1
    rw [← previousStrictι_comp_structure, ← finalOldMap_projection _ (q + 1) j.val (by omega),
      Category.assoc, hb]
  | inr _ =>
    exact previousFiberι_comp_structure _

/-- The exceptional curves of `S_{p,n}`, over `k`, project onto the components of the towers. -/
theorem exceptionalCurveι_comp_structure (i : Fin n) (idx : FinalIndex.{0} q) :
    exceptionalCurveι q n a i idx ≫ multiStructure (q + 1) n a =
      exceptionalCurveToComponent q n a i idx ≫
        finalComponentι (translatedInitial (q + 1) (a i)) q idx ≫
          ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap := by
  rw [multiStructure, ← towerProjection_projection (q + 1) n a i, Category.assoc,
    exceptionalCurve_condition_assoc, selectedProjection_structure (q + 1) (a i) (q + 1)]

variable [IsAlgClosed k] (ha : Function.Injective a)

theorem exceptionalCurveIso_inv_comp_assoc (i : Fin n) (idx : FinalIndex.{0} q) {Z : Scheme.{u}}
    (g : finalComponent (translatedInitial (q + 1) (a i)) q idx ⟶ Z) :
    (exceptionalCurveIso q n a ha i idx).inv ≫ exceptionalCurveToComponent q n a i idx ≫ g = g :=
  Iso.inv_hom_id_assoc (exceptionalCurveIso q n a ha i idx) g

/-- **The curves of the exceptional chains of `S_{p,n}` are `k`-morphisms.** -/
theorem chainCurve_comp_multiStructure (i : Fin n) (j : Fin (q + 1)) :
    chainCurve q n a ha i j ≫ multiStructure (q + 1) n a = projectiveSpaceToSpec k 1 := by
  rw [chainCurve, Category.assoc, exceptionalCurveι_comp_structure, curveIso, Iso.trans_inv,
    Category.assoc, exceptionalCurveIso_inv_comp_assoc, componentIso_hom_comp_structure,
    Iso.inv_hom_id_assoc]

variable (hyp : SinglePoints q n a) (htrans : TowerTransversal q n a ha hyp)

include hyp htrans in
/-- **Lemma 2.2 in Euler-degree form for the `i`-th exceptional chain of `S_{p,n}`.** -/
theorem towerChain_rationalTreePicard_degrees (i : Fin n) :
    Function.Bijective (eulerMultidegree (towerChain q n a ha i)
      (towerChainInclusion q n a ha i ≫ multiStructure (q + 1) n a)) :=
  CurveChain.rationalTreePicard_degrees (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
    (multiStructure (q + 1) n a) (chainData q n a ha hyp i) (htrans i)
    (chainCurve_comp_multiStructure q n a ha i)

include hyp htrans in
/-- The half-class clause on the `i`-th chain in Euler-degree form. -/
theorem towerChain_halfClass_trivial_of_eulerDegree (i : Fin n)
    (M : (multiSurface (q + 1) n a).Pic)
    (h : eulerMultidegree (towerChain q n a ha i)
      (towerChainInclusion q n a ha i ≫ multiStructure (q + 1) n a)
      (schemePicardPullbackHom (towerChainInclusion q n a ha i) (M ^ 2)) = 0) :
    schemePicardPullbackHom (towerChainInclusion q n a ha i) M = 1 :=
  CurveChain.pullback_eq_one_of_eulerMultidegree_sq_eq_zero (multiSurface (q + 1) n a) q
    (chainCurve q n a ha i) (multiStructure (q + 1) n a) (chainData q n a ha hyp i) (htrans i)
    (chainCurve_comp_multiStructure q n a ha i) M h

/-- **The Euler multidegrees of the whole exceptional locus**: restrict a class to each of the `n`
chains and take its Euler multidegree (the manuscript's degrees on the exceptional curves). -/
def locusEulerMultidegree (p : (exceptionalScheme q n a).Pic) :
    (i : Fin n) → ↥(irreducibleComponents (towerChain q n a ha i)) → ℤ :=
  fun i => eulerMultidegree (towerChain q n a ha i)
    (towerChainInclusion q n a ha i ≫ multiStructure (q + 1) n a) (restrictToTower q n a ha i p)

theorem locusEulerMultidegree_one : locusEulerMultidegree q n a ha 1 = 0 := by
  funext i
  show eulerMultidegree (towerChain q n a ha i)
    (towerChainInclusion q n a ha i ≫ multiStructure (q + 1) n a) (restrictToTower q n a ha i 1) = 0
  rw [map_one, eulerMultidegree_one]

include hyp htrans in
/-- **`Pic(exceptional locus of S_{p,n}) ≅ ∏ᵢ ℤ^{components of the i-th chain}` in Euler-degree
form**: the Euler multidegrees of the restrictions to the chains form a bijection. -/
theorem locusEulerMultidegree_bijective : Function.Bijective (locusEulerMultidegree q n a ha) := by
  show Function.Bijective ((Equiv.piCongrRight fun i => Equiv.ofBijective _
    (towerChain_rationalTreePicard_degrees q n a ha hyp htrans i)) ∘ restrictionToChains q n a ha)
  exact (Equiv.bijective _).comp (restrictionToChains_bijective q n a ha)

include hyp htrans in
/-- A class of the exceptional locus of Euler degree zero on every exceptional curve is trivial. -/
theorem locus_eq_one_of_eulerDegree_zero (p : (exceptionalScheme q n a).Pic)
    (hp : locusEulerMultidegree q n a ha p = 0) : p = 1 :=
  (locusEulerMultidegree_bijective q n a ha hyp htrans).1
    (hp.trans (locusEulerMultidegree_one q n a ha).symm)

include hyp htrans in
/-- **The half-class clause on the whole exceptional locus in Euler-degree form**: a class of
`S_{p,n}` whose double has Euler degree zero on every exceptional curve restricts trivially to the
exceptional locus. -/
theorem locus_halfClass_trivial_of_eulerDegree (M : (multiSurface (q + 1) n a).Pic)
    (h : locusEulerMultidegree q n a ha
      (schemePicardPullbackHom (exceptionalInclusion q n a) (M ^ 2)) = 0) :
    schemePicardPullbackHom (exceptionalInclusion q n a) M = 1 := by
  apply locus_halfClass_trivial q n a ha hyp htrans M
  apply (locusEulerMultidegree_bijective q n a ha hyp htrans).1
  rw [h, locusEulerMultidegree_one]

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (q₀ n₀ : ℕ) (a₀ : Fin n₀ → k₀)
    (ha₀ : Function.Injective a₀) (hyp₀ : SinglePoints q₀ n₀ a₀)
    (htrans₀ : TowerTransversal q₀ n₀ a₀ ha₀ hyp₀) :
    Function.Bijective (locusEulerMultidegree q₀ n₀ a₀ ha₀) :=
  locusEulerMultidegree_bijective q₀ n₀ a₀ ha₀ hyp₀ htrans₀

end MultiCentre

end KltDP.Examples.FrobeniusExceptionalEulerDegrees
