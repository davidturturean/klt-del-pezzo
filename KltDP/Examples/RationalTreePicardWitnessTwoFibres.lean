import KltDP.Examples.ProjectiveProductOriginStalkRegular
import KltDP.Examples.FrobeniusStageNoetherianFiniteType
import KltDP.Examples.FrobeniusUnaffectedFibers
import KltDP.Geometry.RationalTreePicardDualGraphTransport

/-!
# Witness (b): the two fibres `x = 0`, `y = 0` of `P¹ × P¹`

BRIEF21, task 2. Let `h = horizontalFiberMorphism 0 : P¹ ⟶ P¹ × P¹` be the fibre `y = 0` and
`v = verticalFiberMorphismAt 0` the fibre `x = 0` (accepted closed immersions, sections of the two
projections). Their union `twoFibresScheme` is the reduced closed subscheme of `P¹ × P¹` on
`range h ∪ range v` (glued vanishing ideal, as in BRIEF19's exceptional chain); the two curves lift
to closed immersions `twoFibresCurve 0 = h`, `twoFibresCurve 1 = v` into it, cover it, and are
incomparable. The two fibres meet in exactly one point, the rational point `(0, 0)` = `h(q₀)` with
`q₀ = [1:0]` (`twoFibres_inter_eq`): a common point `z = h p = v p'` has `x`-coordinate `p` (from
`h ≫ fst = 𝟙`) and `x`-coordinate `[1:0]` (from `v ≫ fst = toSpec ≫ pointMorphism 0`), so `p = q₀`;
and `h q₀ = v q₀` because both `pointMorphism 0 ≫ h` and `pointMorphism 0 ≫ v` are the point
`([1:0], [1:0])` of the fibre product (`pullback.hom_ext`). Hence the two components form a chain
with `m = 1` (`twoFibres_isChain`), the incidence graph is a tree, the dimension is one, and
`P¹ × P¹` is Noetherian, locally Noetherian and proper over `k` (BRIEF20).

**What is carried as a hypothesis in this module**: the transversality of the crossing at the
node, `hcross : TransversalCrossing twoFibresInclusion (twoFibresComponent 0) (twoFibresComponent 1)
twoFibresNode` in BRIEF18's stalk form. Given it, the union is a transversal configuration
(`twoFibres_transversalConfiguration`: no triple points, and the only common point is the node) and
**`Pic(x = 0 ∪ y = 0) ≃* ℤ²`** (`twoFibresPicardEquiv`), with the degree-zero clause. The regularity
and dimension of the ambient stalk at the origin are proved in
`ProjectiveProductOriginStalkRegular`; the identification of the node with `productOrigin`, the
chart ideal `(u) ∩ (v) = (uv)` and the stalk kernel are the remaining inputs of `hcross`
(recorded in `LEMMA22_PROGRESS.md`, Task 21).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace CategoryTheory.Limits

universe u

namespace KltDP.Examples.RationalTreePicardWitnessTwoFibres

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusGraphPicardClassZeroFiber
  FrobeniusUnaffectedFibers FrobeniusStageNoetherianFiniteType FrobeniusMultiCentreSurface

variable {k : Type u} [Field k]

local instance projectiveLine_isIntegral' : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-! ## The two fibres and their intersection -/

/-- The two fibres: `0 ↦ y = 0` (horizontal), `1 ↦ x = 0` (vertical). -/
def fibre : Fin 2 → (projectiveSpace k 1 ⟶ projectiveProduct k) :=
  ![horizontalFiberMorphism (0 : k), verticalFiberMorphismAt (0 : k)]

theorem fibre_zero : fibre (k := k) 0 = horizontalFiberMorphism 0 := rfl

theorem fibre_one : fibre (k := k) 1 = verticalFiberMorphismAt 0 := rfl

instance fibre_isClosedImmersion (i : Fin 2) : IsClosedImmersion (fibre (k := k) i) := by
  fin_cases i
  · exact (inferInstance : IsClosedImmersion (horizontalFiberMorphism (0 : k)))
  · exact (inferInstance : IsClosedImmersion (verticalFiberMorphismAt (0 : k)))

/-- The point of `Spec k`. -/
def specPoint : Spec (CommRingCat.of k) := ⟨⊥, Ideal.bot_prime⟩

theorem spec_subsingleton (p q : Spec (CommRingCat.of k)) : p = q :=
  PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)

/-- The rational point `[1:0]` of `P¹`. -/
def q₀ : projectiveSpace k 1 := (pointMorphism (0 : k)).base specPoint

theorem fst_horizontal (p : projectiveSpace k 1) :
    (firstProjection (k := k)).base ((horizontalFiberMorphism (0 : k)).base p) = p := by
  rw [← Scheme.comp_base_apply, horizontalFiberMorphism_fst]
  rfl

theorem snd_vertical (p : projectiveSpace k 1) :
    (secondProjection (k := k)).base ((verticalFiberMorphismAt (0 : k)).base p) = p := by
  rw [← Scheme.comp_base_apply, verticalFiberMorphismAt_snd]
  rfl

theorem fst_vertical (p : projectiveSpace k 1) :
    (firstProjection (k := k)).base ((verticalFiberMorphismAt (0 : k)).base p) = q₀ := by
  rw [← Scheme.comp_base_apply, verticalFiberMorphismAt_fst, Scheme.comp_base_apply, q₀]
  exact congrArg _ (spec_subsingleton _ _)

theorem snd_horizontal (p : projectiveSpace k 1) :
    (secondProjection (k := k)).base ((horizontalFiberMorphism (0 : k)).base p) = q₀ := by
  rw [← Scheme.comp_base_apply, horizontalFiberMorphism_snd, Scheme.comp_base_apply, q₀]
  exact congrArg _ (spec_subsingleton _ _)

/-- Both fibres pass through the point `([1:0], [1:0])`: the two morphisms `Spec k ⟶ P¹ × P¹`
agree. -/
theorem pointMorphism_comp_fibres :
    pointMorphism (0 : k) ≫ verticalFiberMorphismAt 0 =
      pointMorphism (0 : k) ≫ horizontalFiberMorphism 0 := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, verticalFiberMorphismAt_fst, horizontalFiberMorphism_fst,
      Category.comp_id, ← Category.assoc, pointMorphism_over_base, Category.id_comp]
  · rw [Category.assoc, Category.assoc, verticalFiberMorphismAt_snd, horizontalFiberMorphism_snd,
      Category.comp_id, ← Category.assoc, pointMorphism_over_base, Category.id_comp]

theorem vertical_q₀_eq_horizontal_q₀ :
    (verticalFiberMorphismAt (0 : k)).base q₀ = (horizontalFiberMorphism (0 : k)).base q₀ := by
  have h := congrArg (fun f => f.base (specPoint (k := k))) pointMorphism_comp_fibres
  simpa only [Scheme.comp_base_apply] using h

/-- The two fibres meet in at most one point. -/
theorem twoFibres_inter_subsingleton :
    (Set.range (horizontalFiberMorphism (0 : k)).base ∩
      Set.range (verticalFiberMorphismAt (0 : k)).base).Subsingleton := by
  rintro _ ⟨⟨p, rfl⟩, ⟨p', hp'⟩⟩ _ ⟨⟨r, rfl⟩, ⟨r', hr'⟩⟩
  have hp : p = q₀ := by
    rw [← fst_horizontal p, ← hp', fst_vertical]
  have hr : r = q₀ := by
    rw [← fst_horizontal r, ← hr', fst_vertical]
  rw [hp, hr]

/-- The two fibres meet. -/
theorem twoFibres_inter_nonempty :
    (Set.range (horizontalFiberMorphism (0 : k)).base ∩
      Set.range (verticalFiberMorphismAt (0 : k)).base).Nonempty :=
  ⟨_, ⟨q₀, rfl⟩, q₀, vertical_q₀_eq_horizontal_q₀⟩

theorem twoFibres_inter_eq :
    Set.range (horizontalFiberMorphism (0 : k)).base ∩
      Set.range (verticalFiberMorphismAt (0 : k)).base =
      {(horizontalFiberMorphism (0 : k)).base q₀} :=
  twoFibres_inter_subsingleton.eq_singleton_of_mem ⟨⟨q₀, rfl⟩, q₀, vertical_q₀_eq_horizontal_q₀⟩

/-! ## The union as a reduced closed subscheme -/

/-- The support `{x = 0} ∪ {y = 0}`. -/
def twoFibresLocus : Set (projectiveProduct k) := ⋃ i : Fin 2, Set.range (fibre (k := k) i).base

theorem twoFibresLocus_isClosed : IsClosed (twoFibresLocus (k := k)) :=
  isClosed_iUnion_of_finite fun i => (fibre (k := k) i).isClosedEmbedding.isClosed_range

theorem range_fibre_subset_locus (i : Fin 2) :
    Set.range (fibre (k := k) i).base ⊆ twoFibresLocus :=
  Set.subset_iUnion (fun i : Fin 2 => Set.range (fibre (k := k) i).base) i

/-- The vanishing ideal sheaf of the union of the two fibres. -/
def twoFibresIdeal : (projectiveProduct k).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨twoFibresLocus, twoFibresLocus_isClosed⟩

/-- The union of the two fibres as a reduced closed subscheme of `P¹ × P¹`. -/
def twoFibresScheme : Scheme.{u} := (twoFibresIdeal (k := k)).glueData.glued

/-- Its inclusion into `P¹ × P¹`. -/
def twoFibresInclusion : twoFibresScheme (k := k) ⟶ projectiveProduct k :=
  (twoFibresIdeal (k := k)).gluedTo

instance twoFibresInclusion_isClosedImmersion : IsClosedImmersion (twoFibresInclusion (k := k)) :=
  (twoFibresIdeal (k := k)).gluedTo_isClosedImmersion

instance twoFibresScheme_isReduced : AlgebraicGeometry.IsReduced (twoFibresScheme (k := k)) :=
  (twoFibresIdeal (k := k)).glued_isReduced
    (Scheme.IdealSheafData.vanishingIdeal_support (I := twoFibresIdeal (k := k))).symm

theorem range_twoFibresInclusion :
    Set.range (twoFibresInclusion (k := k)).base = twoFibresLocus :=
  (twoFibresIdeal (k := k)).range_gluedTo

theorem twoFibresInclusion_injective : Function.Injective (twoFibresInclusion (k := k)).base :=
  (twoFibresInclusion (k := k)).isClosedEmbedding.injective

theorem range_fibre_subset_range (i : Fin 2) :
    Set.range (fibre (k := k) i).base ⊆ Set.range (twoFibresInclusion (k := k)).base := by
  rw [range_twoFibresInclusion]
  exact range_fibre_subset_locus i

theorem twoFibresIdeal_le_ker (i : Fin 2) : twoFibresIdeal (k := k) ≤ (fibre i).ker := by
  refine le_trans ?_ (vanishingIdeal_le_ker (fibre i)
    ⟨Set.range (fibre (k := k) i).base, (fibre (k := k) i).isClosedEmbedding.isClosed_range⟩ rfl)
  exact Scheme.IdealSheafData.vanishingIdeal_antimono (range_fibre_subset_locus i)

/-- The fibres as closed immersions of `P¹` into the union (indexed in universe `u`, as the
configuration corollary requires). -/
def twoFibresCurve (i : ULift.{u} (Fin 2)) : projectiveSpace k 1 ⟶ twoFibresScheme (k := k) :=
  liftGluedTo (twoFibresIdeal (k := k)) (fibre i.down) (twoFibresIdeal_le_ker i.down)

theorem twoFibresCurve_comp (i : ULift.{u} (Fin 2)) :
    twoFibresCurve (k := k) i ≫ twoFibresInclusion = fibre i.down :=
  liftGluedTo_gluedTo _ _ _

instance twoFibresCurve_isClosedImmersion (i : ULift.{u} (Fin 2)) :
    IsClosedImmersion (twoFibresCurve (k := k) i) := by
  haveI : IsClosedImmersion (twoFibresCurve (k := k) i ≫ twoFibresInclusion) := by
    rw [twoFibresCurve_comp]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (twoFibresInclusion (k := k))

theorem range_twoFibresCurve_eq (i : ULift.{u} (Fin 2)) :
    Set.range (twoFibresCurve (k := k) i).base =
      (twoFibresInclusion (k := k)).base ⁻¹' Set.range (fibre (k := k) i.down).base := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    show (twoFibresInclusion (k := k)).base ((twoFibresCurve i).base p) ∈
      Set.range (fibre (k := k) i.down).base
    rw [← Scheme.comp_base_apply, twoFibresCurve_comp]
    exact ⟨p, rfl⟩
  · intro hx
    obtain ⟨p, hp⟩ := (show (twoFibresInclusion (k := k)).base x ∈
      Set.range (fibre (k := k) i.down).base from hx)
    refine ⟨p, twoFibresInclusion_injective ?_⟩
    rw [← Scheme.comp_base_apply, twoFibresCurve_comp]
    exact hp

theorem twoFibresCurve_cover :
    ⋃ i : ULift.{u} (Fin 2), Set.range (twoFibresCurve (k := k) i).base = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : (twoFibresInclusion (k := k)).base x ∈ twoFibresLocus := by
    rw [← range_twoFibresInclusion]
    exact ⟨x, rfl⟩
  unfold twoFibresLocus at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr ⟨ULift.up i, ?_⟩
  rw [range_twoFibresCurve_eq]
  exact hi

/-- The support of a fibre in `P¹ × P¹`, indexed for the chain lemmas. -/
def fibreSupport (i : Fin 2) : Set (projectiveProduct k) := Set.range (fibre (k := k) i).base

theorem fibreSupport_subsingleton (j : Fin 1) :
    (fibreSupport (k := k) j.castSucc ∩ fibreSupport j.succ).Subsingleton := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  exact twoFibres_inter_subsingleton

theorem fibreSupport_nonempty (j : Fin 1) :
    (fibreSupport (k := k) j.castSucc ∩ fibreSupport j.succ).Nonempty := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  exact twoFibres_inter_nonempty

theorem fibreSupport_disjoint (i j : Fin 2) (hij : i.val + 1 < j.val) :
    Disjoint (fibreSupport (k := k) i) (fibreSupport j) := by
  have := i.isLt
  have := j.isLt
  omega

theorem fibreSupport_not_subsingleton (i : Fin 2) : ¬ (fibreSupport (k := k) i).Subsingleton := by
  haveI : Nontrivial (projectiveSpace k 1) :=
    FrobeniusExceptionalChainPicard.projectiveLine_nontrivial (k := k)
  intro hs
  obtain ⟨a, b, hab⟩ := exists_pair_ne (projectiveSpace k 1)
  have ha : (fibre (k := k) i).base a ∈ fibreSupport i := ⟨a, rfl⟩
  have hb : (fibre (k := k) i).base b ∈ fibreSupport i := ⟨b, rfl⟩
  exact hab ((fibre (k := k) i).isClosedEmbedding.injective (hs ha hb))

theorem twoFibresCurve_distinct (i j : ULift.{u} (Fin 2))
    (h : Set.range (twoFibresCurve (k := k) i).base ⊆ Set.range (twoFibresCurve (k := k) j).base) :
    i = j := by
  have hS : fibreSupport (k := k) i.down ⊆ fibreSupport j.down := by
    show Set.range (fibre (k := k) i.down).base ⊆ Set.range (fibre (k := k) j.down).base
    rw [← Set.image_preimage_eq_of_subset (range_fibre_subset_range i.down),
      ← range_twoFibresCurve_eq i]
    calc (twoFibresInclusion (k := k)).base '' Set.range (twoFibresCurve i).base
        ⊆ (twoFibresInclusion (k := k)).base '' Set.range (twoFibresCurve j).base :=
          Set.image_mono h
      _ = Set.range (fibre (k := k) j.down).base := by
        rw [range_twoFibresCurve_eq j,
          Set.image_preimage_eq_of_subset (range_fibre_subset_range j.down)]
  have hij := chain_not_subset (fibreSupport (k := k)) fibreSupport_subsingleton
    fibreSupport_disjoint fibreSupport_not_subsingleton i.down j.down hS
  cases i
  cases j
  cases hij
  rfl

/-! ## The configuration -/

local instance projectiveProduct_noetherianSpace' : NoetherianSpace (projectiveProduct k) :=
  projectiveProduct_noetherianSpace

local instance projectiveProduct_isLocallyNoetherian' : IsLocallyNoetherian (projectiveProduct k) :=
  projectiveProduct_isLocallyNoetherian

instance twoFibresScheme_noetherianSpace : NoetherianSpace (twoFibresScheme (k := k)) :=
  noetherianSpace_of_isClosedImmersion (twoFibresInclusion (k := k))

instance twoFibresScheme_isLocallyNoetherian : IsLocallyNoetherian (twoFibresScheme (k := k)) :=
  isLocallyNoetherian_of_isClosedImmersion (twoFibresInclusion (k := k))

/-- The two components of the union, indexed by `Fin 2`. -/
def twoFibresComponent : Fin 2 ≃ ↥(irreducibleComponents (twoFibresScheme (k := k))) :=
  Equiv.ulift.symm.trans (curveComponentEquiv (twoFibresScheme (k := k))
    (fun _ => projectiveSpace k 1) twoFibresCurve (fun _ => projectiveLine_isIntegral)
    twoFibresCurve_cover twoFibresCurve_distinct)

theorem twoFibresComponent_val (i : Fin 2) :
    (twoFibresComponent (k := k) i).1 = Set.range (twoFibresCurve (k := k) (ULift.up i)).base :=
  rfl

/-- The two components form a chain (`m = 1`). -/
theorem twoFibres_isChain : IsChain (twoFibresScheme (k := k)) twoFibresComponent where
  subsingleton j := by
    rw [twoFibresComponent_val, twoFibresComponent_val, range_twoFibresCurve_eq,
      range_twoFibresCurve_eq, ← Set.preimage_inter]
    exact (fibreSupport_subsingleton j).preimage twoFibresInclusion_injective
  nonempty j := by
    rw [twoFibresComponent_val, twoFibresComponent_val, range_twoFibresCurve_eq,
      range_twoFibresCurve_eq, ← Set.preimage_inter]
    exact (fibreSupport_nonempty j).preimage'
      (Set.inter_subset_left.trans (range_fibre_subset_range j.castSucc))
  disjoint i j hij := by
    rw [twoFibresComponent_val, twoFibresComponent_val, range_twoFibresCurve_eq,
      range_twoFibresCurve_eq]
    exact (fibreSupport_disjoint i j hij).preimage (twoFibresInclusion (k := k)).base

theorem twoFibres_isTree : (componentPointIncidenceGraph (twoFibresScheme (k := k))).IsTree :=
  isTree_of_chain (twoFibresScheme (k := k)) twoFibresComponent twoFibres_isChain

theorem twoFibres_dim : topologicalKrullDim (twoFibresScheme (k := k)) ≤ 1 :=
  topologicalKrullDim_le_one_of_curves (twoFibresScheme (k := k)) (fun _ => projectiveSpace k 1)
    twoFibresCurve twoFibresCurve_cover
    (fun _ => FrobeniusExceptionalChainPicard.projectiveLine_dim_le_one)

/-- The node `(0, 0)` of the union, as a point of `twoFibresScheme`. -/
def twoFibresNode : twoFibresScheme (k := k) := (twoFibresCurve (k := k) (ULift.up 0)).base q₀

theorem twoFibresInclusion_node :
    (twoFibresInclusion (k := k)).base twoFibresNode = (horizontalFiberMorphism (0 : k)).base q₀ := by
  rw [twoFibresNode, ← Scheme.comp_base_apply, twoFibresCurve_comp]
  rfl

/-- A point of both components is the node. -/
theorem eq_node_of_mem (x : twoFibresScheme (k := k))
    (h0 : x ∈ (twoFibresComponent (k := k) 0).1) (h1 : x ∈ (twoFibresComponent (k := k) 1).1) :
    x = twoFibresNode := by
  rw [twoFibresComponent_val, range_twoFibresCurve_eq] at h0 h1
  apply twoFibresInclusion_injective
  rw [twoFibresInclusion_node]
  have hmem : (twoFibresInclusion (k := k)).base x ∈
      Set.range (horizontalFiberMorphism (0 : k)).base ∩
        Set.range (verticalFiberMorphismAt (0 : k)).base := ⟨h0, h1⟩
  rw [twoFibres_inter_eq] at hmem
  exact hmem

/-- **Hypothesis carried in this module**: the crossing of the two fibres at the node is
transversal in the stalk form of BRIEF18. -/
def TwoFibresCrossing : Prop :=
  TransversalCrossing (twoFibresInclusion (k := k)) (twoFibresComponent 0) (twoFibresComponent 1)
    twoFibresNode

/-- Given the crossing at the node, the union of the two fibres is a transversal configuration. -/
theorem twoFibres_transversalConfiguration (hcross : TwoFibresCrossing (k := k)) :
    TransversalConfiguration (twoFibresInclusion (k := k)) where
  no_triple C D E _ _ _ _ := by
    set e := twoFibresComponent (k := k) with he
    have ha := (e.symm C).isLt
    have hb := (e.symm D).isLt
    have hc := (e.symm E).isLt
    rcases (show (e.symm C).val = (e.symm D).val ∨ (e.symm C).val = (e.symm E).val ∨
        (e.symm D).val = (e.symm E).val by omega) with h | h | h
    · exact Or.inl (e.symm.injective (Fin.ext h))
    · exact Or.inr (Or.inl (e.symm.injective (Fin.ext h)))
    · exact Or.inr (Or.inr (e.symm.injective (Fin.ext h)))
  crossing C D hCD x hC hD := by
    set e := twoFibresComponent (k := k) with he
    have hab : (e.symm C).val ≠ (e.symm D).val := fun h => hCD (e.symm.injective (Fin.ext h))
    have ha := (e.symm C).isLt
    have hb := (e.symm D).isLt
    have hCe : C = e (e.symm C) := (e.apply_symm_apply C).symm
    have hDe : D = e (e.symm D) := (e.apply_symm_apply D).symm
    rcases (show ((e.symm C).val = 0 ∧ (e.symm D).val = 1) ∨
        ((e.symm C).val = 1 ∧ (e.symm D).val = 0) by omega) with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · have hC' : C = e 0 := by rw [hCe]; exact congrArg e (Fin.ext h0)
      have hD' : D = e 1 := by rw [hDe]; exact congrArg e (Fin.ext h1)
      have hx : x = twoFibresNode := eq_node_of_mem x (hC' ▸ hC) (hD' ▸ hD)
      rw [hC', hD', hx]
      exact hcross
    · have hC' : C = e 1 := by rw [hCe]; exact congrArg e (Fin.ext h1)
      have hD' : D = e 0 := by rw [hDe]; exact congrArg e (Fin.ext h0)
      have hx : x = twoFibresNode := eq_node_of_mem x (hD' ▸ hD) (hC' ▸ hC)
      rw [hC', hD', hx]
      exact hcross.symm

/-! ## The Picard group -/

section Picard

variable [IsAlgClosed k] (hcross : TwoFibresCrossing (k := k))

local instance projectiveProductToSpec_locallyOfFiniteType :
    LocallyOfFiniteType (projectiveProductToSpec (k := k)) :=
  inferInstance

include hcross in
/-- **Witness (b), modulo the crossing at the node**: the multidegree map of the union of the two
fibres is bijective. -/
theorem twoFibres_rationalTreePicard :
    Function.Bijective (multidegreeHom k (twoFibresScheme (k := k))
      (lineIdentification (twoFibresScheme (k := k)) twoFibresCurve twoFibresCurve_cover
        twoFibresCurve_distinct)) :=
  rationalTreePicard_of_configuration (twoFibresScheme (k := k)) twoFibresInclusion
    projectiveProductToSpec (twoFibres_transversalConfiguration hcross) twoFibres_dim
    twoFibres_isTree twoFibresCurve twoFibresCurve_cover twoFibresCurve_distinct

/-- `Pic(x = 0 ∪ y = 0) ≃* ℤ²`, modulo the crossing at the node. -/
def twoFibresPicardEquiv : (twoFibresScheme (k := k)).Pic ≃* (Fin 2 → Multiplicative ℤ) :=
  (picardEquiv_of_configuration (twoFibresScheme (k := k)) twoFibresInclusion
    projectiveProductToSpec (twoFibres_transversalConfiguration hcross) twoFibres_dim
    twoFibres_isTree twoFibresCurve twoFibresCurve_cover twoFibresCurve_distinct).trans
    (MulEquiv.arrowCongr Equiv.ulift (MulEquiv.refl (Multiplicative ℤ)))

include hcross in
/-- A line bundle on the union with exponent zero on both fibres is trivial (modulo the crossing). -/
theorem twoFibres_trivial_of_degree_zero (L : InvertibleSheaf (twoFibresScheme (k := k)))
    (hL : ∀ i : ULift.{u} (Fin 2), componentExponent k (twoFibresScheme (k := k))
      {lineComponent (twoFibresScheme (k := k)) twoFibresCurve twoFibresCurve_cover
        twoFibresCurve_distinct i}
      (lineIdentification (twoFibresScheme (k := k)) twoFibresCurve twoFibresCurve_cover
        twoFibresCurve_distinct
        (lineComponent (twoFibresScheme (k := k)) twoFibresCurve twoFibresCurve_cover
          twoFibresCurve_distinct i)) L = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit (twoFibresScheme (k := k)).ringCatSheaf) :=
  trivial_of_degree_zero_of_configuration (twoFibresScheme (k := k)) twoFibresInclusion
    projectiveProductToSpec (twoFibres_transversalConfiguration hcross) twoFibres_dim
    twoFibres_isTree twoFibresCurve twoFibresCurve_cover twoFibresCurve_distinct L hL

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (hcross : TwoFibresCrossing (k := k₀)) :
    (twoFibresScheme (k := k₀)).Pic ≃* (Fin 2 → Multiplicative ℤ) :=
  twoFibresPicardEquiv hcross

end Picard

end KltDP.Examples.RationalTreePicardWitnessTwoFibres
