import KltDP.Geometry.PicardClopenDecomposition
import KltDP.Examples.FrobeniusMultiCentreHalfClass

/-!
# The Picard group of the whole exceptional locus of `S_{p,n}`

BRIEF23, task 2. The exceptional locus `exceptionalScheme q n a` of `S_{p,n}` (task 22) is the
disjoint union of the `n` chains `towerChain i` (closed immersions `towerToLocus i` with pairwise
disjoint ranges covering the locus, lane F's disjointness of the towers' exceptional curves).
Each range is therefore clopen (`chainOpen i`), the chain maps isomorphically onto its clopen
piece (`chainToOpen`: a surjective closed immersion into the reduced open subscheme is an
isomorphism, Mathlib `isIso_of_isClosedImmersion_of_surjective`), and the Picard group of a clopen
decomposition is the product of the Picard groups of the pieces (`PicardClopenDecomposition`).
Hence **`Pic(exceptional locus) ≃* ∏ᵢ Pic(towerChain i) ≃* ℤ^{n(q+1)}`** (`locusPicardEquivPi`,
`locusPicardEquiv`, modulo lane F's per-tower `SinglePoints`/`TowerTransversal`), the
tower-by-tower degree `exceptionalDegree` of task 22 is bijective (`exceptionalDegree_bijective`),
a class of the locus with degree zero on every exceptional curve is trivial
(`locus_eq_one_of_degree_zero`), a class with even degrees is a square (`locus_exists_sq_of_even`),
and the manuscript's half-class clause holds on the whole locus (`locus_halfClass_trivial`).

The clopen pieces are indexed by `ULift (Fin n)` because the decomposition theorem needs an index
type in universe `u`; the identification of the chain with its piece uses that a surjective closed
immersion into a reduced scheme is an isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreLocusPicard

open KltDP.Geometry KltDP.Geometry.RationalTreePicard KltDP.Geometry.PicardClopenDecomposition
  FrobeniusMultiCentreSurface FrobeniusMultiCentreChainPicard FrobeniusMultiCentreHalfClass
  FrobeniusExceptionalChainPicard

variable {k : Type u} [Field k] [IsAlgClosed k] (q n : ℕ) (a : Fin n → k)
  (ha : Function.Injective a)

/-! ## The chains as clopen pieces of the locus -/

/-- The range of the `i`-th chain in the exceptional locus. -/
def chainRange (i : Fin n) : Set (exceptionalScheme q n a) :=
  Set.range (towerToLocus q n a ha i).base

theorem chainRange_isClosed (i : Fin n) : IsClosed (chainRange q n a ha i) :=
  (towerToLocus q n a ha i).isClosedEmbedding.isClosed_range

theorem chainRange_disjoint {i j : Fin n} (hij : i ≠ j) :
    Disjoint (chainRange q n a ha i) (chainRange q n a ha j) := by
  rw [Set.disjoint_left]
  rintro z ⟨y, rfl⟩ ⟨y', hy'⟩
  have h1 : (exceptionalInclusion q n a).base ((towerToLocus q n a ha i).base y) ∈
      Set.range (towerChainInclusion q n a ha i).base :=
    ⟨y, by rw [← towerToLocus_comp q n a ha i, Scheme.comp_base_apply]⟩
  have h2 : (exceptionalInclusion q n a).base ((towerToLocus q n a ha i).base y) ∈
      Set.range (towerChainInclusion q n a ha j).base :=
    ⟨y', by rw [← towerToLocus_comp q n a ha j, Scheme.comp_base_apply, hy']⟩
  exact Set.disjoint_left.mp (towerChain_range_disjoint q n a ha hij) h1 h2

theorem chainRange_cover (z : exceptionalScheme q n a) : ∃ i, z ∈ chainRange q n a ha i := by
  have hz : (exceptionalInclusion q n a).base z ∈ exceptionalLocus q n a := by
    rw [← range_exceptionalInclusion]
    exact ⟨z, rfl⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  obtain ⟨idx, hidx⟩ := Set.mem_iUnion.mp hi
  have hidx' : (exceptionalInclusion q n a).base z ∈
      Set.range (chainCurve q n a ha i ((chainEquiv.{0} q).symm idx)).base := by
    rw [range_chainCurve]
    have h : chainMember.{0} q ((chainEquiv.{0} q).symm idx) = idx :=
      (chainEquiv.{0} q).apply_symm_apply idx
    rw [h]
    exact hidx
  have hx : (exceptionalInclusion q n a).base z ∈ Set.range (towerChainInclusion q n a ha i).base :=
    CurveChain.support_subset_range (multiSurface (q + 1) n a) q (chainCurve q n a ha i) _ hidx'
  obtain ⟨y, hy⟩ := hx
  refine ⟨i, y, ?_⟩
  apply (exceptionalInclusion q n a).isClosedEmbedding.injective
  rw [← Scheme.comp_base_apply, towerToLocus_comp]
  exact hy

theorem chainRange_isOpen (i : Fin n) : IsOpen (chainRange q n a ha i) := by
  rw [← isClosed_compl_iff]
  have h : (chainRange q n a ha i)ᶜ = ⋃ j ∈ ({j | j ≠ i} : Set (Fin n)), chainRange q n a ha j := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, hj⟩ := chainRange_cover q n a ha z
      have hji : j ≠ i := fun h => hz (h ▸ hj)
      exact Set.mem_iUnion₂.mpr ⟨j, hji, hj⟩
    · intro hz hzi
      obtain ⟨j, hji, hj⟩ := Set.mem_iUnion₂.mp hz
      exact Set.disjoint_left.mp (chainRange_disjoint q n a ha hji) hj hzi
  rw [h]
  exact (Set.toFinite _).isClosed_biUnion fun j _ => chainRange_isClosed q n a ha j

/-- The `i`-th chain as a clopen open of the locus. -/
def chainOpen (i : Fin n) : (exceptionalScheme q n a).Opens :=
  ⟨chainRange q n a ha i, chainRange_isOpen q n a ha i⟩

theorem chainOpen_disjoint (i j : Fin n) (hij : i ≠ j) :
    chainOpen q n a ha i ⊓ chainOpen q n a ha j = ⊥ := by
  apply Opens.ext
  exact Set.disjoint_iff_inter_eq_empty.mp (chainRange_disjoint q n a ha hij)

theorem chainOpen_iSup : (⨆ i, chainOpen q n a ha i) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨i, hi⟩ := chainRange_cover q n a ha z
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

/-- The clopen pieces, indexed in universe `u` (as the decomposition theorem requires). -/
abbrev chainOpenU : ULift.{u} (Fin n) → (exceptionalScheme q n a).Opens :=
  fun i => chainOpen q n a ha i.down

theorem chainOpenU_disjoint (i j : ULift.{u} (Fin n)) (hij : i ≠ j) :
    chainOpenU q n a ha i ⊓ chainOpenU q n a ha j = ⊥ :=
  chainOpen_disjoint q n a ha i.down j.down (fun h => hij (ULift.ext i j h))

theorem chainOpenU_iSup : (⨆ i, chainOpenU q n a ha i) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨i, hi⟩ := chainRange_cover q n a ha z
  exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩

local instance uliftFin_decidableEq : DecidableEq (ULift.{u} (Fin n)) := Equiv.ulift.decidableEq

/-! ## The chain is its clopen piece -/

/-- The chain maps into its clopen piece. -/
def chainToOpen (i : Fin n) : towerChain q n a ha i ⟶ (chainOpen q n a ha i).toScheme :=
  IsOpenImmersion.lift (chainOpen q n a ha i).ι (towerToLocus q n a ha i)
    (by rw [Scheme.Opens.range_ι]; exact subset_rfl)

theorem chainToOpen_ι (i : Fin n) :
    chainToOpen q n a ha i ≫ (chainOpen q n a ha i).ι = towerToLocus q n a ha i :=
  IsOpenImmersion.lift_fac _ _ _

instance chainToOpen_isPreimmersion (i : Fin n) : IsPreimmersion (chainToOpen q n a ha i) := by
  haveI : IsPreimmersion (chainToOpen q n a ha i ≫ (chainOpen q n a ha i).ι) := by
    rw [chainToOpen_ι]
    infer_instance
  exact IsPreimmersion.of_comp _ (chainOpen q n a ha i).ι

theorem chainToOpen_surjective (i : Fin n) : Function.Surjective (chainToOpen q n a ha i).base := by
  rintro ⟨z, hz⟩
  obtain ⟨y, hy⟩ := hz
  refine ⟨y, ?_⟩
  apply (chainOpen q n a ha i).ι.isOpenEmbedding.injective
  rw [← Scheme.comp_base_apply, chainToOpen_ι]
  exact hy

instance chainToOpen_isClosedImmersion (i : Fin n) : IsClosedImmersion (chainToOpen q n a ha i) :=
  IsClosedImmersion.of_isPreimmersion _
    (by rw [Set.range_eq_univ.mpr (chainToOpen_surjective q n a ha i)]; exact isClosed_univ)

instance chainToOpen_surjectiveClass (i : Fin n) : Surjective (chainToOpen q n a ha i) :=
  ⟨chainToOpen_surjective q n a ha i⟩

instance chainOpen_isReduced (i : Fin n) :
    AlgebraicGeometry.IsReduced (chainOpen q n a ha i).toScheme :=
  isReduced_of_isOpenImmersion (chainOpen q n a ha i).ι

/-- **The chain is isomorphic to its clopen piece of the locus.** -/
instance chainToOpen_isIso (i : Fin n) : IsIso (chainToOpen q n a ha i) :=
  isIso_of_isClosedImmersion_of_surjective _

/-! ## Picard groups -/

/-- Pullback along an isomorphism of schemes is an isomorphism of Picard groups. -/
def picardEquivOfIso {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsIso g] : Z.Pic ≃* Y.Pic where
  toFun := schemePicardPullbackHom g
  invFun := schemePicardPullbackHom (inv g)
  left_inv c := by
    rw [← MonoidHom.comp_apply, ← schemePicardPullbackHom_comp, IsIso.inv_hom_id,
      schemePicardPullbackHom_id]
    rfl
  right_inv c := by
    rw [← MonoidHom.comp_apply, ← schemePicardPullbackHom_comp, IsIso.hom_inv_id,
      schemePicardPullbackHom_id]
    rfl
  map_mul' := map_mul _

theorem picardEquivOfIso_apply {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsIso g] (c : Z.Pic) :
    picardEquivOfIso g c = schemePicardPullbackHom g c := rfl

/-- Restriction of Picard classes of the locus to all the chains. -/
def restrictionToChains :
    (exceptionalScheme q n a).Pic →* (∀ i : Fin n, (towerChain q n a ha i).Pic) :=
  Pi.monoidHom fun i => restrictToTower q n a ha i

theorem restrictionToChains_apply (c : (exceptionalScheme q n a).Pic) (i : Fin n) :
    restrictionToChains q n a ha c i = restrictToTower q n a ha i c := rfl

/-- Restricting to a chain is restricting to its clopen piece and then pulling back along the
isomorphism `chainToOpen`. -/
theorem restrictionToChains_apply_eq (c : (exceptionalScheme q n a).Pic) (i : Fin n) :
    restrictionToChains q n a ha c i =
      schemePicardPullbackHom (chainToOpen q n a ha i)
        (restrictionPi (chainOpenU q n a ha) c ⟨i⟩) := by
  rw [restrictionToChains_apply, restrictionPi_apply, restrictToTower, ← MonoidHom.comp_apply,
    ← schemePicardPullbackHom_comp, chainToOpen_ι]

/-- **Restriction to the chains is bijective**: the clopen decomposition of the locus. -/
theorem restrictionToChains_bijective : Function.Bijective (restrictionToChains q n a ha) := by
  constructor
  · intro c c' h
    apply (picardEquiv (chainOpenU q n a ha) (chainOpenU_disjoint q n a ha)
      (chainOpenU_iSup q n a ha)).injective
    funext i
    rw [picardEquiv_apply, picardEquiv_apply]
    have hi := congrFun h i.down
    rw [restrictionToChains_apply_eq, restrictionToChains_apply_eq, restrictionPi_apply,
      restrictionPi_apply] at hi
    exact (picardEquivOfIso (chainToOpen q n a ha i.down)).injective
      (by rw [picardEquivOfIso_apply, picardEquivOfIso_apply]; exact hi)
  · intro f
    obtain ⟨c, hc⟩ := (picardEquiv (chainOpenU q n a ha) (chainOpenU_disjoint q n a ha)
      (chainOpenU_iSup q n a ha)).surjective
      (fun i => (picardEquivOfIso (chainToOpen q n a ha i.down)).symm (f i.down))
    refine ⟨c, ?_⟩
    funext i
    rw [restrictionToChains_apply_eq, restrictionPi_apply]
    have hi : schemePicardPullbackHom (chainOpenU q n a ha ⟨i⟩).ι c =
        (picardEquivOfIso (chainToOpen q n a ha i)).symm (f i) := by
      have h := congrFun hc ⟨i⟩
      rwa [picardEquiv_apply] at h
    rw [hi, ← picardEquivOfIso_apply, MulEquiv.apply_symm_apply]

/-- **`Pic(exceptional locus) ≃* ∏ᵢ Pic(C_{i1} ∪ ⋯ ∪ C_{iq} ∪ P_i)`.** -/
def locusPicardEquivPi :
    (exceptionalScheme q n a).Pic ≃* (∀ i : Fin n, (towerChain q n a ha i).Pic) :=
  MulEquiv.ofBijective (restrictionToChains q n a ha) (restrictionToChains_bijective q n a ha)

theorem locusPicardEquivPi_apply (c : (exceptionalScheme q n a).Pic) (i : Fin n) :
    locusPicardEquivPi q n a ha c i = restrictToTower q n a ha i c := rfl

variable (hyp : SinglePoints q n a) (htrans : TowerTransversal q n a ha hyp)

include ha hyp htrans in
theorem exceptionalDegree_apply (c : (exceptionalScheme q n a).Pic) (p : Fin n × Fin (q + 1)) :
    exceptionalDegree q n a ha hyp htrans c p =
      towerChainPicardEquiv q n a ha hyp htrans p.1 (restrictToTower q n a ha p.1 c) p.2 := by
  simp only [exceptionalDegree, Pi.monoidHom_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply,
    MulEquiv.coe_toMonoidHom]

include ha hyp htrans in
/-- **The tower-by-tower degree of the exceptional locus is bijective.** -/
theorem exceptionalDegree_bijective : Function.Bijective (exceptionalDegree q n a ha hyp htrans) := by
  constructor
  · intro c c' h
    apply (restrictionToChains_bijective q n a ha).1
    funext i
    rw [restrictionToChains_apply, restrictionToChains_apply]
    apply (towerChainPicardEquiv q n a ha hyp htrans i).injective
    funext j
    have hij := congrFun h (i, j)
    rw [exceptionalDegree_apply, exceptionalDegree_apply] at hij
    exact hij
  · intro g
    obtain ⟨c, hc⟩ := (restrictionToChains_bijective q n a ha).2
      (fun i => (towerChainPicardEquiv q n a ha hyp htrans i).symm (fun j => g (i, j)))
    refine ⟨c, ?_⟩
    funext p
    rw [exceptionalDegree_apply]
    have hi : restrictToTower q n a ha p.1 c =
        (towerChainPicardEquiv q n a ha hyp htrans p.1).symm (fun j => g (p.1, j)) := by
      have h := congrFun hc p.1
      rwa [restrictionToChains_apply] at h
    rw [hi, MulEquiv.apply_symm_apply]

/-- **`Pic(exceptional locus of S_{p,n}) ≃* ℤ^{n(q+1)}`**, indexed by the `n(q+1)` exceptional
curves; the underlying map is the tower-by-tower degree `exceptionalDegree`. -/
def locusPicardEquiv :
    (exceptionalScheme q n a).Pic ≃* (Fin n × Fin (q + 1) → Multiplicative ℤ) :=
  MulEquiv.ofBijective (exceptionalDegree q n a ha hyp htrans)
    (exceptionalDegree_bijective q n a ha hyp htrans)

theorem locusPicardEquiv_apply (c : (exceptionalScheme q n a).Pic) (p : Fin n × Fin (q + 1)) :
    locusPicardEquiv q n a ha hyp htrans c p = exceptionalDegree q n a ha hyp htrans c p := rfl

include ha hyp htrans in
/-- A class of the exceptional locus of degree zero on every exceptional curve is trivial. -/
theorem locus_eq_one_of_degree_zero (c : (exceptionalScheme q n a).Pic)
    (hc : exceptionalDegree q n a ha hyp htrans c = 1) : c = 1 :=
  (exceptionalDegree_bijective q n a ha hyp htrans).1 (hc.trans (map_one _).symm)

include ha hyp htrans in
/-- A class of the exceptional locus with even degree on every exceptional curve is a square. -/
theorem locus_exists_sq_of_even (c : (exceptionalScheme q n a).Pic)
    (hc : ∀ p, Even (Multiplicative.toAdd (exceptionalDegree q n a ha hyp htrans c p))) :
    ∃ N : (exceptionalScheme q n a).Pic, c = N ^ 2 := by
  refine ⟨(locusPicardEquiv q n a ha hyp htrans).symm
    (fun p => Multiplicative.ofAdd (hc p).choose), ?_⟩
  apply (locusPicardEquiv q n a ha hyp htrans).injective
  rw [map_pow, MulEquiv.apply_symm_apply]
  funext p
  rw [Pi.pow_apply, ← ofAdd_nsmul, two_nsmul, ← (hc p).choose_spec, ofAdd_toAdd]
  rfl

include ha hyp htrans in
/-- **The half-class clause on the whole exceptional locus**: a class of `S_{p,n}` whose double
restricts trivially to the exceptional locus restricts trivially. -/
theorem locus_halfClass_trivial (M : (multiSurface (q + 1) n a).Pic)
    (h : schemePicardPullbackHom (exceptionalInclusion q n a) (M ^ 2) = 1) :
    schemePicardPullbackHom (exceptionalInclusion q n a) M = 1 := by
  have h2 : (schemePicardPullbackHom (exceptionalInclusion q n a) M) ^ 2 = 1 := by
    rw [← map_pow]
    exact h
  have h3 : exceptionalDegree q n a ha hyp htrans
      (schemePicardPullbackHom (exceptionalInclusion q n a) M) = 1 := by
    have h4 := congrArg (exceptionalDegree q n a ha hyp htrans) h2
    rw [map_pow, map_one] at h4
    funext p
    have hp := congrFun h4 p
    simp only [Pi.pow_apply, Pi.one_apply] at hp
    have h' : (2 : ℕ) • Multiplicative.toAdd (exceptionalDegree q n a ha hyp htrans
        (schemePicardPullbackHom (exceptionalInclusion q n a) M) p) = 0 := by
      rw [← toAdd_pow, hp, toAdd_one]
    rcases smul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 two_ne_zero
    · exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
  exact locus_eq_one_of_degree_zero q n a ha hyp htrans _ h3

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (q₀ n₀ : ℕ) (a₀ : Fin n₀ → k₀)
    (ha₀ : Function.Injective a₀) (hyp : SinglePoints q₀ n₀ a₀)
    (htrans : TowerTransversal q₀ n₀ a₀ ha₀ hyp) :
    (exceptionalScheme q₀ n₀ a₀).Pic ≃* (Fin n₀ × Fin (q₀ + 1) → Multiplicative ℤ) :=
  locusPicardEquiv q₀ n₀ a₀ ha₀ hyp htrans

end KltDP.Examples.FrobeniusMultiCentreLocusPicard
