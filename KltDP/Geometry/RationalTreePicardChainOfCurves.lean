import KltDP.Examples.FrobeniusExceptionalChainPicard

/-!
# A chain of projective lines in a scheme, and its Picard group

BRIEF22, task 1 (generic part). Given closed immersions `c i : P¹ ⟶ S` (`i : Fin (m + 1)`) into a
Noetherian, locally Noetherian scheme `S` whose supports form a chain — consecutive supports meet
in exactly one point, non-consecutive supports are disjoint (`ChainData`) — the union
`CurveChain.scheme S m c` is the reduced closed subscheme of `S` on the union of the supports
(glued vanishing ideal), the curves lift to closed immersions `curve i : P¹ ⟶ scheme` covering it
with pairwise incomparable images, the irreducible components are enumerated by `Fin (m + 1)`
(`component`), they form a chain (`isChain`, task 19's `IsChain`), the incidence graph is a tree,
the dimension is at most one, and — given the transversality of the crossings at the `m` chain
points in the stalk form of BRIEF18 (`Transversal`) — the union is a transversal configuration in
`S` (`transversalConfiguration`). For `k` algebraically closed and `S` locally of finite type over
`k`, **`Pic(scheme) ≃* ℤ^{m+1}`** (`picardEquiv`), the multidegree map is bijective
(`rationalTreePicard`) and a line bundle of exponent zero on every curve is trivial
(`trivial_of_degree_zero`). This is the `Fin (m + 1)`-indexed form of the construction of
witness (b) (task 21, `m = 1`) and of the exceptional chain of a tower (task 19); it is applied to
the exceptional chains of the multi-centre surface `S_{p,n}` in `FrobeniusMultiCentreChainPicard`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace CategoryTheory.Limits

universe u

namespace KltDP.Geometry.CurveChain

open KltDP.Geometry KltDP.Geometry.RationalTreePicard

variable {k : Type u} [Field k] (S : Scheme.{u}) (m : ℕ)
  (c : Fin (m + 1) → (projectiveSpace k 1 ⟶ S)) [∀ i, IsClosedImmersion (c i)]

local instance projectiveLine_isIntegral' : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-! ## The supports and the chain hypotheses -/

/-- The support of the `i`-th curve. -/
def support (i : Fin (m + 1)) : Set S := Set.range (c i).base

/-- The chain hypotheses: consecutive supports meet in exactly one point, non-consecutive
supports are disjoint. -/
structure ChainData : Prop where
  subsingleton : ∀ j : Fin m, (support S m c j.castSucc ∩ support S m c j.succ).Subsingleton
  nonempty : ∀ j : Fin m, (support S m c j.castSucc ∩ support S m c j.succ).Nonempty
  disjoint : ∀ i j : Fin (m + 1), i.val + 1 < j.val → Disjoint (support S m c i) (support S m c j)

theorem support_not_subsingleton (i : Fin (m + 1)) : ¬ (support S m c i).Subsingleton := by
  haveI : Nontrivial (projectiveSpace k 1) :=
    KltDP.Examples.FrobeniusExceptionalChainPicard.projectiveLine_nontrivial (k := k)
  intro hs
  obtain ⟨a, b, hab⟩ := exists_pair_ne (projectiveSpace k 1)
  have ha : (c i).base a ∈ support S m c i := ⟨a, rfl⟩
  have hb : (c i).base b ∈ support S m c i := ⟨b, rfl⟩
  exact hab ((c i).isClosedEmbedding.injective (hs ha hb))

/-! ## The union as a reduced closed subscheme -/

/-- The union of the supports. -/
def locus : Set S := ⋃ i : Fin (m + 1), support S m c i

theorem locus_isClosed : IsClosed (locus S m c) :=
  isClosed_iUnion_of_finite fun i => (c i).isClosedEmbedding.isClosed_range

omit [∀ i, IsClosedImmersion (c i)] in
theorem support_subset_locus (i : Fin (m + 1)) : support S m c i ⊆ locus S m c :=
  Set.subset_iUnion (fun i : Fin (m + 1) => support S m c i) i

/-- The vanishing ideal sheaf of the union. -/
def ideal : S.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨locus S m c, locus_isClosed S m c⟩

/-- The union of the curves as a reduced closed subscheme of `S`. -/
def scheme : Scheme.{u} := (ideal S m c).glueData.glued

/-- Its inclusion into `S`. -/
def inclusion : scheme S m c ⟶ S := (ideal S m c).gluedTo

instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion S m c) :=
  (ideal S m c).gluedTo_isClosedImmersion

instance scheme_isReduced : AlgebraicGeometry.IsReduced (scheme S m c) :=
  (ideal S m c).glued_isReduced
    (Scheme.IdealSheafData.vanishingIdeal_support (I := ideal S m c)).symm

theorem range_inclusion : Set.range (inclusion S m c).base = locus S m c :=
  (ideal S m c).range_gluedTo

theorem inclusion_injective : Function.Injective (inclusion S m c).base :=
  (inclusion S m c).isClosedEmbedding.injective

theorem support_subset_range (i : Fin (m + 1)) :
    support S m c i ⊆ Set.range (inclusion S m c).base := by
  rw [range_inclusion]
  exact support_subset_locus S m c i

theorem ideal_le_ker (i : Fin (m + 1)) : ideal S m c ≤ (c i).ker := by
  refine le_trans ?_ (vanishingIdeal_le_ker (c i)
    ⟨support S m c i, (c i).isClosedEmbedding.isClosed_range⟩ rfl)
  exact Scheme.IdealSheafData.vanishingIdeal_antimono (support_subset_locus S m c i)

/-- The curves as closed immersions of `P¹` into the union (indexed in universe `u`). -/
def curve (i : ULift.{u} (Fin (m + 1))) : projectiveSpace k 1 ⟶ scheme S m c :=
  liftGluedTo (ideal S m c) (c i.down) (ideal_le_ker S m c i.down)

theorem curve_comp (i : ULift.{u} (Fin (m + 1))) :
    curve S m c i ≫ inclusion S m c = c i.down :=
  liftGluedTo_gluedTo _ _ _

instance curve_isClosedImmersion (i : ULift.{u} (Fin (m + 1))) :
    IsClosedImmersion (curve S m c i) := by
  haveI : IsClosedImmersion (curve S m c i ≫ inclusion S m c) := by
    rw [curve_comp]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (inclusion S m c)

theorem range_curve_eq (i : ULift.{u} (Fin (m + 1))) :
    Set.range (curve S m c i).base = (inclusion S m c).base ⁻¹' support S m c i.down := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    show (inclusion S m c).base ((curve S m c i).base p) ∈ support S m c i.down
    rw [← Scheme.comp_base_apply, curve_comp]
    exact ⟨p, rfl⟩
  · intro hx
    obtain ⟨p, hp⟩ := (show (inclusion S m c).base x ∈ support S m c i.down from hx)
    refine ⟨p, inclusion_injective S m c ?_⟩
    rw [← Scheme.comp_base_apply, curve_comp]
    exact hp

theorem curve_cover :
    ⋃ i : ULift.{u} (Fin (m + 1)), Set.range (curve S m c i).base = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : (inclusion S m c).base x ∈ locus S m c := by
    rw [← range_inclusion]
    exact ⟨x, rfl⟩
  unfold locus at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr ⟨ULift.up i, ?_⟩
  rw [range_curve_eq]
  exact hi

theorem curve_distinct (hd : ChainData S m c) (i j : ULift.{u} (Fin (m + 1)))
    (h : Set.range (curve S m c i).base ⊆ Set.range (curve S m c j).base) : i = j := by
  have hS : support S m c i.down ⊆ support S m c j.down := by
    rw [← Set.image_preimage_eq_of_subset (support_subset_range S m c i.down),
      ← range_curve_eq S m c i]
    calc (inclusion S m c).base '' Set.range (curve S m c i).base
        ⊆ (inclusion S m c).base '' Set.range (curve S m c j).base := Set.image_mono h
      _ = support S m c j.down := by
        rw [range_curve_eq S m c j,
          Set.image_preimage_eq_of_subset (support_subset_range S m c j.down)]
  have hij := chain_not_subset (support S m c) hd.subsingleton hd.disjoint
    (support_not_subsingleton S m c) i.down j.down hS
  cases i
  cases j
  cases hij
  rfl

/-! ## The configuration -/

section Configuration

variable [NoetherianSpace S] [IsLocallyNoetherian S]

instance scheme_noetherianSpace : NoetherianSpace (scheme S m c) :=
  noetherianSpace_of_isClosedImmersion (inclusion S m c)

instance scheme_isLocallyNoetherian : IsLocallyNoetherian (scheme S m c) :=
  isLocallyNoetherian_of_isClosedImmersion (inclusion S m c)

/-- The irreducible components of the union, enumerated along the chain. -/
def component (hd : ChainData S m c) : Fin (m + 1) ≃ ↥(irreducibleComponents (scheme S m c)) :=
  Equiv.ulift.symm.trans (curveComponentEquiv (scheme S m c) (fun _ => projectiveSpace k 1)
    (curve S m c) (fun _ => projectiveLine_isIntegral) (curve_cover S m c)
    (curve_distinct S m c hd))

omit [NoetherianSpace S] [IsLocallyNoetherian S] in
theorem component_val (hd : ChainData S m c) (i : Fin (m + 1)) :
    (component S m c hd i).1 = Set.range (curve S m c (ULift.up i)).base :=
  rfl

omit [NoetherianSpace S] [IsLocallyNoetherian S] in
/-- The components form a chain. -/
theorem isChain (hd : ChainData S m c) : IsChain (scheme S m c) (component S m c hd) where
  subsingleton j := by
    rw [component_val, component_val, range_curve_eq, range_curve_eq, ← Set.preimage_inter]
    exact (hd.subsingleton j).preimage (inclusion_injective S m c)
  nonempty j := by
    rw [component_val, component_val, range_curve_eq, range_curve_eq, ← Set.preimage_inter]
    exact (hd.nonempty j).preimage'
      (Set.inter_subset_left.trans (support_subset_range S m c j.castSucc))
  disjoint i j hij := by
    rw [component_val, component_val, range_curve_eq, range_curve_eq]
    exact (hd.disjoint i j hij).preimage (inclusion S m c).base

omit [NoetherianSpace S] [IsLocallyNoetherian S] in
theorem isTree (hd : ChainData S m c) :
    (componentPointIncidenceGraph (scheme S m c)).IsTree :=
  isTree_of_chain (scheme S m c) (component S m c hd) (isChain S m c hd)

omit [NoetherianSpace S] [IsLocallyNoetherian S] in
theorem dim : topologicalKrullDim (scheme S m c) ≤ 1 :=
  topologicalKrullDim_le_one_of_curves (scheme S m c) (fun _ => projectiveSpace k 1)
    (curve S m c) (curve_cover S m c)
    (fun _ => KltDP.Examples.FrobeniusExceptionalChainPicard.projectiveLine_dim_le_one)

/-- **Transversality of the crossings** (BRIEF18's stalk form): at every common point of two
consecutive components, `O_{S, x}` is regular of dimension two with local equations of the two
curves generating its maximal ideal and `O_{scheme, x} = O_{S, x} ⧸ (f g)`. -/
def Transversal (hd : ChainData S m c) : Prop :=
  ∀ (j : Fin m) (x : scheme S m c), x ∈ (component S m c hd j.castSucc).1 →
    x ∈ (component S m c hd j.succ).1 →
    TransversalCrossing (inclusion S m c) (component S m c hd j.castSucc)
      (component S m c hd j.succ) x

omit [IsLocallyNoetherian S] in
/-- Given the crossings, the union is a transversal configuration in `S`. -/
theorem transversalConfiguration (hd : ChainData S m c) (htrans : Transversal S m c hd) :
    TransversalConfiguration (inclusion S m c) where
  no_triple C D E x hC hD hE := by
    set e := component S m c hd with he
    have key : ∀ a b : Fin (m + 1), a.val + 1 < b.val → x ∈ (e a).1 → x ∈ (e b).1 → False :=
      fun a b hab ha hb => Set.disjoint_left.mp ((isChain S m c hd).disjoint a b hab) ha hb
    have hC' : x ∈ (e (e.symm C)).1 := by rw [Equiv.apply_symm_apply]; exact hC
    have hD' : x ∈ (e (e.symm D)).1 := by rw [Equiv.apply_symm_apply]; exact hD
    have hE' : x ∈ (e (e.symm E)).1 := by rw [Equiv.apply_symm_apply]; exact hE
    by_contra hcon
    push_neg at hcon
    obtain ⟨hCD, hCE, hDE⟩ := hcon
    have hab : (e.symm C).val ≠ (e.symm D).val := fun h => hCD (e.symm.injective (Fin.ext h))
    have hac : (e.symm C).val ≠ (e.symm E).val := fun h => hCE (e.symm.injective (Fin.ext h))
    have hbc : (e.symm D).val ≠ (e.symm E).val := fun h => hDE (e.symm.injective (Fin.ext h))
    rcases (show (e.symm C).val + 1 < (e.symm D).val ∨ (e.symm D).val + 1 < (e.symm C).val ∨
        (e.symm C).val + 1 < (e.symm E).val ∨ (e.symm E).val + 1 < (e.symm C).val ∨
        (e.symm D).val + 1 < (e.symm E).val ∨ (e.symm E).val + 1 < (e.symm D).val by omega)
      with h | h | h | h | h | h
    · exact key _ _ h hC' hD'
    · exact key _ _ h hD' hC'
    · exact key _ _ h hC' hE'
    · exact key _ _ h hE' hC'
    · exact key _ _ h hD' hE'
    · exact key _ _ h hE' hD'
  crossing C D hCD x hC hD := by
    set e := component S m c hd with he
    have key : ∀ a b : Fin (m + 1), a.val + 1 < b.val → x ∈ (e a).1 → x ∈ (e b).1 → False :=
      fun a b hab ha hb => Set.disjoint_left.mp ((isChain S m c hd).disjoint a b hab) ha hb
    have hC' : x ∈ (e (e.symm C)).1 := by rw [Equiv.apply_symm_apply]; exact hC
    have hD' : x ∈ (e (e.symm D)).1 := by rw [Equiv.apply_symm_apply]; exact hD
    have hab : (e.symm C).val ≠ (e.symm D).val := fun h => hCD (e.symm.injective (Fin.ext h))
    have hCe : C = e (e.symm C) := (e.apply_symm_apply C).symm
    have hDe : D = e (e.symm D) := (e.apply_symm_apply D).symm
    by_cases h1 : (e.symm C).val + 1 < (e.symm D).val
    · exact (key _ _ h1 hC' hD').elim
    by_cases h2 : (e.symm D).val + 1 < (e.symm C).val
    · exact (key _ _ h2 hD' hC').elim
    rcases (show (e.symm D).val = (e.symm C).val + 1 ∨ (e.symm C).val = (e.symm D).val + 1 by omega)
      with h | h
    · have hj : (e.symm C).val < m := by have := (e.symm D).isLt; omega
      have ha : e.symm C = Fin.castSucc ⟨(e.symm C).val, hj⟩ := Fin.ext rfl
      have hb : e.symm D = Fin.succ ⟨(e.symm C).val, hj⟩ := Fin.ext h
      rw [hCe, hDe, ha, hb]
      exact htrans ⟨(e.symm C).val, hj⟩ x (by rw [← ha]; exact hC') (by rw [← hb]; exact hD')
    · have hj : (e.symm D).val < m := by have := (e.symm C).isLt; omega
      have ha : e.symm D = Fin.castSucc ⟨(e.symm D).val, hj⟩ := Fin.ext rfl
      have hb : e.symm C = Fin.succ ⟨(e.symm D).val, hj⟩ := Fin.ext h
      rw [hCe, hDe, ha, hb]
      exact (htrans ⟨(e.symm D).val, hj⟩ x (by rw [← ha]; exact hD') (by rw [← hb]; exact hC')).symm

end Configuration

/-! ## The Picard group -/

section Picard

variable [IsAlgClosed k] [NoetherianSpace S] [IsLocallyNoetherian S]
  (π : S ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType π]
  (hd : ChainData S m c) (htrans : Transversal S m c hd)

include π htrans in
/-- **The multidegree map of a chain of projective lines is bijective.** -/
theorem rationalTreePicard :
    Function.Bijective (multidegreeHom k (scheme S m c)
      (lineIdentification (scheme S m c) (curve S m c) (curve_cover S m c)
        (curve_distinct S m c hd))) :=
  rationalTreePicard_of_configuration (scheme S m c) (inclusion S m c) π
    (transversalConfiguration S m c hd htrans) (dim S m c) (isTree S m c hd) (curve S m c)
    (curve_cover S m c) (curve_distinct S m c hd)

/-- **`Pic(chain) ≃* ℤ^{m+1}`**, indexed along the chain. -/
def picardEquiv : (scheme S m c).Pic ≃* (Fin (m + 1) → Multiplicative ℤ) :=
  (picardEquiv_of_configuration (scheme S m c) (inclusion S m c) π
    (transversalConfiguration S m c hd htrans) (dim S m c) (isTree S m c hd) (curve S m c)
    (curve_cover S m c) (curve_distinct S m c hd)).trans
    (MulEquiv.arrowCongr Equiv.ulift (MulEquiv.refl (Multiplicative ℤ)))

include π htrans in
/-- A line bundle on the chain with exponent zero on every curve is trivial. -/
theorem trivial_of_degree_zero (L : InvertibleSheaf (scheme S m c))
    (hL : ∀ i : ULift.{u} (Fin (m + 1)), componentExponent k (scheme S m c)
      {lineComponent (scheme S m c) (curve S m c) (curve_cover S m c) (curve_distinct S m c hd) i}
      (lineIdentification (scheme S m c) (curve S m c) (curve_cover S m c) (curve_distinct S m c hd)
        (lineComponent (scheme S m c) (curve S m c) (curve_cover S m c)
          (curve_distinct S m c hd) i)) L = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit (scheme S m c).ringCatSheaf) :=
  trivial_of_degree_zero_of_configuration (scheme S m c) (inclusion S m c) π
    (transversalConfiguration S m c hd htrans) (dim S m c) (isTree S m c hd) (curve S m c)
    (curve_cover S m c) (curve_distinct S m c hd) L hL

end Picard

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (S₀ : Scheme.{0}) [NoetherianSpace S₀]
    [IsLocallyNoetherian S₀] (m₀ : ℕ) (c₀ : Fin (m₀ + 1) → (projectiveSpace k₀ 1 ⟶ S₀))
    [∀ i, IsClosedImmersion (c₀ i)] (π₀ : S₀ ⟶ Spec (CommRingCat.of k₀)) [LocallyOfFiniteType π₀]
    (hd : ChainData S₀ m₀ c₀) (htrans : Transversal S₀ m₀ c₀ hd) :
    (scheme S₀ m₀ c₀).Pic ≃* (Fin (m₀ + 1) → Multiplicative ℤ) :=
  picardEquiv S₀ m₀ c₀ π₀ hd htrans

end KltDP.Geometry.CurveChain
