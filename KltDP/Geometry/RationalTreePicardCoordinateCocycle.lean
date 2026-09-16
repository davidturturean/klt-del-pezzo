import KltDP.Geometry.RationalTreePicardSurjectiveReduction
import KltDP.Geometry.RationalTreePicardLeafNodeGluing
import KltDP.Geometry.TransitionUnitPicardComparison
import KltDP.Geometry.RationalTreePicardComponentIntersectionFinite

/-!
# The coordinate cocycle of a component

BRIEF16, step 1. For a component `C` of the curve `X` (identified with the projective line by
`e`), we build an open cover of `X` and a unit cocycle on it whose glued line bundle
`coordinateBundle` is the candidate "coordinate" line bundle of `C` (exponent `1` on `C`, `0` on
every other component). The cover: the two standard-chart pieces of the open part of `C`
(`leafOpen X C` minus the image of the complement of a standard open), the complement `X ∖ C`,
and one open per node `q ∈ C ∩ Z_{Cᶜ}` (the complement of the other nodes and of the image of a
standard-open complement missing `q`). Every pairwise intersection of two distinct members of
the cover misses the nodes, hence splits as the disjoint union of its part inside `C` (an open
of `X` contained in `leafOpen X C`, where the closed immersion of `C` is an isomorphism on
sections) and its part outside `C`. The transition unit is the transported standard transition
`T` of `O(1)` (the accepted `monomialCocycle k 1`) on the first part and `1` on the second
(`disjointUnit`); the cocycle identities are checked on the two parts separately
(`sections_ext_of_disjoint`).

Pulling the cocycle back along the closed immersion `componentLine k C e : P¹ ⟶ X` of the
component gives exactly the refinement of the standard `O(1)` cocycle to the cover
`ψ⁻¹(coordOpens)` (`pullbackUnits_componentLine_coordUnits`), so the Picard class of the
pulled-back cocycle is the class of `O(1)` (`picardClass_pullbackUnits_coordUnits`, through the
accepted `picardClass_eq_of_refinement`).

What is NOT proved here: that the pullback of the glued line bundle is the line bundle glued from
the pulled-back cocycle (`PullbackGluedClass`, stated generically for any morphism, cover and
cocycle). Under that hypothesis the component exponent of `coordinateBundle` on `C` is `1`
(`componentExponent_coordinateBundle_self`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

open TransitionUnitGluing ProjectiveLineTransitionExtension ProjectiveLineComparison

section SectionRestriction

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The section map of a morphism commutes with restriction. -/
theorem app_res {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)) :
    f.app V (res X h s) = res Y (f.preimage_le_preimage_of_le h) (f.app U s) := by
  have h1 := ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) s
  simp only [CommRingCat.comp_apply] at h1
  exact h1

theorem app_mul (U : X.Opens) (a b : Γ(X, U)) : f.app U (a * b) = f.app U a * f.app U b :=
  (f.app U).hom.map_mul a b

theorem app_one (U : X.Opens) : f.app U (1 : Γ(X, U)) = 1 :=
  (f.app U).hom.map_one

end SectionRestriction

section DisjointSup

variable {X : Scheme.{u}} {A B : X.Opens} (hAB : A ⊓ B = ⊥)

/-- Sections over the union of two disjoint opens are pairs of sections. -/
def disjointSectionsEquiv : Γ(X, A ⊔ B) ≃+* Γ(X, A) × Γ(X, B) where
  toFun s := (res X le_sup_left s, res X le_sup_right s)
  invFun p := (X.sheaf.objSupIsoProdEqLocus A B).inv ⟨p,
    (show _ = _ from @Subsingleton.elim _ (subsingleton_sections_of_eq_bot hAB) _ _)⟩
  left_inv s := by
    have h : (X.sheaf.objSupIsoProdEqLocus A B).hom s =
        ⟨(res X le_sup_left s, res X le_sup_right s),
          (show _ = _ from @Subsingleton.elim _ (subsingleton_sections_of_eq_bot hAB) _ _)⟩ := by
      apply Subtype.ext
      exact Prod.ext (TopCat.Sheaf.objSupIsoProdEqLocus_hom_fst X.sheaf A B s)
        (TopCat.Sheaf.objSupIsoProdEqLocus_hom_snd X.sheaf A B s)
    dsimp only
    rw [← h]
    have h2 := ConcreteCategory.congr_hom (X.sheaf.objSupIsoProdEqLocus A B).hom_inv_id s
    simpa only [CommRingCat.comp_apply, CommRingCat.id_apply] using h2
  right_inv p := Prod.ext (TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf A B _)
    (TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf A B _)
  map_mul' s t := Prod.ext (map_mul _ s t) (map_mul _ s t)
  map_add' s t := Prod.ext (map_add _ s t) (map_add _ s t)

theorem disjointSectionsEquiv_symm_fst (p : Γ(X, A) × Γ(X, B)) :
    res X le_sup_left ((disjointSectionsEquiv hAB).symm p) = p.1 :=
  TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf A B _

theorem disjointSectionsEquiv_symm_snd (p : Γ(X, A) × Γ(X, B)) :
    res X le_sup_right ((disjointSectionsEquiv hAB).symm p) = p.2 :=
  TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf A B _

/-- A unit on `A` extended by a unit on the disjoint open `B`. -/
def disjointUnit (u : Γ(X, A)ˣ) (v : Γ(X, B)ˣ) : Γ(X, A ⊔ B)ˣ :=
  Units.map (disjointSectionsEquiv hAB).symm.toRingHom.toMonoidHom
    (MulEquiv.prodUnits.symm (u, v))

theorem coe_disjointUnit (u : Γ(X, A)ˣ) (v : Γ(X, B)ˣ) :
    (disjointUnit hAB u v : Γ(X, A ⊔ B)) =
      (disjointSectionsEquiv hAB).symm ((u : Γ(X, A)), (v : Γ(X, B))) := rfl

theorem res_disjointUnit_left (u : Γ(X, A)ˣ) (v : Γ(X, B)ˣ) :
    res X le_sup_left (disjointUnit hAB u v : Γ(X, A ⊔ B)) = u := by
  rw [coe_disjointUnit]
  exact disjointSectionsEquiv_symm_fst hAB _

theorem res_disjointUnit_right (u : Γ(X, A)ˣ) (v : Γ(X, B)ˣ) :
    res X le_sup_right (disjointUnit hAB u v : Γ(X, A ⊔ B)) = v := by
  rw [coe_disjointUnit]
  exact disjointSectionsEquiv_symm_snd hAB _

omit hAB in
/-- Two sections over an open covered by two opens agree if they agree on both. -/
theorem sections_ext_of_disjoint {W : X.Opens} (hW : W ≤ A ⊔ B) {s t : Γ(X, W)}
    (h₁ : res X (inf_le_left : W ⊓ A ≤ W) s = res X inf_le_left t)
    (h₂ : res X (inf_le_left : W ⊓ B ≤ W) s = res X inf_le_left t) : s = t :=
  X.sheaf.eq_of_locally_eq₂ (homOfLE (inf_le_left : W ⊓ A ≤ W))
    (homOfLE (inf_le_left : W ⊓ B ≤ W))
    ((le_inf le_rfl hW).trans (inf_sup_left W A B).le) s t h₁ h₂

end DisjointSup

section PullbackUnits

variable {Y X : Scheme.{u}} (f : Y ⟶ X) {ι : Type u} (U : ι → X.Opens)
  (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)

theorem preimage_inf_le (i j : ι) : f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j ≤ f ⁻¹ᵁ (U i ⊓ U j) :=
  fun _ hx => ⟨hx.1, hx.2⟩

/-- The pullback of a unit cocycle along a morphism. -/
def pullbackUnits (i j : ι) : Γ(Y, f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j)ˣ :=
  Units.map (res Y (preimage_inf_le f U i j)).toMonoidHom
    (Units.map (f.app (U i ⊓ U j)).hom.toMonoidHom (g i j))

theorem pullbackUnits_val (i j : ι) :
    (pullbackUnits f U g i j : Γ(Y, f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j)) =
      res Y (preimage_inf_le f U i j) (f.app (U i ⊓ U j) (g i j)) := rfl

theorem pullbackUnits_isCocycle (hg : IsCocycle X U g) :
    IsCocycle Y (fun i => f ⁻¹ᵁ U i) (pullbackUnits f U g) where
  unit_self i := by
    rw [pullbackUnits_val]
    have h : ((g i i : Γ(X, U i ⊓ U i))) = 1 := hg.unit_self i
    rw [h, app_one, map_one]
  mul_res i j l := by
    rw [pullbackUnits_val, pullbackUnits_val, pullbackUnits_val]
    simp only [res_res]
    have hT : f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j ⊓ f ⁻¹ᵁ U l ≤ f ⁻¹ᵁ (U i ⊓ U j ⊓ U l) :=
      fun _ hx => ⟨⟨hx.1.1, hx.1.2⟩, hx.2⟩
    have key : ∀ (a b : ι) (hab : U i ⊓ U j ⊓ U l ≤ U a ⊓ U b)
        (h : f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j ⊓ f ⁻¹ᵁ U l ≤ f ⁻¹ᵁ (U a ⊓ U b)),
        res Y h (f.app (U a ⊓ U b) (g a b)) =
          res Y hT (f.app (U i ⊓ U j ⊓ U l) (res X hab (g a b))) := by
      intro a b hab h
      rw [app_res, res_res]
    rw [key i j inf_le_left, key j l (inclCoc X U (U i) j l), key i l (inclSnd X U (U i) j l),
      ← map_mul, ← app_mul, hg.mul_res i j l]

theorem pullbackUnits_cover (hU : (⨆ i, U i) = ⊤) : (⨆ i, f ⁻¹ᵁ U i) = ⊤ :=
  f.preimage_iSup_eq_top hU

/-- The (yet unproved) compatibility of the cocycle-glued line bundle with pullback: the Picard
class of the pullback is the class of the pulled-back cocycle. -/
def PullbackGluedClass : Prop :=
  ∀ {Y X : Scheme.{u}} (f : Y ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (hg : IsCocycle X U g) (hU : (⨆ i, U i) = ⊤),
    (pullbackInvertibleSheaf f (invertibleSheaf X U g hg hU)).toPic =
      picardClass Y (fun i => f ⁻¹ᵁ U i) (pullbackUnits f U g) (pullbackUnits_isCocycle f U g hg)
        (pullbackUnits_cover f U hU)

theorem picardClass_congr {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {g g' : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ} (h : g = g') (hg : IsCocycle X U g)
    (hU : (⨆ i, U i) = ⊤) :
    picardClass X U g hg hU = picardClass X U g' (h ▸ hg) hU := by
  subst h
  rfl

end PullbackUnits

section CoordinateCover

variable (k : Type u) [Field k] {X : Scheme.{u}} [NoetherianSpace X]
  (C : ↥(irreducibleComponents X)) (e : componentUnionScheme X {C} ≅ projectiveSpace k 1)

/-- The closed immersion of the projective line onto the component `C`. -/
abbrev componentLine : projectiveSpace k 1 ⟶ X := e.inv ≫ componentUnionInclusion X {C}

instance componentLine_isClosedImmersion : IsClosedImmersion (componentLine k C e) :=
  inferInstance

theorem componentLine_injective : Function.Injective (componentLine k C e).base :=
  (componentLine k C e).isClosedEmbedding.isEmbedding.injective

theorem range_componentLine : Set.range (componentLine k C e).base = C.1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩
    have h : (componentUnionInclusion X {C}).base (e.inv.base y) ∈
        Set.range (componentUnionInclusion X {C}).base := ⟨_, rfl⟩
    rw [range_componentUnionInclusion, coe_componentClosedUnion_singleton] at h
    exact h
  · intro x hx
    have hx' : x ∈ Set.range (componentUnionInclusion X {C}).base := by
      rw [range_componentUnionInclusion, coe_componentClosedUnion_singleton]
      exact hx
    obtain ⟨y, rfl⟩ := hx'
    refine ⟨e.hom.base y, ?_⟩
    change (e.inv ≫ componentUnionInclusion X {C}).base (e.hom.base y) = _
    rw [Scheme.comp_base_apply, ← Scheme.comp_base_apply e.hom e.inv, e.hom_inv_id,
      Scheme.id.base]
    rfl

/-- The intersection points of `C` with the other components. -/
def nodesOn : Set X := C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X)

theorem nodesOn_subset_componentIntersectionPoints :
    nodesOn C ⊆ componentIntersectionPoints X := by
  rintro x ⟨hxC, hx⟩
  obtain ⟨D, hD, hxD⟩ := (mem_componentClosedUnion X ({C}ᶜ) x).mp hx
  exact ⟨C, D, fun h => hD (Set.mem_singleton_iff.mpr h.symm), hxC, hxD⟩

variable (hdim : topologicalKrullDim X ≤ 1)

include hdim in
theorem nodesOn_finite : (nodesOn C).Finite :=
  (componentIntersectionPoints_finite X hdim).subset (nodesOn_subset_componentIntersectionPoints C)

include hdim in
theorem isClosed_nodesOn_diff (q : X) : IsClosed (nodesOn C \ {q}) := by
  rw [← Set.biUnion_of_singleton (nodesOn C \ {q})]
  exact ((nodesOn_finite C hdim).diff).isClosed_biUnion fun x hx =>
    isClosed_singleton_of_mem_componentIntersectionPoints X hdim
      (nodesOn_subset_componentIntersectionPoints C hx.1)

/-- The image in `X` of the complement of a standard open of the projective line. -/
def lineImage (i : ULift.{u} (Fin 2)) : Set X :=
  (componentLine k C e).base '' ((standardOpens k i : Set (projectiveSpace k 1))ᶜ)

theorem isClosed_lineImage (i : ULift.{u} (Fin 2)) : IsClosed (lineImage k C e i) :=
  (componentLine k C e).isClosedEmbedding.isClosedMap _ (standardOpens k i).isOpen.isClosed_compl

theorem lineImage_subset (i : ULift.{u} (Fin 2)) : lineImage k C e i ⊆ C.1 := by
  rw [← range_componentLine k C e]
  exact Set.image_subset_range _ _

theorem mem_lineImage_iff (i : ULift.{u} (Fin 2)) (y : projectiveSpace k 1) :
    (componentLine k C e).base y ∈ lineImage k C e i ↔ y ∉ standardOpens k i := by
  constructor
  · rintro ⟨y', hy', hyy'⟩
    rw [componentLine_injective k C e hyy'] at hy'
    exact hy'
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem lineImage_inter : lineImage k C e ⟨0⟩ ∩ lineImage k C e ⟨1⟩ = ∅ := by
  unfold lineImage
  rw [← Set.image_inter (componentLine_injective k C e), ← Set.compl_union]
  have h : (standardOpens k ⟨0⟩ : Set (projectiveSpace k 1)) ∪ standardOpens k ⟨1⟩ =
      Set.univ := by
    rw [← Opens.coe_sup]
    change ((chartOpen k 0 ⊔ chartOpen k 1 : (projectiveSpace k 1).Opens) :
      Set (projectiveSpace k 1)) = Set.univ
    rw [chartOpen_sup, Opens.coe_top]
  rw [h, Set.compl_univ, Set.image_empty]

open scoped Classical in
/-- A standard chart index whose image complement misses the given point of `C`. -/
def nodeChart (q : X) : ULift.{u} (Fin 2) :=
  if q ∈ lineImage k C e ⟨0⟩ then ⟨1⟩ else ⟨0⟩

theorem not_mem_lineImage_nodeChart (q : X) : q ∉ lineImage k C e (nodeChart k C e q) := by
  classical
  unfold nodeChart
  split_ifs with h
  · intro h'
    have hmem : q ∈ lineImage k C e ⟨0⟩ ∩ lineImage k C e ⟨1⟩ := ⟨h, h'⟩
    rw [lineImage_inter] at hmem
    exact hmem
  · exact h

/-- The index set of the coordinate cover: the two standard chart pieces of the open part of
`C`, the complement of `C`, and one chart per node. -/
abbrev CoordIndex : Type u := ULift.{u} (Fin 2) ⊕ Option ↥(nodesOn C)

/-- The coordinate cover of `X` attached to the component `C`. -/
def coordOpens : CoordIndex C → X.Opens
  | Sum.inl i => leafOpen X C ⊓ ⟨(lineImage k C e i)ᶜ, (isClosed_lineImage k C e i).isOpen_compl⟩
  | Sum.inr none => complementOpen X C
  | Sum.inr (some q) => ⟨((nodesOn C \ {q.1}) ∪ lineImage k C e (nodeChart k C e q.1))ᶜ,
      ((isClosed_nodesOn_diff C hdim q.1).union (isClosed_lineImage k C e _)).isOpen_compl⟩

/-- The standard chart subordinate to each member of the coordinate cover. -/
def coordChart : CoordIndex C → ULift.{u} (Fin 2)
  | Sum.inl i => i
  | Sum.inr none => ⟨0⟩
  | Sum.inr (some q) => nodeChart k C e q.1

theorem mem_coordOpens_inl (i : ULift.{u} (Fin 2)) (x : X) :
    x ∈ coordOpens k C e hdim (Sum.inl i) ↔ x ∈ leafOpen X C ∧ x ∉ lineImage k C e i :=
  Iff.rfl

theorem mem_coordOpens_none (x : X) :
    x ∈ coordOpens k C e hdim (Sum.inr none) ↔ x ∉ componentClosedUnion X {C} :=
  Iff.rfl

theorem mem_coordOpens_some (q : ↥(nodesOn C)) (x : X) :
    x ∈ coordOpens k C e hdim (Sum.inr (some q)) ↔
      x ∉ nodesOn C \ {q.1} ∧ x ∉ lineImage k C e (nodeChart k C e q.1) := by
  change x ∈ ((nodesOn C \ {q.1}) ∪ lineImage k C e (nodeChart k C e q.1))ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_union, not_or]

theorem coordOpens_cover (x : X) : ∃ a, x ∈ coordOpens k C e hdim a := by
  by_cases hxC : x ∈ C.1
  · by_cases hxN : x ∈ (componentClosedUnion X ({C}ᶜ) : Set X)
    · refine ⟨Sum.inr (some ⟨x, hxC, hxN⟩), (mem_coordOpens_some k C e hdim _ x).mpr ⟨?_, ?_⟩⟩
      · exact fun h => h.2 rfl
      · exact not_mem_lineImage_nodeChart k C e x
    · have hxC' := hxC
      rw [← range_componentLine k C e] at hxC'
      obtain ⟨y, rfl⟩ := hxC'
      have hy : y ∈ ((chartOpen k 0 ⊔ chartOpen k 1 : (projectiveSpace k 1).Opens) :
          Set (projectiveSpace k 1)) := by
        rw [chartOpen_sup]
        trivial
      rw [Opens.coe_sup] at hy
      rcases hy with hy0 | hy1
      · exact ⟨Sum.inl ⟨0⟩, hxN, fun h => (mem_lineImage_iff k C e ⟨0⟩ y).mp h hy0⟩
      · exact ⟨Sum.inl ⟨1⟩, hxN, fun h => (mem_lineImage_iff k C e ⟨1⟩ y).mp h hy1⟩
  · refine ⟨Sum.inr none, fun h => hxC ?_⟩
    change x ∈ (componentClosedUnion X {C} : Set X) at h
    rw [coe_componentClosedUnion_singleton] at h
    exact h

theorem coordOpens_iSup : (⨆ a, coordOpens k C e hdim a) = ⊤ :=
  top_unique fun x _ => Opens.mem_iSup.mpr (coordOpens_cover k C e hdim x)

theorem preimage_coordOpens_le (a : CoordIndex C) :
    componentLine k C e ⁻¹ᵁ coordOpens k C e hdim a ≤ standardOpens k (coordChart k C e a) := by
  intro y hy
  by_contra hyS
  have hmem : (componentLine k C e).base y ∈ lineImage k C e (coordChart k C e a) :=
    (mem_lineImage_iff k C e _ y).mpr hyS
  have hyC : (componentLine k C e).base y ∈ C.1 := by
    rw [← range_componentLine k C e]
    exact ⟨y, rfl⟩
  rcases a with i | (_ | q)
  · exact hy.2 hmem
  · apply hy
    rw [coe_componentClosedUnion_singleton]
    exact hyC
  · exact hy (Or.inr hmem)

theorem not_mem_nodesOn_of_mem_coordOpens {a b : CoordIndex C} (hab : a ≠ b) {x : X}
    (hxa : x ∈ coordOpens k C e hdim a) (hxb : x ∈ coordOpens k C e hdim b) : x ∉ nodesOn C := by
  intro hxN
  rcases a with i | (_ | q)
  · exact hxa.1 hxN.2
  · apply hxa
    rw [coe_componentClosedUnion_singleton]
    exact hxN.1
  · rcases b with j | (_ | q')
    · exact hxb.1 hxN.2
    · apply hxb
      rw [coe_componentClosedUnion_singleton]
      exact hxN.1
    · have hq : x = q.1 := by
        by_contra hne
        exact ((mem_coordOpens_some k C e hdim q x).mp hxa).1 ⟨hxN, hne⟩
      have hq' : x = q'.1 := by
        by_contra hne
        exact ((mem_coordOpens_some k C e hdim q' x).mp hxb).1 ⟨hxN, hne⟩
      exact hab (by rw [Subtype.ext (hq.symm.trans hq')])

theorem coordOpens_inter_le {a b : CoordIndex C} (hab : a ≠ b) :
    coordOpens k C e hdim a ⊓ coordOpens k C e hdim b ≤ leafOpen X C ⊔ complementOpen X C := by
  intro x hx
  change x ∈ ((leafOpen X C ⊔ complementOpen X C : X.Opens) : Set X)
  rw [Opens.coe_sup, Set.mem_union]
  by_cases hxC : x ∈ C.1
  · left
    intro hxN
    exact not_mem_nodesOn_of_mem_coordOpens k C e hdim hab hx.1 hx.2 ⟨hxC, hxN⟩
  · right
    intro h
    apply hxC
    change x ∈ (componentClosedUnion X {C} : Set X) at h
    rw [coe_componentClosedUnion_singleton] at h
    exact h

/-- The overlap of two members of the coordinate cover. -/
abbrev coordOverlap (a b : CoordIndex C) : X.Opens :=
  coordOpens k C e hdim a ⊓ coordOpens k C e hdim b

/-- The part of an overlap inside the open part of `C`. -/
abbrev leafPiece (a b : CoordIndex C) : X.Opens := coordOverlap k C e hdim a b ⊓ leafOpen X C

/-- The part of an overlap outside `C`. -/
abbrev complPiece (a b : CoordIndex C) : X.Opens :=
  coordOverlap k C e hdim a b ⊓ complementOpen X C

theorem leafPiece_inf_complPiece (a b : CoordIndex C) :
    leafPiece k C e hdim a b ⊓ complPiece k C e hdim a b = ⊥ :=
  le_bot_iff.mp fun _ hx => (leafOpen_inf_complementOpen X C).le ⟨hx.1.2, hx.2.2⟩

theorem coordOverlap_le_sup {a b : CoordIndex C} (hab : a ≠ b) :
    coordOverlap k C e hdim a b ≤ leafPiece k C e hdim a b ⊔ complPiece k C e hdim a b :=
  (le_inf le_rfl (coordOpens_inter_le k C e hdim hab)).trans (inf_sup_left _ _ _).le

theorem preimage_leafPiece_le (a b : CoordIndex C) :
    componentLine k C e ⁻¹ᵁ leafPiece k C e hdim a b ≤
      standardOpens k (coordChart k C e a) ⊓ standardOpens k (coordChart k C e b) :=
  le_inf
    (((componentLine k C e).preimage_le_preimage_of_le
      (inf_le_left.trans inf_le_left)).trans (preimage_coordOpens_le k C e hdim a))
    (((componentLine k C e).preimage_le_preimage_of_le
      (inf_le_left.trans inf_le_right)).trans (preimage_coordOpens_le k C e hdim b))

/-- The standard transition of `O(1)` restricted to the preimage of an overlap piece. -/
def standardOnLeafPiece (a b : CoordIndex C) :
    Γ(projectiveSpace k 1, componentLine k C e ⁻¹ᵁ leafPiece k C e hdim a b)ˣ :=
  Units.map (res (projectiveSpace k 1) (preimage_leafPiece_le k C e hdim a b)).toMonoidHom
    (monomialCocycle k 1 (coordChart k C e a) (coordChart k C e b))

theorem preimage_coordOverlap_le_leafPiece {a b : CoordIndex C} (hab : a ≠ b) :
    componentLine k C e ⁻¹ᵁ coordOpens k C e hdim a ⊓
        componentLine k C e ⁻¹ᵁ coordOpens k C e hdim b ≤
      componentLine k C e ⁻¹ᵁ leafPiece k C e hdim a b := by
  intro y hy
  have hyC : (componentLine k C e).base y ∈ C.1 := by
    rw [← range_componentLine k C e]
    exact ⟨y, rfl⟩
  refine ⟨⟨hy.1, hy.2⟩, fun hN => ?_⟩
  exact not_mem_nodesOn_of_mem_coordOpens k C e hdim hab hy.1 hy.2 ⟨hyC, hN⟩

end CoordinateCover

section LineUnits

variable (k : Type u) [Field k] {X : Scheme.{u}} [NoetherianSpace X]
  [AlgebraicGeometry.IsReduced X] (C : ↥(irreducibleComponents X))
  (e : componentUnionScheme X {C} ≅ projectiveSpace k 1)

/-- Over an open contained in a component union, the section map of the closed immersion of
the union is an isomorphism. -/
theorem isIso_componentUnionInclusion_app (S : Set ↥(irreducibleComponents X)) (V : X.Opens)
    (hV : (V : Set X) ⊆ componentClosedUnion X S) {W : X.Opens} (hWV : W ≤ V) :
    IsIso ((componentUnionInclusion X S).app W) := by
  haveI := componentUnionInclusion_restrict_isIso X S V hV
  have h := morphismRestrict_app (componentUnionInclusion X S) V (V.ι ⁻¹ᵁ W)
  have hW : V.ι ''ᵁ V.ι ⁻¹ᵁ W = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inter, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hWV
  haveI : IsIso ((componentUnionInclusion X S).app (V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :=
    IsIso.of_isIso_fac_right h.symm
  rw [← hW]
  infer_instance

theorem isIso_componentLine_app {W : X.Opens} (hW : W ≤ leafOpen X C) :
    IsIso ((componentLine k C e).app W) := by
  haveI := isIso_componentUnionInclusion_app {C} (leafOpen X C) (leafOpen_subset X C) hW
  change IsIso ((e.inv ≫ componentUnionInclusion X {C}).app W)
  rw [Scheme.comp_app]
  infer_instance

/-- A unit on an open of the open part of `C`, transported from the projective line through
the section isomorphism of the closed immersion. -/
def lineUnit {W : X.Opens} (hW : W ≤ leafOpen X C)
    (v : Γ(projectiveSpace k 1, componentLine k C e ⁻¹ᵁ W)ˣ) : Γ(X, W)ˣ :=
  haveI := isIso_componentLine_app k C e hW
  Units.map
    (asIso ((componentLine k C e).app W)).commRingCatIsoToRingEquiv.symm.toRingHom.toMonoidHom v

theorem app_lineUnit {W : X.Opens} (hW : W ≤ leafOpen X C)
    (v : Γ(projectiveSpace k 1, componentLine k C e ⁻¹ᵁ W)ˣ) :
    (componentLine k C e).app W (lineUnit k C e hW v : Γ(X, W)) = v := by
  haveI := isIso_componentLine_app k C e hW
  exact (asIso ((componentLine k C e).app W)).commRingCatIsoToRingEquiv.apply_symm_apply v

theorem componentLine_app_injective {W : X.Opens} (hW : W ≤ leafOpen X C) :
    Function.Injective ((componentLine k C e).app W) := by
  haveI := isIso_componentLine_app k C e hW
  intro a b h
  exact (asIso ((componentLine k C e).app W)).commRingCatIsoToRingEquiv.injective h

theorem lineUnit_res {V W : X.Opens} (hW : W ≤ leafOpen X C) (hVW : V ≤ W)
    (v : Γ(projectiveSpace k 1, componentLine k C e ⁻¹ᵁ W)ˣ) :
    res X hVW (lineUnit k C e hW v : Γ(X, W)) =
      lineUnit k C e (hVW.trans hW)
        (Units.map (res (projectiveSpace k 1)
          ((componentLine k C e).preimage_le_preimage_of_le hVW)).toMonoidHom v) := by
  apply componentLine_app_injective k C e (hVW.trans hW)
  rw [app_res, app_lineUnit, app_lineUnit]
  rfl

theorem lineUnit_one {W : X.Opens} (hW : W ≤ leafOpen X C) : lineUnit k C e hW 1 = 1 :=
  map_one _

end LineUnits

section CoordinateCocycle

variable (k : Type u) [Field k] {X : Scheme.{u}} [NoetherianSpace X]
  [AlgebraicGeometry.IsReduced X] (C : ↥(irreducibleComponents X))
  (e : componentUnionScheme X {C} ≅ projectiveSpace k 1) (hdim : topologicalKrullDim X ≤ 1)

/-- The transported standard transition on the part of an overlap inside `C`. -/
def leafUnit (a b : CoordIndex C) : Γ(X, leafPiece k C e hdim a b)ˣ :=
  lineUnit k C e inf_le_right (standardOnLeafPiece k C e hdim a b)

theorem leafUnit_self (a : CoordIndex C) : leafUnit k C e hdim a a = 1 := by
  unfold leafUnit standardOnLeafPiece
  have h : monomialCocycle k 1 (coordChart k C e a) (coordChart k C e a) = 1 :=
    Units.ext ((monomialCocycle_isCocycle k 1).unit_self (coordChart k C e a))
  rw [h, map_one, lineUnit_one]

open scoped Classical in
/-- The coordinate cocycle: the transported standard transition on the part of an overlap
inside `C`, extended by `1` on the part outside `C`. -/
def coordUnits (a b : CoordIndex C) : Γ(X, coordOverlap k C e hdim a b)ˣ :=
  if hab : a = b then 1 else
    Units.map (res X (coordOverlap_le_sup k C e hdim hab)).toMonoidHom
      (disjointUnit (leafPiece_inf_complPiece k C e hdim a b) (leafUnit k C e hdim a b) 1)

theorem coordUnits_self (a : CoordIndex C) : coordUnits k C e hdim a a = 1 := by
  unfold coordUnits
  rw [dif_pos rfl]

theorem coordUnits_res_leaf (a b : CoordIndex C) :
    res X (inf_le_left : leafPiece k C e hdim a b ≤ coordOverlap k C e hdim a b)
        (coordUnits k C e hdim a b : Γ(X, coordOverlap k C e hdim a b)) =
      (leafUnit k C e hdim a b : Γ(X, leafPiece k C e hdim a b)) := by
  unfold coordUnits
  split_ifs with hab
  · subst hab
    rw [leafUnit_self, Units.val_one, Units.val_one, map_one]
  · change res X _ (res X (coordOverlap_le_sup k C e hdim hab)
      (disjointUnit (leafPiece_inf_complPiece k C e hdim a b) (leafUnit k C e hdim a b) 1 :
        Γ(X, leafPiece k C e hdim a b ⊔ complPiece k C e hdim a b))) = _
    rw [res_res]
    exact res_disjointUnit_left _ _ _

theorem coordUnits_res_compl (a b : CoordIndex C) :
    res X (inf_le_left : complPiece k C e hdim a b ≤ coordOverlap k C e hdim a b)
        (coordUnits k C e hdim a b : Γ(X, coordOverlap k C e hdim a b)) = 1 := by
  unfold coordUnits
  split_ifs with hab
  · rw [Units.val_one, map_one]
  · change res X _ (res X (coordOverlap_le_sup k C e hdim hab)
      (disjointUnit (leafPiece_inf_complPiece k C e hdim a b) (leafUnit k C e hdim a b) 1 :
        Γ(X, leafPiece k C e hdim a b ⊔ complPiece k C e hdim a b))) = _
    rw [res_res, res_disjointUnit_right]
    rfl

/-- The coordinate cocycle restricted to any open inside `C` is the transported standard
transition. -/
theorem coordUnits_res_of_le_leafOpen (a b : CoordIndex C) {W : X.Opens}
    (hW : W ≤ coordOverlap k C e hdim a b) (hWl : W ≤ leafOpen X C) :
    res X hW (coordUnits k C e hdim a b : Γ(X, coordOverlap k C e hdim a b)) =
      lineUnit k C e hWl
        (Units.map (res (projectiveSpace k 1)
          (((componentLine k C e).preimage_le_preimage_of_le (le_inf hW hWl)).trans
            (preimage_leafPiece_le k C e hdim a b))).toMonoidHom
          (monomialCocycle k 1 (coordChart k C e a) (coordChart k C e b))) := by
  have h1 : res X hW (coordUnits k C e hdim a b : Γ(X, coordOverlap k C e hdim a b)) =
      res X (le_inf hW hWl : W ≤ leafPiece k C e hdim a b)
        (res X inf_le_left (coordUnits k C e hdim a b : Γ(X, coordOverlap k C e hdim a b))) := by
    rw [res_res]
  rw [h1, coordUnits_res_leaf, leafUnit, lineUnit_res]
  apply componentLine_app_injective k C e hWl
  rw [app_lineUnit, app_lineUnit]
  change res (projectiveSpace k 1) _ (res (projectiveSpace k 1) _ _) = res (projectiveSpace k 1) _ _
  exact res_res _ _ _ _

theorem coordUnits_isCocycle : IsCocycle X (coordOpens k C e hdim) (coordUnits k C e hdim) where
  unit_self a := by
    rw [coordUnits_self]
    rfl
  mul_res i j l := by
    by_cases hall : i = j ∧ j = l
    · obtain ⟨rfl, rfl⟩ := hall
      simp only [coordUnits_self, Units.val_one, map_one, one_mul]
    · have hT : coordOpens k C e hdim i ⊓ coordOpens k C e hdim j ⊓ coordOpens k C e hdim l ≤
          leafOpen X C ⊔ complementOpen X C := by
        by_cases hij : i = j
        · subst hij
          have hil : i ≠ l := fun h => hall ⟨rfl, h⟩
          exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans
            (coordOpens_inter_le k C e hdim hil)
        · exact inf_le_left.trans (coordOpens_inter_le k C e hdim hij)
      apply sections_ext_of_disjoint hT
      · rw [map_mul]
        simp only [res_res]
        have hres : ∀ (a b : CoordIndex C)
            (h : coordOpens k C e hdim i ⊓ coordOpens k C e hdim j ⊓ coordOpens k C e hdim l ⊓
              leafOpen X C ≤ coordOverlap k C e hdim a b),
            res X h (coordUnits k C e hdim a b : Γ(X, coordOverlap k C e hdim a b)) =
              lineUnit k C e inf_le_right
                (Units.map (res (projectiveSpace k 1)
                  (((componentLine k C e).preimage_le_preimage_of_le (le_inf h inf_le_right)).trans
                    (preimage_leafPiece_le k C e hdim a b))).toMonoidHom
                  (monomialCocycle k 1 (coordChart k C e a) (coordChart k C e b))) :=
          fun a b h => coordUnits_res_of_le_leafOpen k C e hdim a b h inf_le_right
        rw [hres i j _, hres j l _, hres i l _]
        apply componentLine_app_injective k C e inf_le_right
        rw [app_mul, app_lineUnit, app_lineUnit, app_lineUnit]
        change res (projectiveSpace k 1) _ _ * res (projectiveSpace k 1) _ _ =
          res (projectiveSpace k 1) _ _
        exact IsCocycle.mul_res_of_le (projectiveSpace k 1) (standardOpens k) (monomialCocycle k 1)
          (monomialCocycle_isCocycle k 1)
          (le_inf (le_inf
            (((componentLine k C e).preimage_le_preimage_of_le
              (inf_le_left.trans (inf_le_left.trans inf_le_left))).trans
              (preimage_coordOpens_le k C e hdim i))
            (((componentLine k C e).preimage_le_preimage_of_le
              (inf_le_left.trans (inf_le_left.trans inf_le_right))).trans
              (preimage_coordOpens_le k C e hdim j)))
            (((componentLine k C e).preimage_le_preimage_of_le
              (inf_le_left.trans inf_le_right)).trans (preimage_coordOpens_le k C e hdim l)))
      · rw [map_mul]
        simp only [res_res]
        have key : ∀ (a b : CoordIndex C)
            (h : coordOpens k C e hdim i ⊓ coordOpens k C e hdim j ⊓ coordOpens k C e hdim l ⊓
              complementOpen X C ≤ coordOverlap k C e hdim a b),
            res X h (coordUnits k C e hdim a b : Γ(X, coordOverlap k C e hdim a b)) = 1 := by
          intro a b h
          have h' : coordOpens k C e hdim i ⊓ coordOpens k C e hdim j ⊓ coordOpens k C e hdim l ⊓
              complementOpen X C ≤ complPiece k C e hdim a b := le_inf h inf_le_right
          rw [← res_res X h' inf_le_left, coordUnits_res_compl, map_one]
        rw [key i j _, key j l _, key i l _, one_mul]

/-- The coordinate line bundle of the component `C`, glued from the coordinate cocycle. -/
def coordinateBundle : InvertibleSheaf X :=
  invertibleSheaf X (coordOpens k C e hdim) (coordUnits k C e hdim)
    (coordUnits_isCocycle k C e hdim) (coordOpens_iSup k C e hdim)

theorem coordinateBundle_toPic :
    (coordinateBundle k C e hdim).toPic =
      picardClass X (coordOpens k C e hdim) (coordUnits k C e hdim)
        (coordUnits_isCocycle k C e hdim) (coordOpens_iSup k C e hdim) := rfl

/-- The pullback of the coordinate cocycle along the closed immersion of the component is the
refinement of the standard `O(1)` cocycle to the preimage cover. -/
theorem pullbackUnits_componentLine_coordUnits :
    pullbackUnits (componentLine k C e) (coordOpens k C e hdim) (coordUnits k C e hdim) =
      refinedUnits (projectiveSpace k 1) (standardOpens k) (monomialCocycle k 1)
        (fun a => componentLine k C e ⁻¹ᵁ coordOpens k C e hdim a) (coordChart k C e)
        (preimage_coordOpens_le k C e hdim) := by
  funext a b
  apply Units.ext
  rw [pullbackUnits_val, refinedUnits_val]
  by_cases hab : a = b
  · subst hab
    rw [coordUnits_self, Units.val_one, app_one, map_one,
      (monomialCocycle_isCocycle k 1).unit_self, map_one]
  · have hle := preimage_coordOverlap_le_leafPiece k C e hdim hab
    rw [← res_res (projectiveSpace k 1) hle
      ((componentLine k C e).preimage_le_preimage_of_le
        (inf_le_left : leafPiece k C e hdim a b ≤ coordOverlap k C e hdim a b)),
      ← app_res, coordUnits_res_leaf, leafUnit, app_lineUnit]
    change res (projectiveSpace k 1) _ (res (projectiveSpace k 1) _ _) = _
    exact res_res _ _ _ _

/-- The Picard class of the pulled-back coordinate cocycle is the class of `O(1)`. -/
theorem picardClass_pullbackUnits_coordUnits :
    picardClass (projectiveSpace k 1) (fun a => componentLine k C e ⁻¹ᵁ coordOpens k C e hdim a)
        (pullbackUnits (componentLine k C e) (coordOpens k C e hdim) (coordUnits k C e hdim))
        (pullbackUnits_isCocycle _ _ _ (coordUnits_isCocycle k C e hdim))
        (pullbackUnits_cover _ _ (coordOpens_iSup k C e hdim)) =
      (monomialLineBundle k 1).toPic := by
  rw [picardClass_congr _ (pullbackUnits_componentLine_coordUnits k C e hdim)]
  exact (picardClass_eq_of_refinement (projectiveSpace k 1) (standardOpens k) (monomialCocycle k 1)
    (monomialCocycle_isCocycle k 1) _ (coordChart k C e) (preimage_coordOpens_le k C e hdim)
    (pullbackUnits_cover _ _ (coordOpens_iSup k C e hdim))).symm

/-- Under the pullback compatibility of glued line bundles, the coordinate bundle has component
exponent `1` on its component. -/
theorem componentExponent_coordinateBundle_self (hP : PullbackGluedClass.{u}) :
    componentExponent k X {C} e (coordinateBundle k C e hdim) = 1 := by
  have hP' : (pullbackInvertibleSheaf (componentLine k C e) (coordinateBundle k C e hdim)).toPic =
      picardClass (projectiveSpace k 1)
        (fun a => componentLine k C e ⁻¹ᵁ coordOpens k C e hdim a)
        (pullbackUnits (componentLine k C e) (coordOpens k C e hdim) (coordUnits k C e hdim))
        (pullbackUnits_isCocycle _ _ _ (coordUnits_isCocycle k C e hdim))
        (pullbackUnits_cover _ _ (coordOpens_iSup k C e hdim)) :=
    hP (componentLine k C e) (coordOpens k C e hdim) (coordUnits k C e hdim)
      (coordUnits_isCocycle k C e hdim) (coordOpens_iSup k C e hdim)
  have h1 : ProjectiveLineSheafExponent.exponent k
      (pullbackInvertibleSheaf (componentLine k C e) (coordinateBundle k C e hdim)) = 1 := by
    rw [← ProjectiveLinePicardExponent.value_toPic, hP', picardClass_pullbackUnits_coordUnits,
      ProjectiveLinePicardExponent.value_toPic, monomialLineBundle_exponent]
  have hiso : (pullbackInvertibleSheaf e.inv
      (componentUnionRestriction X {C} (coordinateBundle k C e hdim))).obj ≅
      (pullbackInvertibleSheaf (componentLine k C e) (coordinateBundle k C e hdim)).obj :=
    (schemeModulePullbackCompIso e.inv (componentUnionInclusion X {C})).app _
  unfold componentExponent chartExponent
  rw [← h1]
  exact ProjectiveLineSheafExponent.exponent_eq_of_iso k _ _ hiso

end CoordinateCocycle

end KltDP.Geometry.RationalTreePicard
