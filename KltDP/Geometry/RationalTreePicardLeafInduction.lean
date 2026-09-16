import KltDP.Geometry.RationalTreePicardLeafScalarIdentity
import KltDP.Geometry.RationalTreePicardComponentDimension
import KltDP.Geometry.RationalTreePicardMultidegree

/-!
# The leaf induction for the rational-tree Picard lemma

Passage from the curve `X` to the closed union `Z_S = componentUnionScheme X S` of a selection
of components, and the induction step of the kernel statement of `lem:tree-picard`.

* Inheritance: `Z_S` is a Noetherian space (`componentUnionScheme_noetherianSpace`), reduced
  (accepted instance), of dimension `≤ 1` when `X` is, and `ι_S ≫ f` is locally of finite type.
* Component correspondence: every component `D'` of `Z_S` is the preimage of an original
  component `componentImage X S D' ∈ S`; the correspondence is injective.
* Exponent transfer: an identification `φ : Z_S,{D'} ≅ Z_{D}` over `X` of the reduced closed
  subschemes carried by the same component transports a frame of `L` on `Z_D` to a frame of the
  restricted bundle on `Z_S,{D'}`, hence zero component exponent on `X` gives zero component
  exponent of `componentUnionRestriction X S L` on `Z_S` (for any identification with `P^1`).
* The induction step `leafInductionStep`: if every line bundle on `Z_{Cᶜ}` with all component
  exponents zero is trivial, then a line bundle on `X` with all component exponents zero is
  trivial (via `leafNodeUnitIsoOfExponentZero`), given the identification data
  `ComponentUnionIdentification X {C}ᶜ` of the components of `Z_{Cᶜ}` with the original
  components `D ≠ C`.
* The base case (one component) and the two-component case need no identification data:
  `trivial_of_subsingleton_components`, `trivial_of_two_components`.
* Assembly by strong induction on the number of components
  (`rationalTreePicard_trivial_of_exponents_zero`, and `multidegreeHom_injective_of_inheritance`
  for the kernel half of `lem:tree-picard`), given the identification data for all closed unions
  and the inheritance `InheritsLeafHypotheses` of the component-point tree and of the transverse
  branch germs to the complementary union of a leaf.

The identification data (uniqueness of the reduced closed subscheme structure on a component,
`Z_S,{D'} ≅ Z_D` over `X`) is stated as data here; see `LEMMA22_PROGRESS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

namespace KltDP.Geometry.RationalTreePicard

section Inheritance

variable (X : Scheme.{u}) [NoetherianSpace X] (S : Set ↥(irreducibleComponents X))

/-- The closed union of components is a Noetherian space (a closed subspace of one). -/
instance componentUnionScheme_noetherianSpace : NoetherianSpace (componentUnionScheme X S) :=
  (componentUnionInclusion X S).isEmbedding.isInducing.noetherianSpace

/-- Dimension at most one is inherited by the closed union. -/
theorem componentUnionScheme_topologicalKrullDim_le_one (hdim : topologicalKrullDim X ≤ 1) :
    topologicalKrullDim (componentUnionScheme X S) ≤ 1 :=
  (IsClosedEmbedding.topologicalKrullDim_le (componentUnionInclusion X S).base
    (componentUnionInclusion X S).isClosedEmbedding).trans hdim

/-- The closed union of components of a locally Noetherian scheme is locally Noetherian: on the
pullback of an affine cover, the section rings are quotients of Noetherian rings. -/
instance componentUnionScheme_isLocallyNoetherian [IsLocallyNoetherian X] :
    IsLocallyNoetherian (componentUnionScheme X S) := by
  let 𝒰 := X.affineCover.pullbackCover (componentUnionInclusion X S)
  haveI hci : ∀ i, IsClosedImmersion
      (pullback.snd (componentUnionInclusion X S) (X.affineCover.map i)) :=
    fun i => MorphismProperty.pullback_snd _ _ inferInstance
  haveI : ∀ i, IsAffine (𝒰.obj i) := fun i =>
    (IsClosedImmersion.isAffine_surjective_of_isAffine
      (pullback.snd (componentUnionInclusion X S) (X.affineCover.map i))).1
  rw [isLocallyNoetherian_iff_of_affine_openCover 𝒰]
  intro i
  haveI hX : IsNoetherianRing Γ(X.affineCover.obj i, ⊤) :=
    (isLocallyNoetherian_iff_of_affine_openCover X.affineCover).mp inferInstance i
  exact isNoetherianRing_of_surjective _ _
    (pullback.snd (componentUnionInclusion X S) (X.affineCover.map i)).appTop.hom
    (IsClosedImmersion.isAffine_surjective_of_isAffine
      (pullback.snd (componentUnionInclusion X S) (X.affineCover.map i))).2

/-- The structure morphism of the closed union is locally of finite type. -/
instance componentUnionInclusion_comp_locallyOfFiniteType {k : Type u} [CommRing k]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (componentUnionInclusion X S ≫ f) :=
  inferInstance

/-- The original component underlying a component of the closed union. -/
def componentImage (D : ↥(irreducibleComponents (componentUnionScheme X S))) :
    ↥(irreducibleComponents X) :=
  Classical.choose (exists_componentUnionComponent_image X S D)

theorem componentImage_mem (D : ↥(irreducibleComponents (componentUnionScheme X S))) :
    componentImage X S D ∈ S :=
  (Classical.choose_spec (exists_componentUnionComponent_image X S D)).1

theorem image_componentImage (D : ↥(irreducibleComponents (componentUnionScheme X S))) :
    (componentUnionInclusion X S).base '' D.1 = (componentImage X S D).1 :=
  (Classical.choose_spec (exists_componentUnionComponent_image X S D)).2

/-- A component of the closed union is the preimage of its original component. -/
theorem componentImage_preimage (D : ↥(irreducibleComponents (componentUnionScheme X S))) :
    D.1 = (componentUnionInclusion X S).base ⁻¹' (componentImage X S D).1 := by
  have hsub : D.1 ⊆ (componentUnionInclusion X S).base ⁻¹' (componentImage X S D).1 := by
    rw [← image_componentImage]
    exact Set.subset_preimage_image _ _
  exact hsub.antisymm (D.2.2 (componentUnionInclusion_preimage_isIrreducible X S _
    (componentImage_mem X S D)) hsub)

theorem componentImage_injective : Function.Injective (componentImage X S) := by
  intro D₁ D₂ h
  apply Subtype.ext
  rw [componentImage_preimage X S D₁, componentImage_preimage X S D₂, h]

/-- Every selected original component is the image of a component of the closed union: the
component of a lift of its generic point. -/
theorem exists_componentImage_eq (C : ↥(irreducibleComponents X)) (hC : C ∈ S) :
    ∃ D : ↥(irreducibleComponents (componentUnionScheme X S)), componentImage X S D = C := by
  have hgeneric := C.2.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents C.1 C.2)
  obtain ⟨y, hy⟩ := component_subset_range_componentUnionInclusion X S C hC hgeneric.mem
  let D : ↥(irreducibleComponents (componentUnionScheme X S)) :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  refine ⟨D, ?_⟩
  have hyD : (componentUnionInclusion X S).base y ∈ (componentImage X S D).1 := by
    rw [← image_componentImage]
    exact ⟨y, mem_irreducibleComponent, rfl⟩
  rw [hy] at hyD
  have hsub : C.1 ⊆ (componentImage X S D).1 :=
    (hgeneric.mem_closed_set_iff
      (isClosed_of_mem_irreducibleComponents _ (componentImage X S D).2)).mp hyD
  exact Subtype.ext ((C.2.2 (componentImage X S D).2.1 hsub).antisymm hsub)

/-- Two distinct selected components give two distinct components of the closed union. -/
theorem nontrivial_components_componentUnionScheme (C D : ↥(irreducibleComponents X))
    (hC : C ∈ S) (hD : D ∈ S) (hCD : C ≠ D) :
    Nontrivial ↥(irreducibleComponents (componentUnionScheme X S)) := by
  obtain ⟨C', hC'⟩ := exists_componentImage_eq X S C hC
  obtain ⟨D', hD'⟩ := exists_componentImage_eq X S D hD
  refine ⟨⟨C', D', fun h => hCD ?_⟩⟩
  rw [← hC', ← hD', h]

/-- The component correspondence, as an equivalence of the components of the closed union with
the selection. -/
def componentImageEquiv : ↥(irreducibleComponents (componentUnionScheme X S)) ≃ ↥S :=
  Equiv.ofBijective (fun D' => ⟨componentImage X S D', componentImage_mem X S D'⟩)
    ⟨fun D₁ D₂ h => componentImage_injective X S (congrArg Subtype.val h),
      fun ⟨C, hC⟩ => by
        obtain ⟨D', hD'⟩ := exists_componentImage_eq X S C hC
        exact ⟨D', Subtype.ext hD'⟩⟩

/-- Intersection points of the closed union map to intersection points of `X`. -/
theorem image_componentIntersectionPoints_subset :
    (componentUnionInclusion X S).base '' componentIntersectionPoints (componentUnionScheme X S) ⊆
      componentIntersectionPoints X := by
  rintro _ ⟨q, ⟨D₁, D₂, hne, hq₁, hq₂⟩, rfl⟩
  refine ⟨componentImage X S D₁, componentImage X S D₂,
    fun h => hne (componentImage_injective X S h), ?_, ?_⟩
  · rw [← image_componentImage]
    exact ⟨q, hq₁, rfl⟩
  · rw [← image_componentImage]
    exact ⟨q, hq₂, rfl⟩

/-- A point on two distinct selected components is the image of an intersection point of the
closed union. -/
theorem exists_componentIntersectionPoint_of_two_components (x : X)
    (C D : ↥(irreducibleComponents X)) (hC : C ∈ S) (hD : D ∈ S) (hCD : C ≠ D)
    (hxC : x ∈ C.1) (hxD : x ∈ D.1) :
    ∃ q ∈ componentIntersectionPoints (componentUnionScheme X S),
      (componentUnionInclusion X S).base q = x := by
  obtain ⟨q, rfl⟩ := component_subset_range_componentUnionInclusion X S C hC hxC
  obtain ⟨C', hC'⟩ := exists_componentImage_eq X S C hC
  obtain ⟨D', hD'⟩ := exists_componentImage_eq X S D hD
  refine ⟨q, ⟨C', D', fun h => hCD (by rw [← hC', ← hD', h]), ?_, ?_⟩, rfl⟩
  · rw [componentImage_preimage X S C', hC']
    exact hxC
  · rw [componentImage_preimage X S D', hD']
    exact hxD

end Inheritance

section Transfer

variable (X : Scheme.{u}) [NoetherianSpace X] (L : InvertibleSheaf X)

/-- A frame of `L` on the closed union of an original component transports, along a scheme
isomorphism over `X`, to a frame of the pullback of `L` along the corresponding closed immersion. -/
def frameOfIsoOver {Y : Scheme.{u}} (g : Y ⟶ X) (D : ↥(irreducibleComponents X))
    (φ : Y ≅ componentUnionScheme X {D}) (hφ : φ.hom ≫ componentUnionInclusion X {D} = g)
    (frame : (schemeModulePullback (componentUnionInclusion X {D})).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X {D}).ringCatSheaf) :
    (schemeModulePullback g).obj L.obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf :=
  (eqToIso (congrArg (fun m => (schemeModulePullback m).obj L.obj) hφ)).symm ≪≫
    (schemeModulePullbackCompIso φ.hom (componentUnionInclusion X {D})).symm.app L.obj ≪≫
    (schemeModulePullback φ.hom).mapIso frame ≪≫ schemeModulePullbackUnitIso φ.hom

/-- A frame on a closed union transports along an equality of the selected sets. -/
def frameOfSetEq {S T : Set ↥(irreducibleComponents X)} (h : S = T)
    (frame : (schemeModulePullback (componentUnionInclusion X T)).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X T).ringCatSheaf) :
    (schemeModulePullback (componentUnionInclusion X S)).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X S).ringCatSheaf := by
  subst h
  exact frame

variable {k : Type u} [Field k] (S : Set ↥(irreducibleComponents X))

/-- Zero component exponent of `L` on an original component gives zero component exponent of
the restriction of `L` to the closed union, on the corresponding component of the union, for
any identification of that component with the projective line, given an identification over
`X` of the two reduced closed subscheme structures. -/
theorem componentExponent_componentUnionRestriction_eq_zero
    (D' : ↥(irreducibleComponents (componentUnionScheme X S)))
    (e' : componentUnionScheme (componentUnionScheme X S) {D'} ≅ projectiveSpace k 1)
    (e : componentUnionScheme X {componentImage X S D'} ≅ projectiveSpace k 1)
    (φ : componentUnionScheme (componentUnionScheme X S) {D'} ≅
      componentUnionScheme X {componentImage X S D'})
    (hφ : φ.hom ≫ componentUnionInclusion X {componentImage X S D'} =
      componentUnionInclusion (componentUnionScheme X S) {D'} ≫ componentUnionInclusion X S)
    (hzero : componentExponent k X {componentImage X S D'} e L = 0) :
    componentExponent k (componentUnionScheme X S) {D'} e' (componentUnionRestriction X S L) = 0 :=
  (componentExponent_eq_zero_iff k (componentUnionScheme X S) {D'} e'
    (componentUnionRestriction X S L)).mpr
    ⟨(schemeModulePullbackCompIso (componentUnionInclusion (componentUnionScheme X S) {D'})
        (componentUnionInclusion X S)).app L.obj ≪≫
      frameOfIsoOver X L _ (componentImage X S D') φ hφ
        (componentFrameOfExponentZero k X {componentImage X S D'} e L hzero)⟩

/-- Identification data: each component of the closed union of `S`, as a reduced closed
subscheme, is identified over `X` with the original component carrying it. -/
structure ComponentUnionIdentification where
  /-- the identification of the reduced closed subschemes -/
  iso : ∀ D' : ↥(irreducibleComponents (componentUnionScheme X S)),
    componentUnionScheme (componentUnionScheme X S) {D'} ≅
      componentUnionScheme X {componentImage X S D'}
  /-- it is an identification over `X` -/
  iso_hom_over : ∀ D' : ↥(irreducibleComponents (componentUnionScheme X S)),
    (iso D').hom ≫ componentUnionInclusion X {componentImage X S D'} =
      componentUnionInclusion (componentUnionScheme X S) {D'} ≫ componentUnionInclusion X S

variable {X S}

/-- The identifications of the components of the closed union with the projective line induced
by identifications of the original components. -/
def ComponentUnionIdentification.projectiveLineIso (ident : ComponentUnionIdentification X S)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (D' : ↥(irreducibleComponents (componentUnionScheme X S))) :
    componentUnionScheme (componentUnionScheme X S) {D'} ≅ projectiveSpace k 1 :=
  ident.iso D' ≪≫ e (componentImage X S D')

/-- All component exponents of the restricted bundle vanish when all original ones do. -/
theorem ComponentUnionIdentification.componentExponent_eq_zero
    (ident : ComponentUnionIdentification X S)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (hzero : ∀ C : ↥(irreducibleComponents X), componentExponent k X {C} (e C) L = 0)
    (D' : ↥(irreducibleComponents (componentUnionScheme X S))) :
    componentExponent k (componentUnionScheme X S) {D'} (ident.projectiveLineIso e D')
      (componentUnionRestriction X S L) = 0 :=
  componentExponent_componentUnionRestriction_eq_zero X L S D' _ (e _) (ident.iso D')
    (ident.iso_hom_over D') (hzero _)

end Transfer

section Factorization

variable (X : Scheme.{u}) [NoetherianSpace X] (S : Set ↥(irreducibleComponents X))

/-- A factorization over `X` of the closed immersion of a component of the closed union through
the reduced closed subscheme of the corresponding original component is an isomorphism: it is a
surjective closed immersion into a reduced scheme. -/
theorem isIso_of_factorization (D' : ↥(irreducibleComponents (componentUnionScheme X S)))
    (g' : componentUnionScheme (componentUnionScheme X S) {D'} ⟶
      componentUnionScheme X {componentImage X S D'})
    (hg' : g' ≫ componentUnionInclusion X {componentImage X S D'} =
      componentUnionInclusion (componentUnionScheme X S) {D'} ≫ componentUnionInclusion X S) :
    IsIso g' := by
  haveI : IsClosedImmersion (g' ≫ componentUnionInclusion X {componentImage X S D'}) := by
    rw [hg']
    infer_instance
  haveI : IsClosedImmersion g' :=
    IsClosedImmersion.of_comp_isClosedImmersion g' (componentUnionInclusion X {componentImage X S D'})
  haveI : Surjective g' := ⟨fun z => by
    have hz : (componentUnionInclusion X {componentImage X S D'}).base z ∈
        (componentImage X S D').1 := by
      have := Set.mem_range_self (f := (componentUnionInclusion X {componentImage X S D'}).base) z
      rwa [range_componentUnionInclusion, coe_componentClosedUnion_singleton] at this
    rw [← image_componentImage] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have hw' : w ∈ Set.range (componentUnionInclusion (componentUnionScheme X S) {D'}).base := by
      rwa [range_componentUnionInclusion, coe_componentClosedUnion_singleton]
    obtain ⟨v, rfl⟩ := hw'
    refine ⟨v, (componentUnionInclusion X {componentImage X S D'}).isClosedEmbedding.injective ?_⟩
    rw [← hwz, ← Scheme.comp_base_apply, hg', Scheme.comp_base_apply]⟩
  exact isIso_of_isClosedImmersion_of_surjective g'

/-- Identification data from factorizations over `X` of the component inclusions of the closed
union through the original components: this is what remains of the uniqueness of the reduced
closed subscheme structure (see `LEMMA22_PROGRESS.md`). -/
def componentUnionIdentificationOfFactorization
    (g : ∀ D' : ↥(irreducibleComponents (componentUnionScheme X S)),
      componentUnionScheme (componentUnionScheme X S) {D'} ⟶
        componentUnionScheme X {componentImage X S D'})
    (hg : ∀ D', g D' ≫ componentUnionInclusion X {componentImage X S D'} =
      componentUnionInclusion (componentUnionScheme X S) {D'} ≫ componentUnionInclusion X S) :
    ComponentUnionIdentification X S where
  iso D' :=
    haveI := isIso_of_factorization X S D' (g D') (hg D')
    asIso (g D')
  iso_hom_over D' := hg D'

end Factorization

section Induction

variable {X : Scheme.{u}} [NoetherianSpace X] [AlgebraicGeometry.IsReduced X]
  {k : Type u} [Field k] [IsAlgClosed k]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  {C : ↥(irreducibleComponents X)} {q : X} {U : X.affineOpens} {hq : q ∈ U.1}
  (h : LeafNodeChart X C q U hq)

include f h in
/-- The induction step: if every line bundle on the complementary union `Z_{Cᶜ}` with all
component exponents zero is trivial, then every line bundle on `X` with all component exponents
zero is trivial. The components of `Z_{Cᶜ}` are identified with the original components by the
given data. -/
theorem leafInductionStep (hcut : C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q})
    (ident : ComponentUnionIdentification X ({C}ᶜ))
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (IH : ∀ (e' : ∀ D' : ↥(irreducibleComponents (componentUnionScheme X ({C}ᶜ))),
        componentUnionScheme (componentUnionScheme X ({C}ᶜ)) {D'} ≅ projectiveSpace k 1)
      (L' : InvertibleSheaf (componentUnionScheme X ({C}ᶜ))),
      (∀ D', componentExponent k (componentUnionScheme X ({C}ᶜ)) {D'} (e' D') L' = 0) →
      Nonempty (L'.obj ≅
        _root_.SheafOfModules.unit (componentUnionScheme X ({C}ᶜ)).ringCatSheaf))
    (L : InvertibleSheaf X)
    (hzero : ∀ C : ↥(irreducibleComponents X), componentExponent k X {C} (e C) L = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) := by
  obtain ⟨frameC'⟩ := IH (ident.projectiveLineIso e) (componentUnionRestriction X ({C}ᶜ) L)
    (ident.componentExponent_eq_zero L e hzero)
  exact ⟨leafNodeUnitIsoOfExponentZero L f h hcut (e C) (hzero C) frameC'⟩

include f h in
/-- Two components meeting at a leaf node: no identification data is needed, the complement
of the leaf is literally the other component. -/
theorem trivial_of_two_components (hcut : C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q})
    (D : ↥(irreducibleComponents X)) (hCD : C ≠ D)
    (hall : ∀ E : ↥(irreducibleComponents X), E = C ∨ E = D)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (L : InvertibleSheaf X)
    (hzero : ∀ C : ↥(irreducibleComponents X), componentExponent k X {C} (e C) L = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) := by
  have hset : ({C}ᶜ : Set ↥(irreducibleComponents X)) = {D} := by
    ext E
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro hE
      rcases hall E with rfl | rfl
      · exact absurd rfl hE
      · rfl
    · rintro rfl
      exact fun h' => hCD h'.symm
  exact ⟨leafNodeUnitIsoOfExponentZero L f h hcut (e C) (hzero C)
    (frameOfSetEq X L hset (componentFrameOfExponentZero k X {D} (e D) L (hzero D)))⟩

end Induction

section BaseCase

variable (X : Scheme.{u}) [NoetherianSpace X]

omit [NoetherianSpace X] in
/-- With a single component, every point lies on it. -/
theorem mem_component_of_subsingleton [Subsingleton ↥(irreducibleComponents X)]
    (C : ↥(irreducibleComponents X)) (x : X) : x ∈ C.1 := by
  have hx : x ∈ (⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩ :
      ↥(irreducibleComponents X)).1 := mem_irreducibleComponent
  rwa [Subsingleton.elim (⟨irreducibleComponent x,
    irreducibleComponent_mem_irreducibleComponents x⟩ : ↥(irreducibleComponents X)) C] at hx

/-- With a single component, its closed union inclusion is surjective. -/
theorem surjective_componentUnionInclusion_of_subsingleton
    [Subsingleton ↥(irreducibleComponents X)] (C : ↥(irreducibleComponents X)) :
    Surjective (componentUnionInclusion X {C}) where
  surj := fun x => by
    have hx : x ∈ Set.range (componentUnionInclusion X {C}).base := by
      rw [range_componentUnionInclusion, coe_componentClosedUnion_singleton]
      exact mem_component_of_subsingleton X C x
    exact hx

/-- The base case: a reduced curve with a single component, a copy of the projective line, on
which a line bundle has zero exponent, carries a trivial bundle. -/
theorem trivial_of_subsingleton_components [AlgebraicGeometry.IsReduced X]
    [Subsingleton ↥(irreducibleComponents X)] {k : Type u} [Field k]
    (C : ↥(irreducibleComponents X)) (e : componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (L : InvertibleSheaf X) (hzero : componentExponent k X {C} e L = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) := by
  haveI := surjective_componentUnionInclusion_of_subsingleton X C
  haveI : IsIso (componentUnionInclusion X {C}) :=
    isIso_of_isClosedImmersion_of_surjective (componentUnionInclusion X {C})
  exact ⟨unitIsoOfPullbackUnitIso (asIso (componentUnionInclusion X {C})).symm L.obj
    (componentFrameOfExponentZero k X {C} e L hzero)⟩

end BaseCase

section Assembly

variable (k : Type u) [Field k]

/-- The kernel statement for one scheme: every line bundle with all component exponents zero
(for the given identifications of the components with the projective line) is trivial. -/
def ExponentsZeroTrivial (Y : Scheme.{u}) [NoetherianSpace Y] : Prop :=
  ∀ (e : ∀ C : ↥(irreducibleComponents Y), componentUnionScheme Y {C} ≅ projectiveSpace k 1)
    (L : InvertibleSheaf Y),
    (∀ C : ↥(irreducibleComponents Y), componentExponent k Y {C} (e C) L = 0) →
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf)

/-- Inheritance of the two combinatorial-geometric hypotheses (component-point tree, transverse
branch germs) from a curve to the complementary union of a leaf component; stated as a
hypothesis of the assembled induction, see `LEMMA22_PROGRESS.md`. (Noetherian, reduced, locally
Noetherian, dimension at most one and finite type over the base are inherited above.) -/
def InheritsLeafHypotheses : Prop :=
  ∀ (Y : Scheme.{u}) [NoetherianSpace Y] [IsLocallyNoetherian Y] [AlgebraicGeometry.IsReduced Y]
    (C : ↥(irreducibleComponents Y)) (q : Y),
    C.1 ∩ (componentClosedUnion Y ({C}ᶜ) : Set Y) = {q} →
    topologicalKrullDim Y ≤ 1 → (componentPointIncidenceGraph Y).IsTree →
    HasTransverseComponentBranches Y →
    (componentPointIncidenceGraph (componentUnionScheme Y ({C}ᶜ))).IsTree ∧
      HasTransverseComponentBranches (componentUnionScheme Y ({C}ᶜ))

/-- A tree component-point incidence graph has a component. -/
theorem nonempty_components_of_isTree (X : Scheme.{u})
    (hTree : (componentPointIncidenceGraph X).IsTree) :
    Nonempty ↥(irreducibleComponents X) := by
  obtain ⟨v⟩ := hTree.isConnected.nonempty
  rcases v with C | q
  · exact ⟨C⟩
  · obtain ⟨C, _, _, _, _⟩ := q.2
    exact ⟨C⟩

/-- The closed union of the complement of a component has fewer components. -/
theorem card_components_componentUnionScheme_compl_lt (X : Scheme.{u}) [NoetherianSpace X]
    (C : ↥(irreducibleComponents X)) :
    Nat.card ↥(irreducibleComponents (componentUnionScheme X ({C}ᶜ))) <
      Nat.card ↥(irreducibleComponents X) := by
  haveI hfin : Finite ↥(irreducibleComponents X) := by
    rw [Set.finite_coe_iff]
    exact NoetherianSpace.finite_irreducibleComponents
  have hssub : ({C}ᶜ : Set ↥(irreducibleComponents X)) ⊂ Set.univ := by
    refine Set.ssubset_univ_iff.mpr fun h => ?_
    have hC : C ∈ ({C}ᶜ : Set ↥(irreducibleComponents X)) := by
      rw [h]
      exact Set.mem_univ C
    exact hC (Set.mem_singleton C)
  calc Nat.card ↥(irreducibleComponents (componentUnionScheme X ({C}ᶜ)))
      ≤ Nat.card ↥({C}ᶜ : Set ↥(irreducibleComponents X)) :=
        Nat.card_le_card_of_injective
          (fun D' => ⟨componentImage X ({C}ᶜ) D', componentImage_mem X ({C}ᶜ) D'⟩)
          (fun D₁ D₂ h => componentImage_injective X ({C}ᶜ) (congrArg Subtype.val h))
    _ < Nat.card ↥(irreducibleComponents X) := by
        rw [Set.Nat.card_coe_set_eq, ← Set.ncard_univ]
        exact Set.ncard_lt_ncard hssub

variable [IsAlgClosed k]

/-- The kernel statement of `lem:tree-picard` by induction on the number of components, given
the identification data of the components of closed unions and the inheritance of the standing
hypotheses to the complementary union of a leaf. -/
theorem rationalTreePicard_trivial_of_exponents_zero
    (ident : ∀ (Y : Scheme.{u}) [NoetherianSpace Y] (S : Set ↥(irreducibleComponents Y)),
      ComponentUnionIdentification Y S)
    (hinherit : InheritsLeafHypotheses.{u}) (n : ℕ) :
    ∀ (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
      [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f],
      Nat.card ↥(irreducibleComponents X) = n →
      topologicalKrullDim X ≤ 1 → (componentPointIncidenceGraph X).IsTree →
      HasTransverseComponentBranches X → ExponentsZeroTrivial k X := by
  refine Nat.strong_induction_on n ?_
  intro n IHn X _ _ _ f _ hcard hdim hTree htrans e L hzero
  haveI hfin : Finite ↥(irreducibleComponents X) := by
    rw [Set.finite_coe_iff]
    exact NoetherianSpace.finite_irreducibleComponents
  have hne : Nonempty ↥(irreducibleComponents X) := nonempty_components_of_isTree X hTree
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · -- one component
    have hpos : 0 < Nat.card ↥(irreducibleComponents X) := Nat.card_pos
    have h1 : Nat.card ↥(irreducibleComponents X) = 1 := by omega
    haveI hsub : Subsingleton ↥(irreducibleComponents X) := (Nat.card_eq_one_iff_unique.mp h1).1
    obtain ⟨C⟩ := hne
    exact trivial_of_subsingleton_components X C (e C) L (hzero C)
  · -- at least two components: a leaf and the induction hypothesis on its complement
    haveI : Nontrivial ↥(irreducibleComponents X) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨C, q, hcut, hcharts⟩ := exists_leafNodeChart X hdim hTree htrans
    obtain ⟨_, ⟨U, hU, rfl⟩, hqU, -⟩ :=
      (isBasis_affine_open X).exists_subset_of_mem_open (Set.mem_univ q) isOpen_univ
    have h : LeafNodeChart X C q ⟨U, hU⟩ hqU := hcharts ⟨U, hU⟩ hqU
    obtain ⟨hTreeZ, htransZ⟩ := hinherit X C q hcut hdim hTree htrans
    have IHZ := IHn _ (hcard ▸ card_components_componentUnionScheme_compl_lt X C)
      (componentUnionScheme X ({C}ᶜ)) (componentUnionInclusion X ({C}ᶜ) ≫ f) rfl
      (componentUnionScheme_topologicalKrullDim_le_one X _ hdim) hTreeZ htransZ
    exact leafInductionStep f h hcut (ident X ({C}ᶜ)) e IHZ L hzero

/-- The kernel half of `lem:tree-picard` under the same hypotheses: the multidegree
homomorphism is injective. -/
theorem multidegreeHom_injective_of_inheritance
    (ident : ∀ (Y : Scheme.{u}) [NoetherianSpace Y] (S : Set ↥(irreducibleComponents Y)),
      ComponentUnionIdentification Y S)
    (hinherit : InheritsLeafHypotheses.{u})
    (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (htrans : HasTransverseComponentBranches X)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1) :
    Function.Injective (multidegreeHom k X e) :=
  (multidegreeHom_injective_iff k X e).mpr fun L hL =>
    rationalTreePicard_trivial_of_exponents_zero k ident hinherit _ X f rfl hdim hTree htrans
      e L hL

end Assembly

end KltDP.Geometry.RationalTreePicard
