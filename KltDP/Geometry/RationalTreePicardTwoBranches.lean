import KltDP.Geometry.RationalTreePicardTransverseInheritance

/-!
# Transverse branches allow exactly two components at a node: the algebra

BRIEF12, task (a), algebraic core. In a two-dimensional vector space, two proper subspaces
sharing a nonzero vector are both the line through it, so they cannot contain the two members of
a linearly independent pair (`two_branches_core`). In a Noetherian local ring `R`, the image in
the cotangent space of an ideal `I < m` is a proper subspace (`cotangentImage_ne_top`, Nakayama
through `IsLocalRing.CotangentSpace.span_image_eq_top_iff`). Hence (`two_branches_local`): with
cotangent dimension two, two branch ideals `I_D, I_E < m` cannot both contain a class `b ≠ 0` while
also containing the two members of an independent pair — which is exactly the configuration
produced by the transverse data at a point on three components `C, D, E` (`b` the class of the
`Cᶜ`-germ of the pair `(C, Cᶜ)`, the pair from `(D, Dᶜ)`).

The geometric instantiation (the branch ideal of a component `D` through `q` is not the maximal
ideal of the stalk: the generic point of `D` gives a smaller prime) is the next step; see
`LEMMA22_PROGRESS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.RationalTreePicard

section LinearAlgebra

variable {κ V : Type*} [Field κ] [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]

/-- A proper subspace of a two-dimensional space containing a nonzero vector is its line. -/
theorem eq_span_singleton_of_ne_top (h2 : Module.finrank κ V = 2) (L : Submodule κ V)
    (hL : L ≠ ⊤) {b : V} (hb0 : b ≠ 0) (hbL : b ∈ L) : L = κ ∙ b := by
  have hle : (κ ∙ b) ≤ L := (Submodule.span_singleton_le_iff_mem b L).mpr hbL
  have hlt : Module.finrank κ L < Module.finrank κ (⊤ : Submodule κ V) :=
    Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hL)
  rw [finrank_top, h2] at hlt
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_span_singleton hb0]; omega)).symm

/-- Two proper subspaces of a two-dimensional space sharing a nonzero vector cannot contain the
two members of a linearly independent pair. -/
theorem two_branches_core (h2 : Module.finrank κ V = 2) (LD LE : Submodule κ V)
    (hD : LD ≠ ⊤) (hE : LE ≠ ⊤) {b c d : V} (hb0 : b ≠ 0) (hbD : b ∈ LD) (hbE : b ∈ LE)
    (hc : c ∈ LD) (hd : d ∈ LE) (hcd : LinearIndependent κ ![c, d]) : False := by
  rw [eq_span_singleton_of_ne_top h2 LD hD hb0 hbD] at hc
  rw [eq_span_singleton_of_ne_top h2 LE hE hb0 hbE] at hd
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hc
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hd
  have hsb : s • b ≠ 0 := by simpa using hcd.ne_zero 0
  have hs : s ≠ 0 := by
    rintro rfl
    exact hsb (zero_smul κ b)
  exact ((LinearIndependent.pair_iff' hsb).mp hcd) (t / s)
    (by rw [smul_smul, div_mul_cancel₀ t hs])

end LinearAlgebra

section CotangentImage

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The image in the cotangent space of the elements of an ideal contained in the maximal
ideal. -/
def cotangentImage (I : Ideal R) : Submodule (ResidueField R) (CotangentSpace R) :=
  Submodule.span (ResidueField R)
    ((maximalIdeal R).toCotangent '' {x : maximalIdeal R | (x : R) ∈ I})

theorem toCotangent_mem_cotangentImage {I : Ideal R} (x : maximalIdeal R) (hx : (x : R) ∈ I) :
    (maximalIdeal R).toCotangent x ∈ cotangentImage R I :=
  Submodule.subset_span ⟨x, hx, rfl⟩

/-- An ideal strictly inside the maximal ideal has a proper image in the cotangent space
(Nakayama). -/
theorem cotangentImage_ne_top [IsNoetherianRing R] {I : Ideal R} (hI : I ≤ maximalIdeal R)
    (hne : I ≠ maximalIdeal R) : cotangentImage R I ≠ ⊤ := by
  intro htop
  rw [cotangentImage, IsLocalRing.CotangentSpace.span_image_eq_top_iff] at htop
  have hcomap : Submodule.comap (Submodule.subtype (maximalIdeal R)) I = ⊤ := by
    rw [← Submodule.span_eq (Submodule.comap (Submodule.subtype (maximalIdeal R)) I)]
    exact htop
  apply hne
  apply le_antisymm hI
  intro y hy
  have hmem : (⟨y, hy⟩ : maximalIdeal R) ∈
      Submodule.comap (Submodule.subtype (maximalIdeal R)) I := by
    rw [hcomap]
    exact Submodule.mem_top
  exact hmem

/-- The local form of the two-branches statement: with cotangent dimension two, two proper
branch ideals cannot share a nonzero cotangent class and contain the two members of an
independent pair. -/
theorem two_branches_local [IsNoetherianRing R]
    (h2 : Module.finrank (ResidueField R) (CotangentSpace R) = 2)
    (ID IE : Ideal R) (hD : ID ≤ maximalIdeal R) (hE : IE ≤ maximalIdeal R)
    (hDne : ID ≠ maximalIdeal R) (hEne : IE ≠ maximalIdeal R)
    (b c d : maximalIdeal R) (hbD : (b : R) ∈ ID) (hbE : (b : R) ∈ IE)
    (hb0 : (maximalIdeal R).toCotangent b ≠ 0) (hc : (c : R) ∈ ID) (hd : (d : R) ∈ IE)
    (hcd : LinearIndependent (ResidueField R)
      ![(maximalIdeal R).toCotangent c, (maximalIdeal R).toCotangent d]) : False :=
  two_branches_core h2 (cotangentImage R ID) (cotangentImage R IE)
    (cotangentImage_ne_top R hD hDne) (cotangentImage_ne_top R hE hEne) hb0
    (toCotangent_mem_cotangentImage R b hbD) (toCotangent_mem_cotangentImage R b hbE)
    (toCotangent_mem_cotangentImage R c hc) (toCotangent_mem_cotangentImage R d hd) hcd

end CotangentImage

section BranchIdeal

variable {Y : Scheme.{u}} [NoetherianSpace Y]

/-- Chart ideals are antitone in the selection of components. -/
theorem componentChartIdeal_anti {S T : Set ↥(irreducibleComponents Y)} (h : S ⊆ T)
    (U : Y.affineOpens) : componentChartIdeal Y T U ≤ componentChartIdeal Y S U := by
  rw [componentChartIdeal_eq, componentChartIdeal_eq]
  apply PrimeSpectrum.vanishingIdeal_anti_mono
  apply Set.preimage_mono
  intro x hx
  obtain ⟨C, hC, hxC⟩ := (mem_componentClosedUnion Y S x).mp hx
  exact (mem_componentClosedUnion Y T x).mpr ⟨C, h hC, hxC⟩

/-- The chart ideal of a component through `q`, in the stalk at `q`, lies in the maximal ideal. -/
theorem chartIdeal_map_germ_le_maximalIdeal (D : ↥(irreducibleComponents Y)) (q : Y)
    (hqD : q ∈ D.1) (U : Y.affineOpens) (hq : q ∈ U.1) :
    (componentChartIdeal Y {D} U).map (Y.presheaf.germ U.1 q hq).hom ≤
      maximalIdeal (Y.presheaf.stalk q) := by
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨q, hq⟩ : U.1)
  haveI := U.2.isLocalization_stalk ⟨q, hq⟩
  rw [Ideal.map_le_iff_le_comap]
  have hcomap : (maximalIdeal (Y.presheaf.stalk q)).comap (Y.presheaf.germ U.1 q hq).hom =
      (U.2.primeIdealOf ⟨q, hq⟩).asIdeal :=
    IsLocalization.AtPrime.comap_maximalIdeal _ _
  rw [hcomap]
  intro s hs
  rw [componentChartIdeal_eq] at hs
  refine (PrimeSpectrum.mem_vanishingIdeal _ _).mp hs _ ?_
  show U.2.fromSpec.base (U.2.primeIdealOf ⟨q, hq⟩) ∈ (componentClosedUnion Y {D} : Set Y)
  rw [U.2.fromSpec_primeIdealOf, coe_componentClosedUnion_singleton]
  exact hqD

/-- The chart ideal of a component `D` through `q`, in the stalk at `q`, is not the maximal ideal
when `q` lies on a second component: the generic point of `D` gives a strictly smaller prime. -/
theorem chartIdeal_map_germ_ne_maximalIdeal (D E : ↥(irreducibleComponents Y)) (hDE : D ≠ E)
    (q : Y) (hqD : q ∈ D.1) (hqE : q ∈ E.1) (U : Y.affineOpens) (hq : q ∈ U.1) :
    (componentChartIdeal Y {D} U).map (Y.presheaf.germ U.1 q hq).hom ≠
      maximalIdeal (Y.presheaf.stalk q) := by
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨q, hq⟩ : U.1)
  haveI := U.2.isLocalization_stalk ⟨q, hq⟩
  have hgen := D.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents D.1 D.2)
  have hηU : D.2.1.genericPoint ∈ U.1 := (hgen.mem_open_set_iff U.1.isOpen).mpr ⟨q, hqD, hq⟩
  have hηq : D.2.1.genericPoint ≠ q := by
    intro h
    have hDE' : D.1 ⊆ E.1 := by
      rw [← isGenericPoint_def.mp hgen]
      exact closure_minimal (Set.singleton_subset_iff.mpr (h ▸ hqE))
        (isClosed_of_mem_irreducibleComponents E.1 E.2)
    exact hDE (Subtype.ext (hDE'.antisymm (D.2.2 E.2.1 hDE')))
  have hle : U.2.primeIdealOf ⟨D.2.1.genericPoint, hηU⟩ ≤ U.2.primeIdealOf ⟨q, hq⟩ := by
    rw [PrimeSpectrum.le_iff_specializes,
      ← U.2.fromSpec.isOpenEmbedding.toIsEmbedding.isInducing.specializes_iff,
      U.2.fromSpec_primeIdealOf, U.2.fromSpec_primeIdealOf]
    exact hgen.specializes hqD
  have hne : U.2.primeIdealOf ⟨D.2.1.genericPoint, hηU⟩ ≠ U.2.primeIdealOf ⟨q, hq⟩ := by
    intro h
    apply hηq
    have := congrArg U.2.fromSpec.base h
    rwa [U.2.fromSpec_primeIdealOf, U.2.fromSpec_primeIdealOf] at this
  have hsub : componentChartIdeal Y {D} U ≤ (U.2.primeIdealOf ⟨D.2.1.genericPoint, hηU⟩).asIdeal := by
    intro s hs
    rw [componentChartIdeal_eq] at hs
    refine (PrimeSpectrum.mem_vanishingIdeal _ _).mp hs _ ?_
    show U.2.fromSpec.base (U.2.primeIdealOf ⟨D.2.1.genericPoint, hηU⟩) ∈
      (componentClosedUnion Y {D} : Set Y)
    rw [U.2.fromSpec_primeIdealOf, coe_componentClosedUnion_singleton]
    exact hgen.mem
  intro heq
  apply hne
  have hmapη : (U.2.primeIdealOf ⟨D.2.1.genericPoint, hηU⟩).asIdeal.map
      (algebraMap Γ(Y, U.1) (Y.presheaf.stalk q)) = maximalIdeal (Y.presheaf.stalk q) := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal
        (Ideal.isPrime_map_of_isLocalizationAtPrime (U.2.primeIdealOf ⟨q, hq⟩).asIdeal hle).ne_top
    · rw [← heq]
      exact Ideal.map_mono hsub
  have h1 := Ideal.under_map_of_isLocalizationAtPrime (S := Y.presheaf.stalk q)
    (U.2.primeIdealOf ⟨q, hq⟩).asIdeal hle
  rw [hmapη] at h1
  have h2 : (maximalIdeal (Y.presheaf.stalk q)).comap
      (algebraMap Γ(Y, U.1) (Y.presheaf.stalk q)) = (U.2.primeIdealOf ⟨q, hq⟩).asIdeal :=
    IsLocalization.AtPrime.comap_maximalIdeal _ _
  exact PrimeSpectrum.ext (h1.symm.trans h2)

/-- Under transverse branches, no point lies on three distinct components. -/
theorem not_three_components [IsLocallyNoetherian Y] (htrans : HasTransverseComponentBranches Y)
    (C D E : ↥(irreducibleComponents Y)) (hCD : C ≠ D) (hCE : C ≠ E) (hDE : D ≠ E) (q : Y)
    (hqC : q ∈ C.1) (hqD : q ∈ D.1) (hqE : q ∈ E.1) : False := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hqU, -⟩ :=
    (isBasis_affine_open Y).exists_subset_of_mem_open (Set.mem_univ q) isOpen_univ
  have hqCc : q ∈ (componentClosedUnion Y ({C}ᶜ) : Set Y) :=
    (mem_componentClosedUnion Y _ q).mpr ⟨D, fun h => hCD (Set.mem_singleton_iff.mp h).symm, hqD⟩
  have hqDc : q ∈ (componentClosedUnion Y ({D}ᶜ) : Set Y) :=
    (mem_componentClosedUnion Y _ q).mpr ⟨C, fun h => hCD (Set.mem_singleton_iff.mp h), hqC⟩
  obtain ⟨w, -, hw1, hdim, hind⟩ := htrans C q hqC hqCc ⟨U, hU⟩ hqU
  obtain ⟨v, hv0, hv1, -, hind'⟩ := htrans D q hqD hqDc ⟨U, hU⟩ hqU
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨q, hqU⟩ : U)
  haveI := (⟨U, hU⟩ : Y.affineOpens).2.isLocalization_stalk ⟨q, hqU⟩
  haveI : IsNoetherianRing (Y.presheaf.stalk q) :=
    IsLocalization.isNoetherianRing
      ((⟨U, hU⟩ : Y.affineOpens).2.primeIdealOf ⟨q, hqU⟩).asIdeal.primeCompl
      (Y.presheaf.stalk q) (IsLocallyNoetherian.component_noetherian ⟨U, hU⟩)
  have hCcD : componentChartIdeal Y ({C}ᶜ) ⟨U, hU⟩ ≤ componentChartIdeal Y {D} ⟨U, hU⟩ :=
    componentChartIdeal_anti (Set.singleton_subset_iff.mpr
      (show D ∈ ({C}ᶜ : Set ↥(irreducibleComponents Y)) from
        fun h => hCD (Set.mem_singleton_iff.mp h).symm)) _
  have hCcE : componentChartIdeal Y ({C}ᶜ) ⟨U, hU⟩ ≤ componentChartIdeal Y {E} ⟨U, hU⟩ :=
    componentChartIdeal_anti (Set.singleton_subset_iff.mpr
      (show E ∈ ({C}ᶜ : Set ↥(irreducibleComponents Y)) from
        fun h => hCE (Set.mem_singleton_iff.mp h).symm)) _
  have hDcE : componentChartIdeal Y ({D}ᶜ) ⟨U, hU⟩ ≤ componentChartIdeal Y {E} ⟨U, hU⟩ :=
    componentChartIdeal_anti (Set.singleton_subset_iff.mpr
      (show E ∈ ({D}ᶜ : Set ↥(irreducibleComponents Y)) from
        fun h => hDE (Set.mem_singleton_iff.mp h).symm)) _
  refine two_branches_local (Y.presheaf.stalk q) hdim
    ((componentChartIdeal Y {D} ⟨U, hU⟩).map (Y.presheaf.germ U q hqU).hom)
    ((componentChartIdeal Y {E} ⟨U, hU⟩).map (Y.presheaf.germ U q hqU).hom)
    (chartIdeal_map_germ_le_maximalIdeal D q hqD ⟨U, hU⟩ hqU)
    (chartIdeal_map_germ_le_maximalIdeal E q hqE ⟨U, hU⟩ hqU)
    (chartIdeal_map_germ_ne_maximalIdeal D C hCD.symm q hqD hqC ⟨U, hU⟩ hqU)
    (chartIdeal_map_germ_ne_maximalIdeal E C hCE.symm q hqE hqC ⟨U, hU⟩ hqU)
    (w 1) (v 0) (v 1) (Ideal.map_mono hCcD hw1) (Ideal.map_mono hCcE hw1) (hind.ne_zero 1) hv0
    (Ideal.map_mono hDcE hv1) ?_
  convert hind' using 1
  ext i
  fin_cases i <;> rfl

/-- Under transverse branches, a node of the complement of a leaf component never maps into the
leaf component: the leaf node is on exactly two components of `Y`. -/
theorem image_intersectionPoint_not_mem [IsLocallyNoetherian Y]
    (htrans : HasTransverseComponentBranches Y) (C : ↥(irreducibleComponents Y))
    (z : ↥(componentIntersectionPoints (componentUnionScheme Y ({C}ᶜ)))) :
    (componentUnionInclusion Y ({C}ᶜ)).base z.1 ∉ C.1 := by
  intro hzC
  obtain ⟨D', E', hne, hzD, hzE⟩ := z.2
  refine not_three_components htrans C (componentImage Y ({C}ᶜ) D') (componentImage Y ({C}ᶜ) E')
    (fun h => componentImage_mem Y ({C}ᶜ) D' (by rw [← h]; exact Set.mem_singleton C))
    (fun h => componentImage_mem Y ({C}ᶜ) E' (by rw [← h]; exact Set.mem_singleton C))
    (fun h => hne (componentImage_injective Y ({C}ᶜ) h)) _ hzC ?_ ?_
  · rw [← image_componentImage]
    exact ⟨z.1, hzD, rfl⟩
  · rw [← image_componentImage]
    exact ⟨z.1, hzE, rfl⟩

end BranchIdeal

end KltDP.Geometry.RationalTreePicard
