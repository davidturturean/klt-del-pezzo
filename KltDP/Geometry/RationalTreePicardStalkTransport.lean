import KltDP.Geometry.RationalTreePicardCotangentTransport

/-!
# The stalk transport of the transverse data, and the unconditional kernel statement

BRIEF13. (iii) The ideal of an ideal sheaf at a stalk does not depend on the affine chart
(`ideal_map_germ_eq`, quasi-coherence through `IdealSheafData.map_ideal` and
`exists_basicOpen_le_affine_inter`); the chart ideal of a selection of components of `Y` maps,
under the section map of `ι_S`, into the chart ideal of the corresponding selection of components of
`Z_S` (`chartIdeal_map_app_le`, via the compatibility `Spec_map_appLE_fromSpec` of the affine charts
and `image_componentImage`), hence at the stalks (`stalkMap_chartIdeal_le`, `Scheme.stalkMap_germ`).
With the stalk isomorphism off the leaf (`isIso_stalkMap_componentUnionInclusion_compl`) and the
cotangent transport (`cotangent_transfer`) this proves `TransversePointTransfer Y C` for every reduced
Noetherian `Y` (`transversePointTransfer`), hence `InheritsTransverseBranches` and
`InheritsLeafHypotheses` unconditionally, and the kernel statement of `lem:tree-picard`:
`rationalTreePicard_trivial_of_exponents_zero_final`, `multidegreeHom_injective_final`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.RationalTreePicard

section ChartIndependence

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Restricting to a smaller affine open does not change the ideal at the stalk. -/
theorem ideal_map_germ_eq_of_le {U V : X.affineOpens} (h : V ≤ U) (x : X) (hxV : x ∈ V.1) :
    (I.ideal U).map (X.presheaf.germ U.1 x (h hxV)).hom =
      (I.ideal V).map (X.presheaf.germ V.1 x hxV).hom := by
  rw [← I.map_ideal h, Ideal.map_map, ← CommRingCat.hom_comp]
  erw [TopCat.Presheaf.germ_res']

/-- The ideal of an ideal sheaf at a stalk is independent of the affine chart. -/
theorem ideal_map_germ_eq {U W : X.affineOpens} (x : X) (hxU : x ∈ U.1) (hxW : x ∈ W.1) :
    (I.ideal U).map (X.presheaf.germ U.1 x hxU).hom =
      (I.ideal W).map (X.presheaf.germ W.1 x hxW).hom := by
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 W.2 x ⟨hxU, hxW⟩
  have hfU : X.affineBasicOpen f ≤ U := X.basicOpen_le f
  have hfW : X.affineBasicOpen f ≤ W := by
    show X.basicOpen f ≤ W.1
    rw [hfg]
    exact X.basicOpen_le g
  rw [ideal_map_germ_eq_of_le I hfU x hxf, ideal_map_germ_eq_of_le I hfW x hxf]

end ChartIndependence

section ChartTransfer

variable (Y : Scheme.{u}) [NoetherianSpace Y] (S : Set ↥(irreducibleComponents Y))

/-- The preimage of an affine open under the closed immersion of a component union is affine. -/
theorem isAffineOpen_preimage_componentUnionInclusion (U : Y.affineOpens) :
    IsAffineOpen (componentUnionInclusion Y S ⁻¹ᵁ U.1) := by
  haveI : IsAffine U.1.toScheme := U.2
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine (componentUnionInclusion Y S ∣_ U.1)).1

/-- The affine charts of `Y` and of the closed union are compatible with the inclusion. -/
theorem fromSpec_comap_app (U : Y.affineOpens)
    (p : PrimeSpectrum Γ(componentUnionScheme Y S, componentUnionInclusion Y S ⁻¹ᵁ U.1)) :
    U.2.fromSpec.base (PrimeSpectrum.comap ((componentUnionInclusion Y S).app U.1).hom p) =
      (componentUnionInclusion Y S).base
        ((isAffineOpen_preimage_componentUnionInclusion Y S U).fromSpec.base p) := by
  have h := IsAffineOpen.Spec_map_appLE_fromSpec (componentUnionInclusion Y S) U.2
    (isAffineOpen_preimage_componentUnionInclusion Y S U) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at h
  have := congrArg (fun m => m.base p) h
  simp only [Scheme.comp_base_apply, Spec.map_base_apply] at this
  exact this

/-- The chart ideal of a selection of original components maps into the chart ideal of a
selection of components of the closed union whose images lie in the original selection. -/
theorem chartIdeal_map_app_le (S' : Set ↥(irreducibleComponents (componentUnionScheme Y S)))
    (T : Set ↥(irreducibleComponents Y)) (hST : ∀ D' ∈ S', componentImage Y S D' ∈ T)
    (U : Y.affineOpens) :
    (componentChartIdeal Y T U).map ((componentUnionInclusion Y S).app U.1).hom ≤
      componentChartIdeal (componentUnionScheme Y S) S'
        ⟨_, isAffineOpen_preimage_componentUnionInclusion Y S U⟩ := by
  rw [Ideal.map_le_iff_le_comap]
  intro s hs
  rw [Ideal.mem_comap, componentChartIdeal_eq]
  refine (PrimeSpectrum.mem_vanishingIdeal _ _).mpr fun p hp => ?_
  rw [componentChartIdeal_eq] at hs
  have hmem : PrimeSpectrum.comap ((componentUnionInclusion Y S).app U.1).hom p ∈
      U.2.fromSpec.base ⁻¹' (componentClosedUnion Y T : Set Y) := by
    show U.2.fromSpec.base (PrimeSpectrum.comap ((componentUnionInclusion Y S).app U.1).hom p) ∈
      (componentClosedUnion Y T : Set Y)
    rw [fromSpec_comap_app]
    obtain ⟨D', hD', hz⟩ := (mem_componentClosedUnion (componentUnionScheme Y S) S' _).mp hp
    refine (mem_componentClosedUnion Y T _).mpr ⟨componentImage Y S D', hST D' hD', ?_⟩
    rw [← image_componentImage]
    exact ⟨_, hz, rfl⟩
  exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hs _ hmem

/-- The chart-ideal condition at the stalk transfers along the closed immersion. -/
theorem stalkMap_chartIdeal_le (S' : Set ↥(irreducibleComponents (componentUnionScheme Y S)))
    (T : Set ↥(irreducibleComponents Y)) (hST : ∀ D' ∈ S', componentImage Y S D' ∈ T)
    (z : componentUnionScheme Y S) (U : Y.affineOpens)
    (hxU : (componentUnionInclusion Y S).base z ∈ U.1)
    (V : (componentUnionScheme Y S).affineOpens) (hzV : z ∈ V.1) :
    ((componentChartIdeal Y T U).map
        (Y.presheaf.germ U.1 ((componentUnionInclusion Y S).base z) hxU).hom).map
        ((componentUnionInclusion Y S).stalkMap z).hom ≤
      (componentChartIdeal (componentUnionScheme Y S) S' V).map
        ((componentUnionScheme Y S).presheaf.germ V.1 z hzV).hom := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.stalkMap_germ, CommRingCat.hom_comp,
    ← Ideal.map_map]
  refine le_trans (Ideal.map_mono (chartIdeal_map_app_le Y S S' T hST U)) ?_
  exact (ideal_map_germ_eq (componentUnionIdeal (componentUnionScheme Y S) S')
    (U := ⟨_, isAffineOpen_preimage_componentUnionInclusion Y S U⟩) (W := V) z hxU hzV).le

end ChartTransfer

section Transfer

variable (Y : Scheme.{u}) [NoetherianSpace Y] [AlgebraicGeometry.IsReduced Y]
  (C : ↥(irreducibleComponents Y))

/-- The stalk transport of the transverse data off the leaf component. -/
theorem transversePointTransfer : TransversePointTransfer Y C := by
  intro D' z hxC hY V hz
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := (isBasis_affine_open Y).exists_subset_of_mem_open
    (Set.mem_univ ((componentUnionInclusion Y ({C}ᶜ)).base z)) isOpen_univ
  obtain ⟨w, hw0, hw1, hdim, hind⟩ := hY ⟨U, hU⟩ hxU
  haveI := isIso_stalkMap_componentUnionInclusion_compl Y C z hxC
  let e : Y.presheaf.stalk ((componentUnionInclusion Y ({C}ᶜ)).base z) ≃+*
      (componentUnionScheme Y ({C}ᶜ)).presheaf.stalk z :=
    (asIso ((componentUnionInclusion Y ({C}ᶜ)).stalkMap z)).commRingCatIsoToRingEquiv
  obtain ⟨hdim', hind'⟩ := cotangent_transfer e hdim w hind
  refine ⟨fun i => ⟨e (w i), (mem_maximalIdeal_map_iff e (w i)).mpr (w i).2⟩, ?_, ?_, hdim', hind'⟩
  · refine stalkMap_chartIdeal_le Y ({C}ᶜ) {D'} {componentImage Y ({C}ᶜ) D'} ?_ z ⟨U, hU⟩ hxU V hz
      (Ideal.mem_map_of_mem _ hw0)
    intro D'' hD''
    rw [Set.mem_singleton_iff] at hD''
    rw [hD'']
    exact Set.mem_singleton _
  · refine stalkMap_chartIdeal_le Y ({C}ᶜ) ({D'}ᶜ) ({componentImage Y ({C}ᶜ) D'}ᶜ) ?_ z ⟨U, hU⟩
      hxU V hz (Ideal.mem_map_of_mem _ hw1)
    intro D'' hD'' h
    apply hD''
    rw [Set.mem_singleton_iff] at h ⊢
    exact componentImage_injective Y ({C}ᶜ) h

end Transfer

section Final

/-- The transverse germs are inherited by the complement of a leaf: unconditional. -/
theorem inheritsTransverseBranches : InheritsTransverseBranches.{u} := by
  intro Y _ _ _ C q _ _ _ htransY
  exact hasTransverseComponentBranches_compl_of_transfer htransY (transversePointTransfer Y C)

/-- All standing hypotheses are inherited by the complement of a leaf: unconditional. -/
theorem inheritsLeafHypotheses : InheritsLeafHypotheses.{u} :=
  inheritsLeafHypotheses_of_transverse inheritsTransverseBranches

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The kernel statement of `lem:tree-picard`, unconditional: on a reduced Noetherian curve over
an algebraically closed field with tree component-point incidence graph and transverse branch
germs, every line bundle with zero component exponent on every component (each identified with
the projective line) is trivial. -/
theorem rationalTreePicard_trivial_of_exponents_zero_final (X : Scheme.{u}) [NoetherianSpace X]
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (htrans : HasTransverseComponentBranches X) : ExponentsZeroTrivial k X :=
  rationalTreePicard_trivial_of_exponents_zero'' k inheritsTransverseBranches _ X f rfl hdim hTree
    htrans

/-- The kernel half of `lem:tree-picard`, unconditional: the multidegree homomorphism is
injective. -/
theorem multidegreeHom_injective_final (X : Scheme.{u}) [NoetherianSpace X]
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (htrans : HasTransverseComponentBranches X)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1) :
    Function.Injective (multidegreeHom k X e) :=
  multidegreeHom_injective_of_transverse k inheritsTransverseBranches X f hdim hTree htrans e

end Final

end KltDP.Geometry.RationalTreePicard
