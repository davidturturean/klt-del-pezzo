import KltDP.Geometry.TransverseBranchesCotangentQuotient
import KltDP.Geometry.RationalTreePicardStalkTransport

/-!
# Transverse branches from a transversal configuration of curves in a surface

BRIEF18, task 1 (geometric part). Let `ι : X ⟶ S` be a closed immersion of a Noetherian scheme
`X` (the configuration) into a scheme `S` (the surface). Two irreducible components `C ≠ D` of
`X` *cross transversally* at `q ∈ C ∩ D` (`TransversalCrossing ι C D q`) when the local ring
`O_{S, ι q}` is regular of Krull dimension two (the project's `RegularLocal` predicate) and there
are local equations `f, g ∈ O_{S, ι q}` of `C`, `D` at `q`: they generate the maximal ideal of
`O_{S, ι q}`, the kernel of the (surjective) stalk map `ι♯_q : O_{S, ι q} → O_{X, q}` is `(f g)`
(so `O_{X, q} = O_{S, ι q} ⧸ (f g)`), and the images of `f`, `g` in `O_{X, q}` lie in the stalk
ideals of `C`, `D` (the chart ideals of the reduced components, extended to the stalk). A
*transversal configuration* (`TransversalConfiguration ι`) is one in which no point lies on
three components and any two components cross transversally at each common point.

Main result: `hasTransverseComponentBranches_of_transversalConfiguration` — a transversal
configuration has transverse component branches in the sense of the lane's
`HasTransverseComponentBranches X`, the nodality hypothesis of `lem:tree-picard`
(`KltDP.Manuscript.S02.rationalTreePicard`). The branch germs are `ι♯_q f`, `ι♯_q g`; the cotangent
space of `O_{X, q} = O_{S, ι q} ⧸ (f g)` is that of `O_{S, ι q}` (the kernel lies in `m²`), so it is
two-dimensional with the two classes independent (`transverse_of_crossing_quotient`); the germ
`ι♯_q g` lies in the stalk ideal of the complementary union `Z_{Cᶜ}` because, under the
no-triple-point hypothesis, `Z_{Cᶜ}` coincides with `D` near `q`
(`exists_affine_chartIdeal_compl_eq`, `chartIdeal_compl_map_germ_eq`, through the chart
independence `ideal_map_germ_eq` of the stalk ideal).

The identification of the components of `X` with given curves, and the corollary of
`rationalTreePicard` for a configuration of projective lines, are in
`KltDP/Geometry/RationalTreePicardOfConfiguration.lean`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.RationalTreePicard

variable {X : Scheme.{u}} [NoetherianSpace X]

section LocalIdeal

/-- On a small enough affine chart through a point lying only on the components `C ≠ D`, the
chart ideal of the complementary union `Z_{Cᶜ}` is the chart ideal of `D`. -/
theorem exists_affine_chartIdeal_compl_eq (C D : ↥(irreducibleComponents X)) (hCD : C ≠ D)
    (q : X) (hno : ∀ E : ↥(irreducibleComponents X), q ∈ E.1 → E = C ∨ E = D)
    (U : X.affineOpens) (hq : q ∈ U.1) :
    ∃ (W : X.affineOpens) (_ : q ∈ W.1), W ≤ U ∧
      componentChartIdeal X ({C}ᶜ) W = componentChartIdeal X {D} W := by
  classical
  haveI : Finite ↥(irreducibleComponents X) := by
    rw [Set.finite_coe_iff]
    exact NoetherianSpace.finite_irreducibleComponents
  let K : Set X := ⋃ E ∈ ({C, D}ᶜ : Set ↥(irreducibleComponents X)), E.1
  have hK : IsClosed K :=
    (Set.toFinite _).isClosed_biUnion
      (fun E _ => isClosed_of_mem_irreducibleComponents E.1 E.2)
  have hqK : q ∉ K := by
    intro hqK
    obtain ⟨E, hE, hqE⟩ := Set.mem_iUnion₂.mp hqK
    rcases hno E hqE with rfl | rfl
    · exact hE (Set.mem_insert _ _)
    · exact hE (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hopen : IsOpen ((U.1 : Set X) ∩ Kᶜ) := U.1.isOpen.inter hK.isOpen_compl
  obtain ⟨_, ⟨W, hW, rfl⟩, hqW, hWsub⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open (⟨hq, hqK⟩ : q ∈ (U.1 : Set X) ∩ Kᶜ) hopen
  refine ⟨⟨W, hW⟩, hqW, fun x hx => (hWsub hx).1, ?_⟩
  rw [componentChartIdeal_eq, componentChartIdeal_eq, coe_componentClosedUnion_singleton]
  congr 1
  ext p
  have hpW : hW.fromSpec.base p ∈ (W : Set X) := by
    rw [← hW.range_fromSpec]
    exact Set.mem_range_self p
  simp only [Set.mem_preimage]
  constructor
  · intro hp
    obtain ⟨E, hE, hpE⟩ := (mem_componentClosedUnion X _ _).mp hp
    by_cases hED : E = D
    · rw [hED] at hpE
      exact hpE
    · exfalso
      have hEC : E ≠ C := fun h => hE (Set.mem_singleton_iff.mpr h)
      have hpK : hW.fromSpec.base p ∈ K :=
        Set.mem_iUnion₂.mpr ⟨E, fun h => by
          rcases h with h | h
          · exact hEC h
          · exact hED (Set.mem_singleton_iff.mp h), hpE⟩
      exact (hWsub hpW).2 hpK
  · intro hp
    have hDC : D ∈ ({C}ᶜ : Set ↥(irreducibleComponents X)) :=
      fun h => hCD (Set.mem_singleton_iff.mp h).symm
    exact (mem_componentClosedUnion X _ _).mpr ⟨D, hDC, hp⟩

/-- Under the no-triple-point hypothesis, the stalk ideal of the complementary union `Z_{Cᶜ}` at
a point of `C ∩ D` is the stalk ideal of `D` (on every affine chart). -/
theorem chartIdeal_compl_map_germ_eq (C D : ↥(irreducibleComponents X)) (hCD : C ≠ D) (q : X)
    (hno : ∀ E : ↥(irreducibleComponents X), q ∈ E.1 → E = C ∨ E = D)
    (U : X.affineOpens) (hq : q ∈ U.1) :
    (componentChartIdeal X ({C}ᶜ) U).map (X.presheaf.germ U.1 q hq).hom =
      (componentChartIdeal X {D} U).map (X.presheaf.germ U.1 q hq).hom := by
  obtain ⟨W, hqW, -, hWeq⟩ := exists_affine_chartIdeal_compl_eq C D hCD q hno U hq
  have h1 := ideal_map_germ_eq (componentUnionIdeal X ({C}ᶜ)) q hq hqW
  have h2 := ideal_map_germ_eq (componentUnionIdeal X {D}) q hq hqW
  exact h1.trans ((congrArg (Ideal.map (X.presheaf.germ W.1 q hqW).hom) hWeq).trans h2.symm)

/-- Membership in the stalk ideal of a selection of components can be checked on one affine
chart: it then holds on every affine chart through the point (chart independence
`ideal_map_germ_eq`). -/
theorem mem_chartIdeal_map_germ_of_chart (S' : Set ↥(irreducibleComponents X)) {q : X}
    {U : X.affineOpens} (hqU : q ∈ U.1) {a : X.presheaf.stalk q}
    (ha : a ∈ (componentChartIdeal X S' U).map (X.presheaf.germ U.1 q hqU).hom)
    (W : X.affineOpens) (hqW : q ∈ W.1) :
    a ∈ (componentChartIdeal X S' W).map (X.presheaf.germ W.1 q hqW).hom := by
  have h : (componentChartIdeal X S' U).map (X.presheaf.germ U.1 q hqU).hom =
      (componentChartIdeal X S' W).map (X.presheaf.germ W.1 q hqW).hom :=
    ideal_map_germ_eq (componentUnionIdeal X S') q hqU hqW
  rw [← h]
  exact ha

end LocalIdeal

section Configuration

variable {S : Scheme.{u}} (ι : X ⟶ S)

/-- Transversal crossing of the components `C`, `D` of the closed subscheme `ι : X ⟶ S` at the
point `q ∈ C ∩ D`, in stalk form: the local ring `O_{S, ι q}` is regular of Krull dimension two,
and there are local equations `f`, `g` of `C`, `D` at `q`: germs generating the maximal ideal of
`O_{S, ι q}`, with `O_{X, q} = O_{S, ι q} ⧸ (f g)` (the kernel of the stalk map `ι♯_q` is `(f g)`)
and `ι♯_q f`, `ι♯_q g` in the stalk ideals of `C`, `D`. -/
structure TransversalCrossing (C D : ↥(irreducibleComponents X)) (q : X) : Prop where
  regular : RegularLocal (S.presheaf.stalk (ι.base q))
  dim_eq : ringKrullDim (S.presheaf.stalk (ι.base q)) = 2
  exists_equations : ∃ f g : S.presheaf.stalk (ι.base q),
    Ideal.span {f, g} = maximalIdeal (S.presheaf.stalk (ι.base q)) ∧
    RingHom.ker (ι.stalkMap q).hom = Ideal.span {f * g} ∧
    (∀ (U : X.affineOpens) (hq : q ∈ U.1),
      (ι.stalkMap q).hom f ∈
        (componentChartIdeal X {C} U).map (X.presheaf.germ U.1 q hq).hom) ∧
    (∀ (U : X.affineOpens) (hq : q ∈ U.1),
      (ι.stalkMap q).hom g ∈
        (componentChartIdeal X {D} U).map (X.presheaf.germ U.1 q hq).hom)

/-- Transversal crossing from data on a single affine chart `U` through `q`: the chart-ideal
conditions on `U` give them on every affine chart. -/
theorem TransversalCrossing.ofChart (C D : ↥(irreducibleComponents X)) (q : X)
    (hreg : RegularLocal (S.presheaf.stalk (ι.base q)))
    (hdim : ringKrullDim (S.presheaf.stalk (ι.base q)) = 2)
    (f g : S.presheaf.stalk (ι.base q))
    (hspan : Ideal.span {f, g} = maximalIdeal (S.presheaf.stalk (ι.base q)))
    (hker : RingHom.ker (ι.stalkMap q).hom = Ideal.span {f * g})
    (U : X.affineOpens) (hq : q ∈ U.1)
    (hf : (ι.stalkMap q).hom f ∈
      (componentChartIdeal X {C} U).map (X.presheaf.germ U.1 q hq).hom)
    (hg : (ι.stalkMap q).hom g ∈
      (componentChartIdeal X {D} U).map (X.presheaf.germ U.1 q hq).hom) :
    TransversalCrossing ι C D q where
  regular := hreg
  dim_eq := hdim
  exists_equations := ⟨f, g, hspan, hker,
    fun W hqW => mem_chartIdeal_map_germ_of_chart {C} hq hf W hqW,
    fun W hqW => mem_chartIdeal_map_germ_of_chart {D} hq hg W hqW⟩

/-- A transversal configuration: no point of `X` lies on three irreducible components, and any
two components cross transversally (in `S`) at each of their common points. -/
structure TransversalConfiguration : Prop where
  no_triple : ∀ (C D E : ↥(irreducibleComponents X)) (q : X),
    q ∈ C.1 → q ∈ D.1 → q ∈ E.1 → C = D ∨ C = E ∨ D = E
  crossing : ∀ (C D : ↥(irreducibleComponents X)), C ≠ D →
    ∀ q : X, q ∈ C.1 → q ∈ D.1 → TransversalCrossing ι C D q

/-- A transversal configuration of curves in a surface has transverse component branches: at
every point where a component `C` meets the other components, on every affine chart, the germs
`ι♯_q f`, `ι♯_q g` of the local equations lie in the stalk ideals of `C` and of `Z_{Cᶜ}`, and their
classes are independent in the two-dimensional cotangent space of `O_{X, q}`. -/
theorem hasTransverseComponentBranches_of_transversalConfiguration [IsClosedImmersion ι]
    (h : TransversalConfiguration ι) : HasTransverseComponentBranches X := by
  intro C q hqC hqCc U hq
  obtain ⟨D, hD, hqD⟩ := (mem_componentClosedUnion X _ q).mp hqCc
  have hCD : C ≠ D := fun hCD => hD (Set.mem_singleton_iff.mpr hCD.symm)
  have hno : ∀ E : ↥(irreducibleComponents X), q ∈ E.1 → E = C ∨ E = D := by
    intro E hqE
    rcases h.no_triple C D E q hqC hqD hqE with hCD' | hCE | hDE
    · exact absurd hCD' hCD
    · exact Or.inl hCE.symm
    · exact Or.inr hDE.symm
  obtain ⟨hreg, hdim, f, g, hspan, hker, hfC, hgD⟩ := h.crossing C D hCD q hqC hqD
  have hφ : Function.Surjective (ι.stalkMap q).hom := ι.stalkMap_surjective q
  have hf : f ∈ maximalIdeal (S.presheaf.stalk (ι.base q)) := by
    rw [← hspan]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hg : g ∈ maximalIdeal (S.presheaf.stalk (ι.base q)) := by
    rw [← hspan]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  let w : Fin 2 → maximalIdeal (S.presheaf.stalk (ι.base q)) := ![⟨f, hf⟩, ⟨g, hg⟩]
  have h2 := finrank_cotangentSpace_eq_two_of_regularLocal hreg hdim
  obtain ⟨hfin, hind⟩ := transverse_of_crossing_quotient (ι.stalkMap q).hom hφ h2 w hspan hker
  refine ⟨fun i => ⟨(ι.stalkMap q).hom (w i), map_nonunit (ι.stalkMap q).hom (w i) (w i).2⟩,
    ?_, ?_, hfin, hind⟩
  · exact hfC U hq
  · rw [chartIdeal_compl_map_germ_eq C D hCD q hno U hq]
    exact hgD U hq

end Configuration

end KltDP.Geometry.RationalTreePicard
