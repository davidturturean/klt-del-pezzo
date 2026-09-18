import KltDP.Geometry.TransversalClosedPrimeUnionLocal

/-!
# Original prime-curve unions are transversal configurations

For a finite injective family of original prime curves in a regular
projective surface, the actual reduced closed union is a transversal
configuration if no three curves meet and the original pairwise germ
ideals generate the maximal ideal at common points. The curve lifts are
used only through their actual triangles with the original inclusions.
Their closedness, coverage, component identification, product stalk
kernel, and component-germ membership are all derived.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.TransversalClosedPrimeUnion

open NormalProjectiveSurface RationalTreePicard

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k)
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
    {I : Type u} [Fintype I] (C : I → S.PrimeCurve)
    {Z : Scheme.{u}} [NoetherianSpace Z] [AlgebraicGeometry.IsReduced Z]
    (ι : Z ⟶ S.toScheme) [IsClosedImmersion ι]
    (c : ∀ i, (C i).toScheme ⟶ Z)
    (htri : ∀ i, c i ≫ ι = (C i).inclusion)

include htri in
/-- Every actual curve lift is a closed immersion, since its composite
with the original union inclusion is the original prime inclusion. -/
theorem curveLift_isClosedImmersion (i : I) : IsClosedImmersion (c i) := by
  haveI : IsClosedImmersion (c i ≫ ι) := by
    rw [htri i]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion (c i) ι

include htri in
/-- Membership in a lifted curve is exactly membership of the original
ambient point in the original prime curve. -/
theorem mem_curve_range_iff (i : I) (q : Z) :
    q ∈ Set.range (c i).base ↔ ι.base q ∈ C i := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Scheme.comp_base_apply, htri i]
    exact (C i).inclusion_base_mem y
  · intro hq
    change ι.base q ∈ (C i : Set S.toScheme) at hq
    rw [← (C i).range_inclusion] at hq
    obtain ⟨y, hy⟩ := hq
    refine ⟨y, ι.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.comp_base_apply, htri i]
    exact hy

include htri in
/-- The lifted original curves cover the actual union. -/
theorem curveLift_cover
    (hrange : Set.range ι.base = ⋃ i, (C i : Set S.toScheme)) :
    ⋃ i, Set.range (c i).base = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  have hq : ι.base q ∈ ⋃ i, (C i : Set S.toScheme) := by
    rw [← hrange]
    exact Set.mem_range_self q
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hq
  exact Set.mem_iUnion.mpr ⟨i, (mem_curve_range_iff S C ι c htri i q).mpr hi⟩

include htri in
/-- Inclusion between the ranges of distinct original prime-curve lifts
forces equality of indices. -/
theorem curveLift_incomparable (hinj : Function.Injective C) (i j : I)
    (hsub : Set.range (c i).base ⊆ Set.range (c j).base) : i = j := by
  apply hinj
  apply PrimeCurve.ext
  apply (C i).coe_eq_of_subset_irreducibleCloseds (C j).1 _ (C j).ne_univ
  intro x hx
  change x ∈ (C i : Set S.toScheme) at hx
  rw [← (C i).range_inclusion] at hx
  obtain ⟨y, rfl⟩ := hx
  have hy := (mem_curve_range_iff S C ι c htri j ((c i).base y)).mp
    (hsub (Set.mem_range_self y))
  rwa [← Scheme.comp_base_apply, htri i] at hy

include hregular htri in
/-- At every original transverse double point, the two corresponding
components of the actual reduced union satisfy the full crossing
definition, including the original product stalk kernel. -/
theorem transversalCrossing_of_original_primes
    (hrange : Set.range ι.base = ⋃ i, (C i : Set S.toScheme))
    (a b : I) (hab : C a ≠ C b)
    (A B : ↥(irreducibleComponents Z))
    (hA : A.1 = Set.range (c a).base) (hB : B.1 = Set.range (c b).base)
    (q : Z) (hqA : q ∈ A.1) (hqB : q ∈ B.1)
    (hno : ∀ i, ι.base q ∈ C i → i = a ∨ i = b)
    (hcross : ∀ (U : S.toScheme.affineOpens) (hqU : ι.base q ∈ U.1),
      ((C a).vanishingIdeal.ideal U).map
          (S.toScheme.presheaf.germ U.1 (ι.base q) hqU).hom ⊔
        ((C b).vanishingIdeal.ideal U).map
          (S.toScheme.presheaf.germ U.1 (ι.base q) hqU).hom =
        maximalIdeal (S.toScheme.presheaf.stalk (ι.base q))) :
    TransversalCrossing ι A B q := by
  letI : ∀ i, IsClosedImmersion (c i) := curveLift_isClosedImmersion S C ι c htri
  have hqa : ι.base q ∈ C a :=
    (mem_curve_range_iff S C ι c htri a q).mp (hA ▸ hqA)
  have hqb : ι.base q ∈ C b :=
    (mem_curve_range_iff S C ι c htri b q).mp (hB ▸ hqB)
  obtain ⟨_, ⟨U, hU, rfl⟩, hqU, -⟩ :=
    (isBasis_affine_open S.toScheme).exists_subset_of_mem_open
      (Set.mem_univ (ι.base q)) isOpen_univ
  let V : S.toScheme.affineOpens := ⟨U, hU⟩
  obtain ⟨ca, hqca⟩ := S.primeCurveCartier_hasRegularEquations hregular (C a) (ι.base q)
  obtain ⟨cb, hqcb⟩ := S.primeCurveCartier_hasRegularEquations hregular (C b) (ι.base q)
  let f := S.toScheme.presheaf.germ ca.chart.openSet (ι.base q) hqca ca.coefficient
  let g := S.toScheme.presheaf.germ cb.chart.openSet (ι.base q) hqcb cb.coefficient
  have hf : ((C a).vanishingIdeal.ideal V).map
      (S.toScheme.presheaf.germ V.1 (ι.base q) hqU).hom = Ideal.span {f} :=
    PrimeCurveCrossingCoefficient.vanishingIdeal_map_germ_eq_span_coefficient
      S hregular (C a) V (ι.base q) hqU ca hqca
  have hg : ((C b).vanishingIdeal.ideal V).map
      (S.toScheme.presheaf.germ V.1 (ι.base q) hqU).hom = Ideal.span {g} :=
    PrimeCurveCrossingCoefficient.vanishingIdeal_map_germ_eq_span_coefficient
      S hregular (C b) V (ι.base q) hqU cb hqcb
  have hspan : Ideal.span {f, g} = maximalIdeal (S.toScheme.presheaf.stalk (ι.base q)) := by
    rw [Ideal.span_insert, ← hf, ← hg]
    exact hcross V hqU
  have hdim := crossing_stalk_dimension_two S hregular (C a) (C b) hab (ι.base q) hqa hqb
  have hreg := hregular (ι.base q)
  have hprime : (Ideal.span {g}).IsPrime := by
    rw [← hg]
    exact prime_germ_isPrime S (C b) V (ι.base q) hqU hqb
  refine ⟨hreg, hdim, f, g, hspan, ?_, ?_, ?_⟩
  · rw [stalk_ker_eq_inf_prime S hregular C ι hrange a b q V hqU hno, hf, hg]
    exact span_singleton_inf_span_singleton_of_prime hprime
      (first_parameter_not_mem_second hreg hdim f g hspan)
  · intro W hqW
    apply map_stalk_ker_le_component ι (c a) A hA q V hqU W hqW
    apply Ideal.mem_map_of_mem
    have hker : (c a ≫ ι).ker = (C a).vanishingIdeal := by
      rw [htri a]
      exact (C a).vanishingIdeal.ker_gluedTo
    rw [hker, hf]
    exact Ideal.subset_span (Set.mem_singleton f)
  · intro W hqW
    apply map_stalk_ker_le_component ι (c b) B hB q V hqU W hqW
    apply Ideal.mem_map_of_mem
    have hker : (c b ≫ ι).ker = (C b).vanishingIdeal := by
      rw [htri b]
      exact (C b).vanishingIdeal.ker_gluedTo
    rw [hker, hg]
    exact Ideal.subset_span (Set.mem_singleton g)

include hregular htri in
/-- A finite reduced closed union of original prime curves is a
transversal configuration under the original no-triple-point and
pairwise germ-ideal hypotheses. All local equations and ideal-kernel
comparisons in the conclusion are proved. -/
theorem transversalConfiguration_of_original_primes
    (hinj : Function.Injective C)
    (hrange : Set.range ι.base = ⋃ i, (C i : Set S.toScheme))
    (hno : ∀ (a b d : I) (x : S.toScheme),
      x ∈ C a → x ∈ C b → x ∈ C d → a = b ∨ a = d ∨ b = d)
    (hcross : ∀ (a b : I), a ≠ b → ∀ (x : S.toScheme),
      x ∈ C a → x ∈ C b → ∀ (U : S.toScheme.affineOpens) (hxU : x ∈ U.1),
      ((C a).vanishingIdeal.ideal U).map (S.toScheme.presheaf.germ U.1 x hxU).hom ⊔
        ((C b).vanishingIdeal.ideal U).map (S.toScheme.presheaf.germ U.1 x hxU).hom =
        maximalIdeal (S.toScheme.presheaf.stalk x)) :
    TransversalConfiguration ι := by
  letI : ∀ i, IsClosedImmersion (c i) := curveLift_isClosedImmersion S C ι c htri
  let Cv : I → Scheme.{u} := fun i => (C i).toScheme
  have hint : ∀ i, IsIntegral (Cv i) := fun _ => inferInstance
  have hcover := curveLift_cover S C ι c htri hrange
  have hdistinct := curveLift_incomparable S C ι c htri hinj
  let e : I ≃ ↥(irreducibleComponents Z) :=
    curveComponentEquiv Z Cv c hint hcover hdistinct
  have he : ∀ i, (e i).1 = Set.range (c i).base := fun _ => rfl
  constructor
  · intro A B E q hqA hqB hqE
    obtain ⟨a, rfl⟩ := e.surjective A
    obtain ⟨b, rfl⟩ := e.surjective B
    obtain ⟨d, rfl⟩ := e.surjective E
    have ha := (mem_curve_range_iff S C ι c htri a q).mp ((he a) ▸ hqA)
    have hb := (mem_curve_range_iff S C ι c htri b q).mp ((he b) ▸ hqB)
    have hd := (mem_curve_range_iff S C ι c htri d q).mp ((he d) ▸ hqE)
    rcases hno a b d (ι.base q) ha hb hd with hab | had | hbd
    · exact Or.inl (congrArg e hab)
    · exact Or.inr (Or.inl (congrArg e had))
    · exact Or.inr (Or.inr (congrArg e hbd))
  · intro A B hAB q hqA hqB
    obtain ⟨a, rfl⟩ := e.surjective A
    obtain ⟨b, rfl⟩ := e.surjective B
    have hab : a ≠ b := fun h => hAB (congrArg e h)
    have ha := (mem_curve_range_iff S C ι c htri a q).mp ((he a) ▸ hqA)
    have hb := (mem_curve_range_iff S C ι c htri b q).mp ((he b) ▸ hqB)
    refine transversalCrossing_of_original_primes S hregular C ι c htri hrange a b
      (fun h => hab (hinj h)) (e a) (e b) (he a) (he b) q hqA hqB ?_
      (hcross a b hab (ι.base q) ha hb)
    intro d hd
    rcases hno a b d (ι.base q) ha hb hd with h | h | h
    · exact (hab h).elim
    · exact Or.inl h.symm
    · exact Or.inr h.symm

end KltDP.Geometry.TransversalClosedPrimeUnion

#print axioms KltDP.Geometry.TransversalClosedPrimeUnion.transversalConfiguration_of_original_primes
