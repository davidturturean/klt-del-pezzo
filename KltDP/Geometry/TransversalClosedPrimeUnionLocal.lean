import KltDP.Geometry.ClosedImmersionActualStalkKernel
import KltDP.Geometry.PrimeCurveCrossingCoefficient
import KltDP.Geometry.RationalTreePicardOfConfiguration
import KltDP.Geometry.IntersectionPairingSymmetry
import KltDP.Geometry.ClosedPointDimension
import KltDP.Geometry.CotangentGenerators

/-!
# Transversality of an actual reduced closed union of original prime curves

The finite family consists of prime curves on the original regular surface.
The union is any reduced closed immersion with precisely their union as its
range. Its original stalk kernel is derived from that range and reducedness.
The only crossing input is that the two original vanishing ideals generate
the ambient maximal ideal. No product kernel or branch membership is input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.TransversalClosedPrimeUnion

open NormalProjectiveSurface RationalTreePicard

section Localization

/-- Localization preserves binary intersections of ideals. The pinned API
already contains the denominator criterion used in this proof. -/
theorem map_inf_of_localization {R T : Type*} [CommRing R] [CommRing T]
    (M : Submonoid R) [Algebra R T] [IsLocalization M T] (I J : Ideal R) :
    (I ⊓ J).map (algebraMap R T) =
      I.map (algebraMap R T) ⊓ J.map (algebraMap R T) := by
  ext z
  obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective M z
  simp only [Ideal.mem_inf, IsLocalization.mk'_mem_map_algebraMap_iff]
  constructor
  · rintro ⟨m, hm, hI, hJ⟩
    exact ⟨⟨m, hm, hI⟩, ⟨m, hm, hJ⟩⟩
  · rintro ⟨⟨m, hm, hI⟩, ⟨n, hn, hJ⟩⟩
    refine ⟨m * n, M.mul_mem hm hn, ?_, ?_⟩
    · rw [mul_comm m n, mul_assoc]
      exact I.mul_mem_left n hI
    · rw [mul_assoc]
      exact J.mul_mem_left m hJ

/-- Localization preserves every finite intersection of ideals. -/
theorem map_iInf_of_localization {R T : Type*} [CommRing R] [CommRing T]
    (M : Submonoid R) [Algebra R T] [IsLocalization M T]
    {I : Type*} [Finite I] (J : I → Ideal R) :
    (⨅ i, J i).map (algebraMap R T) = ⨅ i, (J i).map (algebraMap R T) := by
  have h : ∀ (s : Set I), s.Finite →
      (⨅ i ∈ s, J i).map (algebraMap R T) =
        ⨅ i ∈ s, (J i).map (algebraMap R T) := by
    intro s hs
    refine Set.Finite.induction_on s hs ?_ ?_
    · simp [Ideal.map_top]
    · intro i s _ _ ih
      simp only [iInf_insert, map_inf_of_localization M, ih]
  simpa using h Set.univ Set.finite_univ

/-- A finite intersection of ideal sheaves gives the intersection of the
original germ ideals on any affine neighborhood. -/
theorem germ_map_iInf {Y : Scheme.{u}} {I : Type*} [Finite I]
    (J : I → Y.IdealSheafData) (U : Y.affineOpens) (x : Y) (hx : x ∈ U.1) :
    ((⨅ i, J i).ideal U).map (Y.presheaf.germ U.1 x hx).hom =
      ⨅ i, ((J i).ideal U).map (Y.presheaf.germ U.1 x hx).hom := by
  letI := Y.presheaf.algebra_section_stalk ⟨x, hx⟩
  letI := U.2.isLocalization_stalk ⟨x, hx⟩
  rw [Scheme.IdealSheafData.ideal_iInf, iInf_apply]
  exact map_iInf_of_localization (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _

end Localization

section ReducedImmersion

/-- A reduced closed immersion has precisely the vanishing ideal of its
actual closed image as its kernel ideal sheaf. -/
theorem ker_eq_vanishingIdeal {Z Y : Scheme.{u}} (ι : Z ⟶ Y)
    [IsClosedImmersion ι] [AlgebraicGeometry.IsReduced Z]
    (T : Closeds Y) (hT : (T : Set Y) = Set.range ι.base) :
    ι.ker = Scheme.IdealSheafData.vanishingIdeal T := by
  have hs : ι.ker.support = T := by
    apply Closeds.ext
    rw [Scheme.Hom.support_ker, hT]
    exact ι.isClosedEmbedding.isClosed_range.closure_eq
  rw [← SchematicImageDenseOpen.ker_radical ι,
    ← Scheme.IdealSheafData.vanishingIdeal_support, hs]

end ReducedImmersion

section OriginalPrimeIdeals

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k)
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

/-- The original prime-curve germ ideal is prime at every point on that
curve, because its actual quotient is the curve's integral stalk. -/
theorem prime_germ_isPrime (C : S.PrimeCurve) (U : S.toScheme.affineOpens)
    (x : S.toScheme) (hxU : x ∈ U.1) (hxC : x ∈ C) :
    ((C.vanishingIdeal.ideal U).map (S.toScheme.presheaf.germ U.1 x hxU).hom).IsPrime := by
  change x ∈ (C : Set S.toScheme) at hxC
  rw [← C.range_inclusion] at hxC
  obtain ⟨y, rfl⟩ := hxC
  have hker : RingHom.ker (C.inclusion.stalkMap y).hom =
      (C.vanishingIdeal.ideal U).map
        (S.toScheme.presheaf.germ U.1 (C.inclusion.base y) hxU).hom :=
    C.vanishingIdeal.stalkMap_gluedTo_ker_eq_map U hxU
  rw [← hker]
  letI := integralSchemeStalk_isDomain C.toScheme y
  exact RingHom.ker_isPrime (C.inclusion.stalkMap y).hom

include hregular in
/-- Off the original curve, its germ ideal is the unit ideal. -/
theorem prime_germ_eq_top_of_not_mem (C : S.PrimeCurve) (U : S.toScheme.affineOpens)
    (x : S.toScheme) (hxU : x ∈ U.1) (hxC : x ∉ C) :
    (C.vanishingIdeal.ideal U).map (S.toScheme.presheaf.germ U.1 x hxU).hom = ⊤ := by
  obtain ⟨c, hxc⟩ := S.primeCurveCartier_hasRegularEquations hregular C x
  rw [PrimeCurveCrossingCoefficient.vanishingIdeal_map_germ_eq_span_coefficient
    S hregular C U x hxU c hxc]
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_singleton _))
  apply PrimeCurve.germ_isUnit_of_not_mem_support (S.primeCurveCartier hregular C)
    (S.primeCurveCartier_hasRegularEquations hregular C) c x hxc
  change x ∉ ((effectiveCartierIdealDataOfRegularEquations S.toScheme
    (S.primeCurveCartier hregular C)
    (S.primeCurveCartier_hasRegularEquations hregular C)).support : Set S.toScheme)
  rw [S.primeCurveCartier_support hregular C]
  exact hxC

include hregular in
/-- A point on two distinct original prime curves is closed, hence has
the original surface's two-dimensional stalk. -/
theorem crossing_stalk_dimension_two (C D : S.PrimeCurve) (hCD : C ≠ D)
    (x : S.toScheme) (hxC : x ∈ C) (hxD : x ∈ D) :
    ringKrullDim (S.toScheme.presheaf.stalk x) = 2 := by
  let d := S.primeCurveCartier hregular D
  let hd := S.primeCurveCartier_hasRegularEquations hregular D
  let hn := S.notInSupport_of_ne hregular hCD
  have hx : x ∈ Set.range (C.intersectionToSurface d hd hn).base := by
    rw [C.range_intersectionToSurface, S.primeCurveCartier_support hregular D]
    exact ⟨hxC, hxD⟩
  exact S.closed_stalk_dimension_two x
    ((C.range_intersectionToSurface_finite_and_isClosed d hd hn).2 x hx)

variable {I : Type u} [Finite I] (C : I → S.PrimeCurve)
    {Z : Scheme.{u}} (ι : Z ⟶ S.toScheme) [IsClosedImmersion ι]
    [AlgebraicGeometry.IsReduced Z]
    (hrange : Set.range ι.base = ⋃ i, (C i : Set S.toScheme))

include hrange in
/-- The kernel ideal sheaf of the actual reduced union is the finite
intersection of the original prime-curve vanishing ideal sheaves. -/
theorem ker_eq_iInf_prime : ι.ker = ⨅ i, (C i).vanishingIdeal := by
  let T : Closeds S.toScheme := ⟨Set.range ι.base, ι.isClosedEmbedding.isClosed_range⟩
  rw [ker_eq_vanishingIdeal ι T rfl]
  have hT : (T : Set S.toScheme) = ⋃ i, Set.range (C i).inclusion.base := by
    simpa only [PrimeCurve.range_inclusion] using hrange
  rw [Scheme.IdealSheafData.vanishingIdeal_eq_iInf_ker_radical
    (fun i => (C i).inclusion) T hT]
  congr 1
  funext i
  rw [SchematicImageDenseOpen.ker_radical]
  exact (C i).vanishingIdeal.ker_gluedTo

include hrange in
/-- The original immersion's actual stalk kernel is the intersection of
the original prime-curve germ ideals. -/
theorem stalk_ker_eq_iInf_prime (q : Z) (U : S.toScheme.affineOpens)
    (hqU : ι.base q ∈ U.1) :
    RingHom.ker (ι.stalkMap q).hom =
      ⨅ i, ((C i).vanishingIdeal.ideal U).map
        (S.toScheme.presheaf.germ U.1 (ι.base q) hqU).hom := by
  rw [closedImmersion_stalkMap_ker_eq_map ι U hqU,
    ker_eq_iInf_prime S C ι hrange, germ_map_iInf]

include hregular hrange in
/-- At a point lying on at most the two named curves, the actual stalk
kernel is the intersection of their two original germ ideals. -/
theorem stalk_ker_eq_inf_prime (a b : I) (q : Z) (U : S.toScheme.affineOpens)
    (hqU : ι.base q ∈ U.1)
    (hno : ∀ i, ι.base q ∈ C i → i = a ∨ i = b) :
    RingHom.ker (ι.stalkMap q).hom =
      ((C a).vanishingIdeal.ideal U).map (S.toScheme.presheaf.germ U.1 (ι.base q) hqU).hom ⊓
      ((C b).vanishingIdeal.ideal U).map (S.toScheme.presheaf.germ U.1 (ι.base q) hqU).hom := by
  rw [stalk_ker_eq_iInf_prime S C ι hrange]
  refine iInf_eq_inf_of_top _ a b ?_
  intro i hia hib
  exact prime_germ_eq_top_of_not_mem S hregular (C i) U (ι.base q) hqU
    (fun hi => (hno i hi).elim hia hib)

end OriginalPrimeIdeals

section Parameters

/-- Two generators of a regular two-dimensional maximal ideal cannot be
contained one in the principal ideal generated by the other. -/
theorem first_parameter_not_mem_second {R : Type u} [CommRing R] [IsLocalRing R]
    (hreg : RegularLocal R) (hdim : ringKrullDim R = 2) (f g : R)
    (hspan : Ideal.span {f, g} = maximalIdeal R) : f ∉ Ideal.span {g} := by
  intro hf
  letI : IsNoetherianRing R := hreg.1
  have hfg : Ideal.span {f} ≤ Ideal.span {g} :=
    (Ideal.span_singleton_le_iff_mem _).mpr hf
  have hgspan : Ideal.span {g} = maximalIdeal R := by
    simpa only [Ideal.span_insert, sup_eq_right.mpr hfg] using hspan
  have hg : g ∈ maximalIdeal R := hgspan ▸ Ideal.subset_span (Set.mem_singleton g)
  let v : Fin 1 → maximalIdeal R := fun _ => ⟨g, hg⟩
  have hv : Ideal.span (Set.range (fun i => (v i : R))) = maximalIdeal R := by
    simpa only [v, Set.range_const] using hgspan
  have hle := finrank_cotangentSpace_le_card_of_generators v hv
  rw [finrank_cotangentSpace_eq_two_of_regularLocal hreg hdim, Fintype.card_fin] at hle
  omega

end Parameters

section BranchImages

variable {Y Z : Scheme.{u}} [NoetherianSpace Z] (ι : Z ⟶ Y) [IsClosedImmersion ι]
    {W : Scheme.{u}} (c : W ⟶ Z) [QuasiCompact c]
    (A : ↥(irreducibleComponents Z)) (hA : A.1 = Set.range c.base)

include hA in
/-- Sections killed by the original composite into the ambient scheme
map into the actual component ideal on the union. -/
theorem map_app_ker_le_component (U : Y.affineOpens) :
    ((c ≫ ι).ker.ideal U).map (ι.app U.1).hom ≤
      componentChartIdeal Z {A} ⟨ι ⁻¹ᵁ U.1, U.2.preimage ι⟩ := by
  have hle : c.ker ≤ componentUnionIdeal Z {A} := by
    rw [componentUnionIdeal, ← Scheme.IdealSheafData.subset_support_iff_le_vanishingIdeal,
      coe_componentClosedUnion_singleton, hA]
    exact c.range_subset_ker_support
  rw [Ideal.map_le_iff_le_comap]
  intro s hs
  apply (Scheme.IdealSheafData.le_def.mp hle) ⟨ι ⁻¹ᵁ U.1, U.2.preimage ι⟩
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hs ⊢
  have he := ConcreteCategory.congr_hom (Scheme.comp_app c ι U.1) s
  exact he.symm.trans hs

include hA in
/-- The original composite's germ ideal maps into the original component
germ ideal, on every affine chart of the union. -/
theorem map_stalk_ker_le_component (q : Z) (U : Y.affineOpens)
    (hqU : ι.base q ∈ U.1) (V : Z.affineOpens) (hqV : q ∈ V.1) :
    (((c ≫ ι).ker.ideal U).map (Y.presheaf.germ U.1 (ι.base q) hqU).hom).map
        (ι.stalkMap q).hom ≤
      (componentChartIdeal Z {A} V).map (Z.presheaf.germ V.1 q hqV).hom := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.stalkMap_germ, CommRingCat.hom_comp,
    ← Ideal.map_map]
  refine (Ideal.map_mono (map_app_ker_le_component ι c A hA U)).trans ?_
  exact (ideal_map_germ_eq (componentUnionIdeal Z {A})
    (U := ⟨ι ⁻¹ᵁ U.1, U.2.preimage ι⟩) (W := V) q hqU hqV).le

end BranchImages

end KltDP.Geometry.TransversalClosedPrimeUnion
