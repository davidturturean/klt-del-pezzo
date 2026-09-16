import KltDP.Geometry.TransverseBranchesOfSurfaceConfiguration
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The stalk ideals of the components at an intersection point

BRIEF27, item (G2). For a Noetherian scheme `X`, a selection `S` of irreducible components, an affine
chart `U` and a point `q ∈ U`, the **stalk ideal** `stalkIdeal S U hq` is the accepted chart ideal
`componentChartIdeal X S U` extended along the germ map `Γ(X, U) → O_{X, q}` (the ideals appearing
in `HasTransverseComponentBranches`).

* `stalkIdeal_mul_compl`: for `X` reduced, `stalkIdeal {C} · stalkIdeal {C}ᶜ = ⊥` (the accepted
  `componentChartIdeal_inf_compl`, since `I · J ≤ I ⊓ J`).
* `componentChartIdeal_singleton_isPrime`, `stalkIdeal_singleton_isPrime`: for `q ∈ C`, the chart ideal
  of the irreducible component `C` is prime (it is the vanishing ideal of the irreducible set
  `fromSpec⁻¹ C`), and so is its extension to the stalk (Mathlib's `isLocalization_stalk` and
  `IsLocalization.isPrime_of_isPrime_disjoint`).
* **`eq_of_stalkIdeal_le`**: the stalk ideals at `q` of two components through `q` are incomparable —
  `stalkIdeal {C} ≤ stalkIdeal {D}` forces `C = D` (contract to the chart with
  `IsLocalization.comap_map_of_isPrime_disjoint`, pass to zero loci, `D ∩ U ⊆ C`, and `D ⊆ C` by
  irreducibility of `D`; maximality of components). Hence `stalkIdeal_ne_bot_of_ne`: the stalk ideal of
  `C` at a point lying also on another component is nonzero.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.RationalTreePicard

variable {X : Scheme.{u}} [NoetherianSpace X]

/-- The stalk ideal of a selection of components at a point `q` of an affine chart `U`. -/
abbrev stalkIdeal (S : Set ↥(irreducibleComponents X)) (U : X.affineOpens) {q : X} (hq : q ∈ U.1) :
    Ideal (X.presheaf.stalk q) :=
  (componentChartIdeal X S U).map (X.presheaf.germ U.1 q hq).hom

/-! ## The product of the two branch ideals vanishes -/

theorem componentChartIdeal_mul_compl [AlgebraicGeometry.IsReduced X]
    (S : Set ↥(irreducibleComponents X)) (U : X.affineOpens) :
    componentChartIdeal X S U * componentChartIdeal X Sᶜ U = ⊥ :=
  eq_bot_iff.mpr (Ideal.mul_le_inf.trans (componentChartIdeal_inf_compl X S U).le)

theorem stalkIdeal_mul_compl [AlgebraicGeometry.IsReduced X] (S : Set ↥(irreducibleComponents X))
    (U : X.affineOpens) {q : X} (hq : q ∈ U.1) :
    stalkIdeal S U hq * stalkIdeal Sᶜ U hq = ⊥ := by
  rw [← Ideal.map_mul, componentChartIdeal_mul_compl, Ideal.map_bot]

/-! ## Primality -/

omit [NoetherianSpace X] in
theorem primeIdealOf_mem_preimage (C : ↥(irreducibleComponents X)) (U : X.affineOpens) {q : X}
    (hq : q ∈ U.1) (hqC : q ∈ C.1) :
    U.2.primeIdealOf ⟨q, hq⟩ ∈ U.2.fromSpec.base ⁻¹' C.1 := by
  rw [Set.mem_preimage, U.2.fromSpec_primeIdealOf]
  exact hqC

/-- The chart ideal of an irreducible component through a point of the chart is prime. -/
theorem componentChartIdeal_singleton_isPrime (C : ↥(irreducibleComponents X)) (U : X.affineOpens)
    {q : X} (hq : q ∈ U.1) (hqC : q ∈ C.1) : (componentChartIdeal X {C} U).IsPrime := by
  rw [componentChartIdeal_eq, ← PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime,
    coe_componentClosedUnion_singleton]
  exact ⟨⟨_, primeIdealOf_mem_preimage C U hq hqC⟩,
    (C.2 : Maximal IsIrreducible C.1).prop.2.preimage U.2.fromSpec.isOpenEmbedding⟩

theorem componentChartIdeal_le_primeIdealOf (C : ↥(irreducibleComponents X)) (U : X.affineOpens)
    {q : X} (hq : q ∈ U.1) (hqC : q ∈ C.1) :
    componentChartIdeal X {C} U ≤ (U.2.primeIdealOf ⟨q, hq⟩).asIdeal := by
  have h : U.2.primeIdealOf ⟨q, hq⟩ ∈
      PrimeSpectrum.zeroLocus (componentChartIdeal X {C} U : Set Γ(X, U.1)) := by
    rw [componentChartIdeal_zeroLocus, coe_componentClosedUnion_singleton]
    exact primeIdealOf_mem_preimage C U hq hqC
  exact (PrimeSpectrum.mem_zeroLocus _ _).mp h

theorem disjoint_primeCompl_componentChartIdeal (C : ↥(irreducibleComponents X))
    (U : X.affineOpens) {q : X} (hq : q ∈ U.1) (hqC : q ∈ C.1) :
    Disjoint ((U.2.primeIdealOf ⟨q, hq⟩).asIdeal.primeCompl : Set Γ(X, U.1))
      (componentChartIdeal X {C} U : Set Γ(X, U.1)) := by
  rw [Set.disjoint_left]
  intro s hs hsI
  exact hs (componentChartIdeal_le_primeIdealOf C U hq hqC hsI)

/-- The stalk ideal of an irreducible component through `q` is prime. -/
theorem stalkIdeal_singleton_isPrime (C : ↥(irreducibleComponents X)) (U : X.affineOpens) {q : X}
    (hq : q ∈ U.1) (hqC : q ∈ C.1) : (stalkIdeal {C} U hq).IsPrime := by
  letI := X.presheaf.algebra_section_stalk ⟨q, hq⟩
  haveI := U.2.isLocalization_stalk ⟨q, hq⟩
  exact IsLocalization.isPrime_of_isPrime_disjoint _ (X.presheaf.stalk q) _
    (componentChartIdeal_singleton_isPrime C U hq hqC)
    (disjoint_primeCompl_componentChartIdeal C U hq hqC)

/-! ## Incomparability of the stalk ideals of two components through a point -/

/-- **The stalk ideals of two components through `q` are incomparable**: containment forces the
components to coincide. -/
theorem eq_of_stalkIdeal_le (C D : ↥(irreducibleComponents X)) (U : X.affineOpens) {q : X}
    (hq : q ∈ U.1) (hqD : q ∈ D.1)
    (h : stalkIdeal {C} U hq ≤ stalkIdeal {D} U hq) : C = D := by
  letI := X.presheaf.algebra_section_stalk ⟨q, hq⟩
  haveI := U.2.isLocalization_stalk ⟨q, hq⟩
  have h1 : componentChartIdeal X {C} U ≤ componentChartIdeal X {D} U := by
    have h2 := Ideal.map_le_iff_le_comap.mp h
    have h3 : Ideal.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk q))
        (Ideal.map (algebraMap Γ(X, U.1) (X.presheaf.stalk q)) (componentChartIdeal X {D} U)) =
          componentChartIdeal X {D} U :=
      IsLocalization.comap_map_of_isPrime_disjoint _ (X.presheaf.stalk q) _
        (componentChartIdeal_singleton_isPrime D U hq hqD)
        (disjoint_primeCompl_componentChartIdeal D U hq hqD)
    exact h2.trans (le_of_eq h3)
  have h4 : U.2.fromSpec.base ⁻¹' D.1 ⊆ U.2.fromSpec.base ⁻¹' C.1 := by
    have h5 := PrimeSpectrum.zeroLocus_anti_mono_ideal h1
    rwa [componentChartIdeal_zeroLocus, componentChartIdeal_zeroLocus,
      coe_componentClosedUnion_singleton, coe_componentClosedUnion_singleton] at h5
  have h6 : D.1 ∩ (U.1 : Set X) ⊆ C.1 := by
    rintro x ⟨hxD, hxU⟩
    have hx := h4 (primeIdealOf_mem_preimage D U hxU hxD)
    rwa [Set.mem_preimage, U.2.fromSpec_primeIdealOf] at hx
  have h7 : D.1 ⊆ C.1 := by
    by_contra hnot
    obtain ⟨x, hxD, hxC⟩ := Set.not_subset.mp hnot
    obtain ⟨y, hyD, hyU, hyC⟩ := (D.2 : Maximal IsIrreducible D.1).prop.2 (U.1 : Set X) (C.1)ᶜ
      U.1.isOpen (isClosed_of_mem_irreducibleComponents C.1 C.2).isOpen_compl ⟨q, hqD, hq⟩
      ⟨x, hxD, hxC⟩
    exact hyC (h6 ⟨hyD, hyU⟩)
  exact (Subtype.ext ((D.2 : Maximal IsIrreducible D.1).eq_of_le
    (C.2 : Maximal IsIrreducible C.1).prop h7)).symm

/-- The stalk ideal of `C` at a point lying on a second component `D ≠ C` is nonzero. -/
theorem stalkIdeal_ne_bot_of_ne (C D : ↥(irreducibleComponents X)) (hCD : C ≠ D)
    (U : X.affineOpens) {q : X} (hq : q ∈ U.1) (hqD : q ∈ D.1) :
    stalkIdeal {C} U hq ≠ ⊥ := fun h =>
  hCD (eq_of_stalkIdeal_le C D U hq hqD (by rw [h]; exact bot_le))

end KltDP.Geometry.RationalTreePicard
