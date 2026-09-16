import KltDP.RingTheory.FactorialHartogs
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Extension of sections across a point with a two-dimensional factorial stalk

BRIEF30, task 2 (F09 step (i)). Let `S` be an integral scheme, `U` an affine open, `x ∈ U` a point whose
stalk `O_{S,x}` is a unique factorisation domain of Krull dimension two, and `V` an open containing every
point of `U` other than `x` (for instance `U ∖ {x}` when `x` is closed). Then every section of `O_S` on `V`
comes from a unique section on `U`.

* Points of an affine open and primes of its section ring (`primeIdealOf_fromSpec_base`), and the primes of
  the stalk at `x` other than its maximal ideal: each is the extension of the prime of a point `y ∈ U`,
  `y ≠ x` (`exists_point_of_prime_ne_maximalIdeal`); in particular `U` has a point other than `x`
  (`exists_mem_ne_of_ringKrullDim_eq_two`) and `V` is nonempty (`nonempty_of_forall_ne`).
* An element of the function field coming from the stalk at `y ∈ U` lies in the localisation of `Γ(S, U)`
  at the prime of `y` (`memLocalizationAt_of_stalk`, via Mathlib's `IsAffineOpen.isLocalization_stalk`).
* **Hartogs at `x`** (`exists_algebraMap_stalk_eq`): the rational function of `s ∈ Γ(S, V)` lies in the
  image of `O_{S,x}` — by `FactorialHartogs.exists_eq_algebraMap_of_forall_ne_bot_ne_maximalIdeal`, since at
  every prime other than `0` and the maximal ideal it is regular (it is a germ of `s` at a point of `V`).
* **Extension** (`exists_germToFunctionField_eq`, `exists_restrict_eq`, `existsUnique_restrict_eq`): the
  rational function of `s` lies in every localisation of `Γ(S, U)` at a maximal ideal (at `x` by Hartogs,
  elsewhere as a germ of `s`), hence in `Γ(S, U)` (`FactorialHartogs.mem_range_iff_forall_isMaximal`);
  restriction to `V` is injective on an integral scheme.
* **Units** (`exists_unit_extension`): a unit on `V` extends to a unit on `U` with the same rational function.
* The closed-point form (`existsUnique_restrict_eq_of_isClosed`) for `V = U ⊓ {x}ᶜ`.

No Noetherian hypothesis enters. The factorial hypothesis is the instance
`[UniqueFactorizationMonoid (S.presheaf.stalk x)]` (for a regular point it is supplied by the accepted
`regularPoint_stalk_uniqueFactorizationMonoid`), the dimension hypothesis is
`ringKrullDim (S.presheaf.stalk x) = 2`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.ExtendAcrossClosedPoint

open KltDP.RingTheory.FactorialHartogs

/-- The stalks of an integral scheme are domains: they embed in the function field. -/
theorem stalk_isDomain (T : Scheme.{u}) [IsIntegral T] (y : T) : IsDomain (T.presheaf.stalk y) :=
  Function.Injective.isDomain (algebraMap (T.presheaf.stalk y) T.functionField)
    (IsFractionRing.injective _ _)

local instance (T : Scheme.{u}) [IsIntegral T] (y : T) : IsDomain (T.presheaf.stalk y) :=
  stalk_isDomain T y

variable {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U)

/-! ## Points of an affine open and primes of its section ring -/

/-- The prime of the point `fromSpec P` is `P`. -/
theorem primeIdealOf_fromSpec_base (P : PrimeSpectrum Γ(S, U)) :
    hU.primeIdealOf ⟨hU.fromSpec.base P, (hU.isoSpec.inv.base P).2⟩ = P :=
  hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)

/-- Every prime of the stalk at `x ∈ U` other than the maximal ideal lies over the prime of a point
`y ∈ U` different from `x`. -/
theorem exists_point_of_prime_ne_maximalIdeal {x : S} (hxU : x ∈ U)
    (p : Ideal (S.presheaf.stalk x)) [p.IsPrime]
    (hp : p ≠ IsLocalRing.maximalIdeal (S.presheaf.stalk x)) :
    ∃ (y : S) (hyU : y ∈ U), y ≠ x ∧
      (hU.primeIdealOf ⟨y, hyU⟩).asIdeal = p.comap (S.presheaf.germ U x hxU).hom := by
  let Q : PrimeSpectrum Γ(S, U) :=
    ⟨p.comap (S.presheaf.germ U x hxU).hom, Ideal.comap_isPrime _ _⟩
  have hyU : hU.fromSpec.base Q ∈ U := (hU.isoSpec.inv.base Q).2
  refine ⟨hU.fromSpec.base Q, hyU, ?_,
    congrArg PrimeSpectrum.asIdeal (primeIdealOf_fromSpec_base hU Q)⟩
  intro hyx
  apply hp
  have hQx : Q = hU.primeIdealOf ⟨x, hxU⟩ :=
    hU.fromSpec.isOpenEmbedding.injective (hyx.trans (hU.fromSpec_primeIdealOf ⟨x, hxU⟩).symm)
  letI : Algebra Γ(S, U) (S.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨x, hxU⟩
  haveI : IsLocalization.AtPrime (S.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have hm : (IsLocalRing.maximalIdeal (S.presheaf.stalk x)).comap
      (algebraMap Γ(S, U) (S.presheaf.stalk x)) = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    IsLocalization.AtPrime.comap_maximalIdeal (S.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal inferInstance
  have hcomap : p.comap (algebraMap Γ(S, U) (S.presheaf.stalk x)) =
      (IsLocalRing.maximalIdeal (S.presheaf.stalk x)).comap
        (algebraMap Γ(S, U) (S.presheaf.stalk x)) := by
    rw [hm]
    exact congrArg PrimeSpectrum.asIdeal hQx
  calc p = (p.comap (algebraMap Γ(S, U) (S.presheaf.stalk x))).map
          (algebraMap Γ(S, U) (S.presheaf.stalk x)) :=
        (IsLocalization.map_comap (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
          (S.presheaf.stalk x) p).symm
    _ = ((IsLocalRing.maximalIdeal (S.presheaf.stalk x)).comap
          (algebraMap Γ(S, U) (S.presheaf.stalk x))).map
          (algebraMap Γ(S, U) (S.presheaf.stalk x)) := by rw [hcomap]
    _ = IsLocalRing.maximalIdeal (S.presheaf.stalk x) :=
        IsLocalization.map_comap (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
          (S.presheaf.stalk x) _

include hU in
/-- A point whose stalk has Krull dimension two is not the only point of an affine open containing it. -/
theorem exists_mem_ne_of_ringKrullDim_eq_two {x : S} (hxU : x ∈ U)
    (hdim : ringKrullDim (S.presheaf.stalk x) = 2) : ∃ y ∈ U, y ≠ x := by
  obtain ⟨p, hp, -, hpm⟩ := exists_isPrime_ne_bot_ne_maximalIdeal (S.presheaf.stalk x) hdim
  obtain ⟨y, hyU, hyx, -⟩ := exists_point_of_prime_ne_maximalIdeal hU hxU p hpm
  exact ⟨y, hyU, hyx⟩

include hU in
/-- An open containing every point of `U` other than `x` is nonempty. -/
theorem nonempty_of_forall_ne {x : S} (hxU : x ∈ U)
    (hdim : ringKrullDim (S.presheaf.stalk x) = 2) {V : S.Opens}
    (hV : ∀ y ∈ U, y ≠ x → y ∈ V) : Nonempty V := by
  obtain ⟨y, hyU, hyx⟩ := exists_mem_ne_of_ringKrullDim_eq_two hU hxU hdim
  exact ⟨⟨y, hV y hyU hyx⟩⟩

/-! ## Regularity of rational functions at the points of an affine open -/

variable [IsIntegral S]

/-- The image in the function field of an element of the stalk at `y ∈ U` lies in the localisation of
`Γ(S, U)` at the prime of `y`. -/
theorem memLocalizationAt_of_stalk [Nonempty U] {y : S} (hyU : y ∈ U) (g : S.presheaf.stalk y) :
    MemLocalizationAt Γ(S, U) S.functionField (hU.primeIdealOf ⟨y, hyU⟩).asIdeal
      (algebraMap (S.presheaf.stalk y) S.functionField g) := by
  letI : Algebra Γ(S, U) (S.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨y, hyU⟩
  haveI : IsLocalization.AtPrime (S.presheaf.stalk y) (hU.primeIdealOf ⟨y, hyU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hyU⟩
  haveI : IsScalarTower Γ(S, U) (S.presheaf.stalk y) S.functionField :=
    functionField_isScalarTower S U ⟨y, hyU⟩
  obtain ⟨⟨a, t⟩, hat⟩ :=
    IsLocalization.surj (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl g
  refine ⟨a, t, t.2, ?_⟩
  have h := congrArg (algebraMap (S.presheaf.stalk y) S.functionField) hat
  rw [map_mul, ← IsScalarTower.algebraMap_apply Γ(S, U) (S.presheaf.stalk y) S.functionField,
    ← IsScalarTower.algebraMap_apply Γ(S, U) (S.presheaf.stalk y) S.functionField] at h
  rw [mul_comm]
  exact h

/-- The germ of a section at a point, sent to the function field, is its rational function. -/
theorem algebraMap_germ {V : S.Opens} [Nonempty V] {y : S} (hyV : y ∈ V) (s : Γ(S, V)) :
    algebraMap (S.presheaf.stalk y) S.functionField (S.presheaf.germ V y hyV s) =
      S.germToFunctionField V s :=
  TopCat.Presheaf.germ_stalkSpecializes_apply S.presheaf hyV _ s

/-! ## Hartogs at the point and extension -/

variable {x : S} (hxU : x ∈ U) [UniqueFactorizationMonoid (S.presheaf.stalk x)]
  (hdim : ringKrullDim (S.presheaf.stalk x) = 2)

include hU hxU hdim

/-- **Hartogs at `x`**: the rational function of a section on an open containing `U ∖ {x}` comes from the
stalk at `x`. -/
theorem exists_algebraMap_stalk_eq [Nonempty U] {V : S.Opens} [Nonempty V]
    (hV : ∀ y ∈ U, y ≠ x → y ∈ V) (s : Γ(S, V)) :
    ∃ g : S.presheaf.stalk x,
      algebraMap (S.presheaf.stalk x) S.functionField g = S.germToFunctionField V s := by
  letI : Algebra Γ(S, U) (S.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨x, hxU⟩
  haveI : IsScalarTower Γ(S, U) (S.presheaf.stalk x) S.functionField :=
    functionField_isScalarTower S U ⟨x, hxU⟩
  apply exists_eq_algebraMap_of_forall_ne_bot_ne_maximalIdeal (S.presheaf.stalk x)
    S.functionField hdim
  intro p hp _ hpm
  apply MemLocalizationAt.of_comap Γ(S, U) S.functionField p
  obtain ⟨y, hyU, hyx, hy⟩ := exists_point_of_prime_ne_maximalIdeal hU hxU p hpm
  have h := memLocalizationAt_of_stalk hU hyU (S.presheaf.germ V y (hV y hyU hyx) s)
  rw [algebraMap_germ, hy] at h
  exact h

/-- **Extension across `x`** in function-field form: the rational function of a section on an open
containing `U ∖ {x}` is the rational function of a section on `U`. -/
theorem exists_germToFunctionField_eq [Nonempty U] {V : S.Opens} [Nonempty V]
    (hV : ∀ y ∈ U, y ≠ x → y ∈ V) (s : Γ(S, V)) :
    ∃ t : Γ(S, U), S.germToFunctionField U t = S.germToFunctionField V s := by
  have hf : S.germToFunctionField V s ∈ Set.range (algebraMap Γ(S, U) S.functionField) := by
    rw [mem_range_iff_forall_isMaximal]
    intro P hP
    let Q : PrimeSpectrum Γ(S, U) := ⟨P, hP.isPrime⟩
    have hyU : hU.fromSpec.base Q ∈ U := (hU.isoSpec.inv.base Q).2
    have hQ : (hU.primeIdealOf ⟨_, hyU⟩).asIdeal = P :=
      congrArg PrimeSpectrum.asIdeal (primeIdealOf_fromSpec_base hU Q)
    by_cases hyx : hU.fromSpec.base Q = x
    · have hQx : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal = P := by
        have h : hU.primeIdealOf ⟨x, hxU⟩ = Q :=
          hU.fromSpec.isOpenEmbedding.injective
            ((hU.fromSpec_primeIdealOf ⟨x, hxU⟩).trans hyx.symm)
        exact congrArg PrimeSpectrum.asIdeal h
      obtain ⟨g, hg⟩ := exists_algebraMap_stalk_eq hU hxU hdim hV s
      rw [← hQx, ← hg]
      exact memLocalizationAt_of_stalk hU hxU g
    · rw [← hQ, ← algebraMap_germ (hV _ hyU hyx) s]
      exact memLocalizationAt_of_stalk hU hyU _
  obtain ⟨t, ht⟩ := hf
  exact ⟨t, ht⟩

/-- **Extension across `x`**: every section on an open `V ⊆ U` containing `U ∖ {x}` is the restriction of a
section on `U`. -/
theorem exists_restrict_eq {V : S.Opens} (hVU : V ≤ U) (hV : ∀ y ∈ U, y ≠ x → y ∈ V)
    (s : Γ(S, V)) : ∃ t : Γ(S, U), S.presheaf.map (homOfLE hVU).op t = s := by
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI : Nonempty V := nonempty_of_forall_ne hU hxU hdim hV
  obtain ⟨t, ht⟩ := exists_germToFunctionField_eq hU hxU hdim hV s
  refine ⟨t, S.germToFunctionField_injective V ?_⟩
  rw [← ht]
  exact TopCat.Presheaf.germ_res_apply S.presheaf (homOfLE hVU) (genericPoint S) _ t

/-- **Unique extension across `x`**. -/
theorem existsUnique_restrict_eq {V : S.Opens} (hVU : V ≤ U) (hV : ∀ y ∈ U, y ≠ x → y ∈ V)
    (s : Γ(S, V)) : ∃! t : Γ(S, U), S.presheaf.map (homOfLE hVU).op t = s := by
  haveI : Nonempty V := nonempty_of_forall_ne hU hxU hdim hV
  obtain ⟨t, ht⟩ := exists_restrict_eq hU hxU hdim hVU hV s
  exact ⟨t, ht, fun t' ht' => map_injective_of_isIntegral S (homOfLE hVU) (ht'.trans ht.symm)⟩

/-- **Units extend across `x`**: a unit on an open containing `U ∖ {x}` has the rational function of a unit
on `U`. -/
theorem exists_unit_extension [Nonempty U] {V : S.Opens} [Nonempty V]
    (hV : ∀ y ∈ U, y ≠ x → y ∈ V) (a : Γ(S, V)ˣ) :
    ∃ b : Γ(S, U)ˣ, Units.map (S.germToFunctionField U).hom.toMonoidHom b =
      Units.map (S.germToFunctionField V).hom.toMonoidHom a := by
  obtain ⟨b, hb⟩ := exists_germToFunctionField_eq hU hxU hdim hV (a : Γ(S, V))
  obtain ⟨c, hc⟩ := exists_germToFunctionField_eq hU hxU hdim hV (↑a⁻¹ : Γ(S, V))
  have hbc : b * c = 1 := by
    apply S.germToFunctionField_injective U
    change (S.germToFunctionField U).hom (b * c) = (S.germToFunctionField U).hom 1
    rw [map_mul, map_one]
    change S.germToFunctionField U b * S.germToFunctionField U c = 1
    rw [hb, hc]
    change (S.germToFunctionField V).hom (a : Γ(S, V)) * (S.germToFunctionField V).hom ↑a⁻¹ = 1
    rw [← map_mul, Units.mul_inv, map_one]
  refine ⟨⟨b, c, hbc, (mul_comm c b).trans hbc⟩, ?_⟩
  apply Units.ext
  exact hb

/-- **Unique extension across a closed point** `x`: sections on `U ∖ {x}` extend uniquely to `U`. -/
theorem existsUnique_restrict_eq_of_isClosed (hclosed : IsClosed ({x} : Set S))
    (s : Γ(S, U ⊓ (⟨({x} : Set S)ᶜ, hclosed.isOpen_compl⟩ : S.Opens))) :
    ∃! t : Γ(S, U), S.presheaf.map (homOfLE inf_le_left).op t = s :=
  existsUnique_restrict_eq hU hxU hdim inf_le_left
    (fun _ hyU hyx => TopologicalSpace.Opens.mem_inf.mpr ⟨hyU, hyx⟩) s

end KltDP.Geometry.ExtendAcrossClosedPoint
