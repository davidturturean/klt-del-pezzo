import KltDP.Geometry.Surface
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Data.Set.Finite.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Topology.NoetherianSpace

/-!
# Regular local rings and actual singular points

Regularity is the Noetherian local-ring condition that the Krull dimension
equals the dimension of the cotangent space over the residue field. The
Noetherian condition guarantees that the cotangent dimension is finite.

The singular locus is defined on actual scheme points. Every finite-set and
cardinality operation below requires a proof that this locus is finite; no
finiteness theorem for normal surfaces is assumed or asserted here.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry

/-- The ordinary regular-local-ring predicate, using `m/m²` over `R/m`.
The explicit Noetherian conjunct rules out using `finrank` on an infinite
cotangent space. -/
def RegularLocal (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧
    ringKrullDim R =
      (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :
        WithBot ℕ∞)

/-- The dimension appearing in regularity is genuinely finite. -/
theorem regularLocal_cotangent_finiteDimensional {R : Type u}
    [CommRing R] [IsLocalRing R] (hR : RegularLocal R) :
    FiniteDimensional (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  letI : IsNoetherianRing R := hR.1
  infer_instance

/-- Fields are regular local rings of dimension zero. -/
theorem regularLocal_field (k : Type u) [Field k] : RegularLocal k := by
  refine ⟨inferInstance, ?_⟩
  rw [ringKrullDim_eq_zero_of_field, IsLocalRing.finrank_cotangentSpace_eq_zero]
  rfl

/-- Regularity of a field structure on the given ring. The proposition
`IsField R` refers to its existing multiplication, without replacing the ring
structure by a potentially unrelated `Field` instance on the same type. -/
theorem regularLocal_of_isField {R : Type u} [CommRing R] [IsLocalRing R]
    (hfield : IsField R) : RegularLocal R := by
  letI := hfield.toField
  exact regularLocal_field R

/-- A Noetherian normal local domain of Krull dimension at most one is regular.
The nonfield case has a principal maximal ideal and one-dimensional cotangent
space, by the proved discrete-valuation-ring characterizations in Mathlib. -/
theorem regularLocal_of_isIntegrallyClosed_of_ringKrullDim_le_one
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R ≤ 1) : RegularLocal R := by
  by_cases hfield : IsField R
  · exact regularLocal_of_isField hfield
  letI : Ring.KrullDimLE 1 R := ⟨hdim⟩
  have hprime :
      ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime →
        P = IsLocalRing.maximalIdeal R := by
    intro P hP hPprime
    apply IsLocalRing.eq_maximalIdeal
    exact (Ring.krullDimLE_one_iff_of_noZeroDivisors (R := R)).mp
      inferInstance P hP hPprime
  have hcot_le :
      Module.finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.CotangentSpace R) ≤ 1 :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 3 5).mp
      (show IsIntegrallyClosed R ∧
        (∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal R) from
          ⟨inferInstance, hprime⟩)
  have hcot_ne :
      Module.finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.CotangentSpace R) ≠ 0 := by
    intro hzero
    exact hfield (IsLocalRing.finrank_cotangentSpace_eq_zero_iff.mp hzero)
  have hcot :
      Module.finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.CotangentSpace R) = 1 :=
    le_antisymm hcot_le (Nat.one_le_iff_ne_zero.mpr hcot_ne)
  have hdim_lower : 1 ≤ ringKrullDim R := by
    apply Order.one_le_krullDim_iff.mpr
    obtain ⟨P, hP, hPprime⟩ := Ring.not_isField_iff_exists_prime.mp hfield
    refine ⟨⟨⊥, Ideal.bot_prime⟩, ⟨P, hPprime⟩, ?_⟩
    change (⊥ : Ideal R) < P
    exact bot_lt_iff_ne_bot.mpr hP
  refine ⟨inferInstance, ?_⟩
  rw [le_antisymm hdim hdim_lower, hcot]
  rfl

/-- Regularity at an actual scheme point. -/
def RegularPoint (X : Scheme.{u}) (x : X) : Prop :=
  RegularLocal (X.presheaf.stalk x)

/-- Normality supplies regularity at every point whose Noetherian stalk has
dimension at most one. Relating this local dimension to codimension is a
separate scheme-theoretic step. -/
theorem regularPoint_of_normal_of_ringKrullDim_le_one (X : Scheme.{u})
    (hnormal : IsNormalScheme X) (x : X)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1) : RegularPoint X x := by
  letI : IsDomain (X.presheaf.stalk x) := (hnormal x).1
  letI : IsIntegrallyClosed (X.presheaf.stalk x) := (hnormal x).2
  exact regularLocal_of_isIntegrallyClosed_of_ringKrullDim_le_one _ hdim

/-- The set of regular points; openness is a separate mathematical theorem. -/
def regularLocus (X : Scheme.{u}) : Set X := {x | RegularPoint X x}

/-- The singular locus consists exactly of points with nonregular local ring. -/
def singularLocus (X : Scheme.{u}) : Set X := {x | ¬ RegularPoint X x}

/-- The subtype of actual singular scheme points. -/
abbrev SingularPoints (X : Scheme.{u}) := {x : X // x ∈ singularLocus X}

@[simp]
theorem singularPoint_iff_not_regularLocal (X : Scheme.{u}) (x : X) :
    x ∈ singularLocus X ↔ ¬ RegularLocal (X.presheaf.stalk x) := Iff.rfl

theorem singularLocus_eq_compl_regularLocus (X : Scheme.{u}) :
    singularLocus X = (regularLocus X)ᶜ := rfl

/-- A singular point on a normal scheme with Noetherian stalk has local
dimension strictly greater than one. No dimension or finiteness convention
for the set of singular points enters this conclusion. -/
theorem singularPoint_one_lt_ringKrullDim (X : Scheme.{u})
    (hnormal : IsNormalScheme X) (x : X)
    [IsNoetherianRing (X.presheaf.stalk x)] (hx : x ∈ singularLocus X) :
    1 < ringKrullDim (X.presheaf.stalk x) := by
  apply lt_of_not_ge
  intro hdim
  exact hx (regularPoint_of_normal_of_ringKrullDim_le_one X hnormal x hdim)

/-- A point whose stalk is a field is nonsingular. -/
theorem not_singularPoint_of_stalk_field (X : Scheme.{u}) (x : X)
    (hfield : IsField (X.presheaf.stalk x)) : x ∉ singularLocus X := by
  exact not_not_intro (regularLocal_of_isField hfield)

/-- The generic point of an integral scheme is regular: its actual stalk is
the scheme's function field. This needs no surface or finiteness hypothesis. -/
theorem regularPoint_genericPoint (X : Scheme.{u}) [IsIntegral X] :
    RegularPoint X (genericPoint X) := by
  change RegularLocal X.functionField
  exact regularLocal_field X.functionField

/-- In particular the generic point cannot be a singular point. -/
theorem genericPoint_not_mem_singularLocus (X : Scheme.{u}) [IsIntegral X] :
    genericPoint X ∉ singularLocus X := by
  exact not_not_intro (regularPoint_genericPoint X)

/-- A closed set of closed points in a Noetherian sober space is finite.
Each member of a finite irreducible decomposition has a generic point; when
that point is closed, the entire member is its singleton. -/
theorem finite_of_isClosed_of_closedPoints {T : Type u} [TopologicalSpace T]
    [NoetherianSpace T] [QuasiSober T] {s : Set T} (hs : IsClosed s)
    (hpoints : ∀ x ∈ s, IsClosed ({x} : Set T)) : s.Finite := by
  obtain ⟨S, hfinite, hclosed, hirreducible, hcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  rw [hcover]
  apply hfinite.sUnion
  intro t ht
  let x := (hirreducible t ht).genericPoint
  have hx : IsGenericPoint x t :=
    (hirreducible t ht).isGenericPoint_genericPoint (hclosed t ht)
  have hxs : x ∈ s := by
    rw [hcover]
    exact Set.mem_sUnion.mpr ⟨t, ht, hx.mem⟩
  have ht_singleton : t = {x} := hx.def.symm.trans (hpoints x hxs).closure_eq
  rw [ht_singleton]
  exact Set.finite_singleton x

/-- The topological last step of singular-locus finiteness. The geometric
inputs, closedness of the locus and closedness of its points, must be proved
separately; this does not assert them for a normal surface. -/
theorem singularLocus_finite_of_isClosed_of_closedPoints (X : Scheme.{u})
    [NoetherianSpace X] (hclosed : IsClosed (singularLocus X))
    (hpoints : ∀ x ∈ singularLocus X, IsClosed ({x} : Set X)) :
    (singularLocus X).Finite :=
  finite_of_isClosed_of_closedPoints hclosed hpoints

/-- Enumerate the singular locus only after its finiteness has been proved. -/
def singularPointFinset (X : Scheme.{u}) (hfinite : (singularLocus X).Finite) : Finset X :=
  hfinite.toFinset

@[simp]
theorem mem_singularPointFinset (X : Scheme.{u}) (hfinite : (singularLocus X).Finite)
    (x : X) : x ∈ singularPointFinset X hfinite ↔
      ¬ RegularLocal (X.presheaf.stalk x) :=
  hfinite.mem_toFinset

/-- The number of distinct singular points, with a required finiteness proof. -/
def nSing (X : Scheme.{u}) (hfinite : (singularLocus X).Finite) : ℕ :=
  (singularPointFinset X hfinite).card

/-- Any finite set with the defining membership condition is the singular set. -/
theorem singularPointFinset_eq (X : Scheme.{u}) (hfinite : (singularLocus X).Finite)
    (s : Finset X) (hs : ∀ x : X, x ∈ s ↔ ¬ RegularLocal (X.presheaf.stalk x)) :
    singularPointFinset X hfinite = s := by
  classical
  ext x
  exact (mem_singularPointFinset X hfinite x).trans (hs x).symm

/-- The safe cardinal bound is equivalent to the public finite-set statement. -/
theorem nSing_le_iff_exists_finset (X : Scheme.{u})
    (hfinite : (singularLocus X).Finite) (bound : ℕ) :
    nSing X hfinite ≤ bound ↔
      ∃ s : Finset X,
        (∀ x : X, x ∈ s ↔ ¬ RegularLocal (X.presheaf.stalk x)) ∧ s.card ≤ bound := by
  constructor
  · intro h
    exact ⟨singularPointFinset X hfinite, mem_singularPointFinset X hfinite, h⟩
  · rintro ⟨s, hs, hcard⟩
    simpa only [nSing, singularPointFinset_eq X hfinite s hs] using hcard

/-- Conversely, an explicit finite singular set supplies the finiteness proof. -/
theorem singularLocus_finite_of_finset (X : Scheme.{u}) (s : Finset X)
    (hs : ∀ x : X, x ∈ s ↔ ¬ RegularLocal (X.presheaf.stalk x)) :
    (singularLocus X).Finite := by
  have heq : singularLocus X = (s : Set X) := by
    ext x
    exact (hs x).symm
  rw [heq]
  exact s.finite_toSet

end KltDP.Geometry
