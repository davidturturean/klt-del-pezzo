import KltDP.Codes.IntegralNodeCode
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Coordinates on an integral lattice modulo doubles

An actual finite integral basis gives coordinates on the actual additive
quotient `M / (2 M)`. The coordinate reduction map has kernel exactly the
subgroup of doubles. Every binary coordinate vector has a preimage obtained
by taking its canonical integer representatives, so the descended map is a
linear equivalence over `ZMod 2`.

The quotient and its binary scalar action are the existing `Codes.ModTwo`
and `Codes.modTwoModule`. No vector-space identification is assumed and no
alternative quotient is substituted. These statements concern integral
modules; they do not identify a geometric Picard group or descend a surface
intersection form.
-/

namespace KltDP.Lattices.ModTwoCoordinates

open KltDP.Codes

variable {M ι : Type*} [AddCommGroup M] [Fintype ι]

/-- Reduce the actual integral basis coordinates modulo two. -/
noncomputable def coordinateReduction (b : Basis ι ℤ M) : M →+ (ι → ZMod 2) where
  toFun x i := (b.repr x i : ZMod 2)
  map_zero' := by
    funext i
    simp
  map_add' := by
    intro x y
    funext i
    simp

omit [Fintype ι] in
@[simp]
theorem coordinateReduction_apply (b : Basis ι ℤ M) (x : M) (i : ι) :
    coordinateReduction b x i = (b.repr x i : ZMod 2) := rfl

/-- Canonical representatives: each binary coordinate is replaced by its value in `{0,1}`. -/
noncomputable def integerRepresentative (b : Basis ι ℤ M) (x : ι → ZMod 2) : M :=
  b.equivFun.symm (fun i => ((x i).val : ℤ))

/-- The chosen integral representative reduces to the specified binary coordinates. -/
theorem coordinateReduction_integerRepresentative (b : Basis ι ℤ M) (x : ι → ZMod 2) :
    coordinateReduction b (integerRepresentative b x) = x := by
  funext i
  change ((b.equivFun (b.equivFun.symm (fun j => ((x j).val : ℤ))) i : ℤ) : ZMod 2) = x i
  rw [LinearEquiv.apply_symm_apply]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Coordinate reduction is surjective with the preceding explicit representatives. -/
theorem coordinateReduction_surjective (b : Basis ι ℤ M) :
    Function.Surjective (coordinateReduction b) :=
  fun x => ⟨integerRepresentative b x, coordinateReduction_integerRepresentative b x⟩

/-- Vanishing coordinates are exactly integral two-divisibility.

For the reverse construction, integer division by two is applied to each
coordinate; divisibility proves that the resulting half has double `x`.
-/
theorem coordinateReduction_eq_zero_iff (b : Basis ι ℤ M) (x : M) :
    coordinateReduction b x = 0 ↔ ∃ y : M, y + y = x := by
  constructor
  · intro hx
    have hd : ∀ i, (2 : ℤ) ∣ b.repr x i := by
      intro i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (b.repr x i) 2).mp (congrFun hx i)
    refine ⟨b.equivFun.symm (fun i => b.repr x i / 2), ?_⟩
    apply b.equivFun.injective
    rw [map_add, LinearEquiv.apply_symm_apply]
    funext i
    change b.repr x i / 2 + b.repr x i / 2 = b.repr x i
    simpa only [mul_two] using Int.ediv_mul_cancel (hd i)
  · rintro ⟨y, rfl⟩
    rw [map_add]
    funext i
    exact CharTwo.add_self_eq_zero (coordinateReduction b y i)

/-- Equality with the existing subgroup of doubles, not a new kernel predicate. -/
theorem coordinateReduction_ker (b : Basis ι ℤ M) :
    (coordinateReduction b).ker = twiceSubgroup M := by
  ext x
  exact coordinateReduction_eq_zero_iff b x

/-- Descend coordinate reduction to the existing quotient and its binary scalar action. -/
noncomputable def modTwoCoordinates (b : Basis ι ℤ M) :
    ModTwo M →ₗ[ZMod 2] (ι → ZMod 2) :=
  (QuotientAddGroup.lift (twiceSubgroup M) (coordinateReduction b)
    (coordinateReduction_ker b).symm.le).toZModLinearMap 2

@[simp]
theorem modTwoCoordinates_mk (b : Basis ι ℤ M) (x : M) :
    modTwoCoordinates b (modTwoMk M x) = fun i => (b.repr x i : ZMod 2) := rfl

/-- The descended map is injective because its original kernel was exactly the doubles. -/
theorem modTwoCoordinates_injective (b : Basis ι ℤ M) :
    Function.Injective (modTwoCoordinates b) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro q hq
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective (twiceSubgroup M) q
  change modTwoMk M x = q at hx
  subst q
  apply (modTwoMk_eq_zero_iff x).mpr
  exact (coordinateReduction_eq_zero_iff b x).mp hq

/-- Every quotient coordinate vector comes from its canonical integral representative. -/
theorem modTwoCoordinates_surjective (b : Basis ι ℤ M) :
    Function.Surjective (modTwoCoordinates b) := by
  intro x
  refine ⟨modTwoMk M (integerRepresentative b x), ?_⟩
  exact coordinateReduction_integerRepresentative b x

/-- An actual coordinate equivalence for the quotient of the lattice by its doubles. -/
noncomputable def modTwoCoordinatesEquiv (b : Basis ι ℤ M) :
    ModTwo M ≃ₗ[ZMod 2] (ι → ZMod 2) :=
  LinearEquiv.ofBijective (modTwoCoordinates b)
    ⟨modTwoCoordinates_injective b, modTwoCoordinates_surjective b⟩

@[simp]
theorem modTwoCoordinatesEquiv_mk (b : Basis ι ℤ M) (x : M) :
    modTwoCoordinatesEquiv b (modTwoMk M x) = fun i => (b.repr x i : ZMod 2) := rfl

/-- The inverse equivalence is represented by the canonical integer coordinate lift. -/
theorem modTwoCoordinatesEquiv_symm_apply (b : Basis ι ℤ M) (x : ι → ZMod 2) :
    (modTwoCoordinatesEquiv b).symm x = modTwoMk M (integerRepresentative b x) := by
  apply (modTwoCoordinatesEquiv b).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (coordinateReduction_integerRepresentative b x).symm

/-- Finiteness is a conclusion of the constructed equivalence. -/
theorem modTwo_finite (b : Basis ι ℤ M) : Finite (ModTwo M) :=
  Finite.of_equiv (ι → ZMod 2) (modTwoCoordinatesEquiv b).symm.toEquiv

/-- Finite-dimensionality follows from the injective coordinate map. -/
theorem modTwo_finiteDimensional (b : Basis ι ℤ M) :
    FiniteDimensional (ZMod 2) (ModTwo M) :=
  FiniteDimensional.of_injective (modTwoCoordinates b) (modTwoCoordinates_injective b)

/-- Its binary dimension is the cardinality of the supplied integral basis. -/
theorem modTwo_finrank (b : Basis ι ℤ M) :
    Module.finrank (ZMod 2) (ModTwo M) = Fintype.card ι :=
  (modTwoCoordinatesEquiv b).finrank_eq.trans
    (Module.finrank_eq_card_basis (Pi.basisFun (ZMod 2) ι))

end KltDP.Lattices.ModTwoCoordinates
