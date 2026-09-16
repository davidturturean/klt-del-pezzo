import KltDP.Examples.FrobeniusContactBlowupsF29Full
import KltDP.Examples.FrobeniusMultiCentreClassTable

/-!
# F29 completion bundle, extended by the class table on the cluster opens of `S_{p,n}`

`f29_contact_blowups_full'` adds to the BRIEF22 bundle `f29_contact_blowups_full` the clause group
`ClassTableSPn`: on the cluster open `isoPreimage q n a i` of `S_{p,n}` over every centre, the
class table of the translated tower's top stage (`B`, `C_j`, `F̃`, `P`, the total transforms) and
the Picard fibre relation, between the classes of the translated tower's own curves restricted along
the open immersion `isoMap` (`FrobeniusMultiCentreClassTable`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples

open FrobeniusContactBlowupsF29Full FrobeniusMultiCentreClassTable

/-- Clause group (8): the class table and the Picard fibre relation on the cluster opens of
`S_{p,n}`, between the classes of the translated towers' curves restricted along `isoMap`. -/
abbrev ClassTableSPn (k : Type u) [Field k] (q n : ℕ) (a : Fin n → k) : Prop :=
  ∀ i : Fin n,
    (∀ m : ℕ, clusterStrictCurveClass q n a i m =
      (m + (q + 1)) • clusterFirstFiberTotalClass q n a i + clusterSecondFiberTotalClass q n a i -
        ∑ j : Fin (q + 1), clusterTotalExceptionalClass q n a i j) ∧
    (clusterStrictCurveClass q n a i 0 =
      (q + 1) • clusterFirstFiberTotalClass q n a i + clusterSecondFiberTotalClass q n a i -
        ∑ j : Fin (q + 1), clusterTotalExceptionalClass q n a i j) ∧
    (∀ (j : ℕ) (h : j + 1 + 1 ≤ q + 1), clusterOldExceptionalStrictClass q n a i j h =
      clusterTotalExceptionalClass q n a i ⟨j, by omega⟩ -
        clusterTotalExceptionalClass q n a i ⟨j + 1, by omega⟩) ∧
    (clusterFiberClass q n a i =
      clusterFiberZeroTotalClass q n a i -
        ∑ j : Fin (q + 1), clusterTotalExceptionalClass q n a i j) ∧
    (clusterTotalExceptionalClass q n a i (Fin.last q) = clusterStepExceptionalClass q n a i) ∧
    (clusterFiberPullbackClass q n a i =
      clusterFiberClass q n a i +
        ∑ j : Fin q, (j.val + 1) • clusterOldExceptionalStrictClass q n a i j.val (by omega) +
        (q + 1) • clusterTotalExceptionalClass q n a i (Fin.last q))

theorem classTableSPn (k : Type u) [Field k] (q n : ℕ) (a : Fin n → k) : ClassTableSPn k q n a :=
  fun i => clusterClassTable q n a i

/-- **F29 completion bundle, extended**: the seven clause groups of `f29_contact_blowups_full`
together with the class table on the cluster opens of `S_{p,n}`. -/
theorem f29_contact_blowups_full' (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ)
    [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) :
    Construction k q n a ha ∧ Configuration k q n a ha ∧ StrictTransforms k q n a ∧
    Fibres k q n a ∧ ClassTable k q ∧ CartierIdentity k ∧ ChainPicard k q n a ha ∧
    ClassTableSPn k q n a :=
  ⟨construction k q n a ha, configuration k q n a ha, strictTransforms k q n a ha,
    fibres k q n a ha, classTable k q, cartierIdentity k, chainPicard k q n a ha,
    classTableSPn k q n a⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_contact_blowups_full'_universe_check (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ)
    [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) : True := by
  have _ := f29_contact_blowups_full'.{u} k q n a ha
  trivial

end KltDP.Examples
