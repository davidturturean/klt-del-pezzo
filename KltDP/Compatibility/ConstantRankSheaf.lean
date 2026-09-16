import KltDP.Compatibility.InvertibleModuleSheaf
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Constant finite rank for actual module sheaves

The rank is the common cardinality of finite local bases in the existing
`LocalGeneratorsData`. The covering, generating sections and presentation
morphisms are unchanged. Reindexing those bases gives actual trivializations
by the free sheaf on `Fin n`; conversely, such trivializations give the same
local-basis predicate. Rank one is equivalent to the existing invertibility
predicate.

These definitions concern local freeness only. They make no assertion about
cohomology, degrees or tensor-degree additivity.
-/

noncomputable section

open CategoryTheory

universe u v u₁

namespace KltDP.SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrp.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  {M N : _root_.SheafOfModules.{u} R} {n : ℕ}

/-- The actual presentation maps are local bases, each with `n` elements.
Finiteness is explicit, including at rank zero. -/
structure LocalGeneratorsData.HasConstantRank
    (q : _root_.SheafOfModules.LocalGeneratorsData M) (n : ℕ) : Prop where
  isLocallyFreeData : q.IsLocallyFreeData
  basisFinite (i : q.I) : Finite (q.generators i).I
  basisCard (i : q.I) : Nat.card (q.generators i).I = n

/-- Local freeness of constant finite rank for the original module sheaf. -/
class IsLocallyFreeOfRank (M : _root_.SheafOfModules.{u} R) (n : ℕ) : Prop where
  exists_localGeneratorsData :
    ∃ q : _root_.SheafOfModules.LocalGeneratorsData M, LocalGeneratorsData.HasConstantRank q n

/-- Forgetting the common rank retains the same local bases. -/
theorem IsLocallyFreeOfRank.isLocallyFree (h : IsLocallyFreeOfRank M n) :
    M.IsLocallyFree := by
  obtain ⟨q, hq⟩ := h.exists_localGeneratorsData
  exact ⟨q, hq.isLocallyFreeData⟩

/-- The same finite bases prove the existing finite-type predicate. -/
theorem IsLocallyFreeOfRank.isFiniteType (h : IsLocallyFreeOfRank M n) :
    M.IsFiniteType := by
  obtain ⟨q, hq⟩ := h.exists_localGeneratorsData
  exact ⟨q, hq.basisFinite⟩

/-- Rank one on a given local basis is exactly its original singleton-basis
condition, with no replacement cover. -/
theorem LocalGeneratorsData.hasConstantRank_one_iff_isInvertible
    (q : _root_.SheafOfModules.LocalGeneratorsData M) :
    LocalGeneratorsData.HasConstantRank q 1 ↔ LocalGeneratorsData.IsInvertible q := by
  constructor
  · intro hq
    exact {
      isLocallyFreeData := hq.isLocallyFreeData
      basisNonempty := fun i => (Nat.card_eq_one_iff_unique.mp (hq.basisCard i)).2
      basisSubsingleton := fun i => (Nat.card_eq_one_iff_unique.mp (hq.basisCard i)).1 }
  · intro hq
    refine ⟨hq.isLocallyFreeData, ?_, ?_⟩
    · intro i
      letI := hq.basisSubsingleton i
      infer_instance
    · intro i
      letI := hq.basisNonempty i
      letI := hq.basisSubsingleton i
      exact Nat.card_unique

/-- The constant-rank interface agrees with the previously constructed
invertibility predicate at rank one. -/
theorem isLocallyFreeOfRank_one_iff_isInvertible :
    IsLocallyFreeOfRank M 1 ↔ IsInvertible M := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := h.exists_localGeneratorsData
    exact ⟨q, (LocalGeneratorsData.hasConstantRank_one_iff_isInvertible q).mp hq⟩
  · intro h
    obtain ⟨q, hq⟩ := h.exists_isInvertible
    exact ⟨q, (LocalGeneratorsData.hasConstantRank_one_iff_isInvertible q).mpr hq⟩

instance IsInvertible.isLocallyFreeOfRank (M : _root_.SheafOfModules.{u} R)
    [IsInvertible M] : IsLocallyFreeOfRank M 1 :=
  isLocallyFreeOfRank_one_iff_isInvertible.mpr inferInstance

/-- Transporting the original generators along a sheaf isomorphism preserves
the same basis indexing types, their cardinalities and the covering. -/
theorem LocalGeneratorsData.HasConstantRank.ofIso
    {q : _root_.SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.HasConstantRank q n) (e : M ≅ N) :
    LocalGeneratorsData.HasConstantRank (LocalGeneratorsData.ofIso q e) n where
  isLocallyFreeData := {
    isIso := by
      intro i
      change IsIso ((q.generators i).ofEpi
        ((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom).π
      rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
      letI := hq.isLocallyFreeData.isIso i
      infer_instance }
  basisFinite i := hq.basisFinite i
  basisCard i := hq.basisCard i

theorem IsLocallyFreeOfRank.of_iso (h : IsLocallyFreeOfRank M n) (e : M ≅ N) :
    IsLocallyFreeOfRank N n := by
  obtain ⟨q, hq⟩ := h.exists_localGeneratorsData
  exact ⟨LocalGeneratorsData.ofIso q e, hq.ofIso e⟩

theorem isLocallyFreeOfRank_iff_of_iso (e : M ≅ N) :
    IsLocallyFreeOfRank M n ↔ IsLocallyFreeOfRank N n :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

/-- An actual atlas with free sheaf of rank `n` on each member. -/
structure ConstantRankTrivializations (M : _root_.SheafOfModules.{u} R) (n : ℕ) where
  I : Type u₁
  X : I → C
  coversTop : J.CoversTop X
  iso (i : I) :
    _root_.SheafOfModules.free (R := R.over (X i)) (ULift.{u} (Fin n)) ≅ M.over (X i)

/-- Reindex the finite original basis by `Fin n`, including the empty basis
when `n = 0`. -/
def LocalGeneratorsData.HasConstantRank.basisEquiv
    {q : _root_.SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.HasConstantRank q n) (i : q.I) :
    ULift.{u} (Fin n) ≃ (q.generators i).I := by
  letI := hq.basisFinite i
  letI := Fintype.ofFinite (q.generators i).I
  let e : (q.generators i).I ≃ Fin n :=
    Fintype.equivFinOfCardEq (by
      simpa only [Nat.card_eq_fintype_card] using hq.basisCard i)
  exact Equiv.ulift.trans e.symm

/-- The reindexed free sheaf maps by the original isomorphic presentation. -/
def LocalGeneratorsData.HasConstantRank.trivializationIso
    {q : _root_.SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.HasConstantRank q n) (i : q.I) :
    _root_.SheafOfModules.free (R := R.over (q.X i)) (ULift.{u} (Fin n)) ≅
      M.over (q.X i) := by
  letI := hq.isLocallyFreeData.isIso i
  exact ((_root_.SheafOfModules.freeFunctor (R := R.over (q.X i))).mapIso
    (hq.basisEquiv i).toIso) ≪≫ asIso (q.generators i).π

/-- Choose the atlas proved to exist by the local-basis predicate. -/
def IsLocallyFreeOfRank.trivializations (h : IsLocallyFreeOfRank M n) :
    ConstantRankTrivializations M n := by
  let q := h.exists_localGeneratorsData.choose
  let hq := h.exists_localGeneratorsData.choose_spec
  exact {
    I := q.I
    X := q.X
    coversTop := q.coversTop
    iso := hq.trivializationIso }

/-- The standard sections transported through an actual atlas are finite
local bases of the stated cardinality. -/
theorem ConstantRankTrivializations.isLocallyFreeOfRank
    (t : ConstantRankTrivializations M n) : IsLocallyFreeOfRank M n := by
  let q : _root_.SheafOfModules.LocalGeneratorsData M := {
    I := t.I
    X := t.X
    coversTop := t.coversTop
    generators i :=
      (_root_.SheafOfModules.free.generatingSections
        (R := R.over (t.X i)) (ULift.{u} (Fin n))).ofEpi (t.iso i).hom }
  refine ⟨q, ⟨⟨?_⟩, ?_, ?_⟩⟩
  · intro i
    change IsIso ((_root_.SheafOfModules.free.generatingSections
      (R := R.over (t.X i)) (ULift.{u} (Fin n))).ofEpi (t.iso i).hom).π
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π,
      _root_.SheafOfModules.free.generatingSections_π]
    infer_instance
  · intro i
    change Finite (ULift.{u} (Fin n))
    infer_instance
  · intro i
    change Nat.card (ULift.{u} (Fin n)) = n
    simp only [Nat.card_eq_fintype_card, Fintype.card_ulift, Fintype.card_fin]

/-- Constant finite rank is precisely local isomorphism with a fixed
standard finite free sheaf. -/
theorem nonempty_constantRankTrivializations_iff :
    Nonempty (ConstantRankTrivializations M n) ↔ IsLocallyFreeOfRank M n :=
  ⟨fun ⟨t⟩ => t.isLocallyFreeOfRank, fun h => ⟨h.trivializations⟩⟩

end KltDP.SheafOfModules
