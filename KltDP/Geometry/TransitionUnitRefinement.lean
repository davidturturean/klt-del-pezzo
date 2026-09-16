/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors

Adapted from frenzymath/Algebraic-Geometry
9223d85c786394721963a9d642b08d066b72a594,
MainProjects/AlgebraicJacobian/PicardAlbanese/AlgebraicJacobian/Cohomology/
GluedSheafSubord.lean:57-382. The gluing uses the original structure sheaf;
all section equivalences are linear over the actual ring O(W), and the
result is an isomorphism in X.Modules. No external package is imported.
-/
import KltDP.Geometry.TransitionUnitRefinementCocycle
import KltDP.Geometry.TransitionUnitLocalTriviality

/-!
# Refinement of actual transition-unit module sheaves

A subordinate open cover V_i ≤ U_(σ i) carries the actual restrictions of
the original transition units. Restriction of matching families has an
inverse constructed by unique gluing in the original structure sheaf:
the old chart j is assembled from g_(j,σ i) t_i on W ∩ U_j ∩ V_i.
The proved inverse and restriction identities yield an actual module-sheaf
isomorphism. The final specialization constructs the target units by the
original restriction homomorphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) {J I : Type u} {U : J → X.Opens}
  {g : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ}
  {V : I → X.Opens} {g' : ∀ i i' : I, Γ(X, V i ⊓ V i')ˣ} {σ : I → J}

/-- **Componentwise restriction preserves matching**: restricting the `σ i`-th
component of a `U`-glued family to `W ⊓ V i` yields a `V`-glued family for the
restricted multipliers. -/
lemma subordinationFwd_mem (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    {W : X.Opens} {s : ∀ j : J, Γ(X, W ⊓ U j)} (hs : s ∈ sections X U g W) :
    (fun i => res X (inf_le_inf_left W (hσ i)) (s (σ i)))
      ∈ sections X V g' W := by
  intro i i'
  have key := congrArg (res X (le_inf (le_inf (inf_le_left.trans inf_le_left)
      ((inf_le_left.trans inf_le_right).trans (hσ i)))
      (inf_le_right.trans (hσ i')) :
      W ⊓ V i ⊓ V i' ≤ W ⊓ U (σ i) ⊓ U (σ i'))) (hs (σ i) (σ i'))
  rw [map_mul] at key
  rw [hg' i i']
  simp only [res_res] at key ⊢
  exact key

/-- **The forward map of the subordination**: componentwise restriction of glued
sections along `W ⊓ V i ≤ W ⊓ U (σ i)`, as an original section-ring linear map. -/
noncomputable def subordinationFwd (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (W : X.Opens) :
    ↥(sections X U g W) →ₗ[Γ(X, W)] ↥(sections X V g' W) where
  toFun s := ⟨fun i =>
      res X (inf_le_inf_left W (hσ i)) (s.val (σ i)),
    subordinationFwd_mem X hσ hg' s.property⟩
  map_add' s t := Subtype.ext (funext fun i =>
    map_add (res X (inf_le_inf_left W (hσ i))) (s.val (σ i)) (t.val (σ i)))
  map_smul' r s := by
    apply Subtype.ext
    funext i
    change res X (inf_le_inf_left W (hσ i))
        (res X (inf_le_left : W ⊓ U (σ i) ≤ W) r * s.val (σ i)) =
      res X (inf_le_left : W ⊓ V i ≤ W) r *
        res X (inf_le_inf_left W (hσ i)) (s.val (σ i))
    rw [map_mul, res_res]

@[simp]
lemma subordinationFwd_val (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    {W : X.Opens} (s : ↥(sections X U g W)) (i : I) :
    (subordinationFwd X hσ hg' W s).val i
      = res X (inf_le_inf_left W (hσ i)) (s.val (σ i)) :=
  rfl

/-! ## The inverse assembly -/

variable (g) in
/-- The `(j, i)`-th candidate of the inverse assembly: over `W ⊓ U j ⊓ V i`, the
`j`-th component of the assembled `U`-glued family is `g j (σ i) · t i`. -/
noncomputable def subordinationCandidate (hσ : ∀ i : I, V i ≤ U (σ i)) {W : X.Opens}
    (t : ∀ i : I, Γ(X, W ⊓ V i)) (j : J) (i : I) : Γ(X, W ⊓ U j ⊓ V i) :=
  res X (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans (hσ i)) :
      W ⊓ U j ⊓ V i ≤ U j ⊓ U (σ i)) (g j (σ i) : Γ(X, U j ⊓ U (σ i)))
    * res X (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W ⊓ U j ⊓ V i ≤ W ⊓ V i) (t i)

/-- **The candidates are compatible** (the cocycle law at `(j, σ i, σ i')` against the
matching of `t`): the candidates `g j (σ i) · t i` agree on the pairwise overlaps of
the cover `{W ⊓ U j ⊓ V i}_i`. -/
lemma subordinationCandidate_compatible (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : IsCocycle X U g)
    {W : X.Opens} {t : ∀ i : I, Γ(X, W ⊓ V i)}
    (ht : t ∈ sections X V g' W) (j : J) (i i' : I) :
    res X (inf_le_left : (W ⊓ U j ⊓ V i) ⊓ (W ⊓ U j ⊓ V i') ≤ W ⊓ U j ⊓ V i)
        (subordinationCandidate X g hσ t j i)
      = res X inf_le_right (subordinationCandidate X g hσ t j i') := by
  -- the matching of `t`, restricted to the overlap and rewritten through `hg'`
  have hmatch := congrArg (res X (le_inf (le_inf
      (inf_le_left.trans (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right))
      (inf_le_right.trans inf_le_right) :
      (W ⊓ U j ⊓ V i) ⊓ (W ⊓ U j ⊓ V i') ≤ W ⊓ V i ⊓ V i')) (ht i i')
  rw [map_mul, hg' i i'] at hmatch
  simp only [res_res] at hmatch
  -- the cocycle law at `(j, σ i, σ i')`, restricted to the overlap
  have hcoc := IsCocycle.mul_res_of_le X U g hc (le_inf (le_inf
      (inf_le_left.trans (inf_le_left.trans inf_le_right))
      ((inf_le_left.trans inf_le_right).trans (hσ i)))
      ((inf_le_right.trans inf_le_right).trans (hσ i')) :
      (W ⊓ U j ⊓ V i) ⊓ (W ⊓ U j ⊓ V i') ≤ U j ⊓ U (σ i) ⊓ U (σ i'))
  rw [subordinationCandidate, subordinationCandidate, map_mul, map_mul]
  simp only [res_res]


  rw [hmatch, ← mul_assoc, hcoc]

/-- **Existence and uniqueness of the assembled component**: the candidates
`g j (σ i) · t i` glue to a unique section over `W ⊓ U j` (the family `V` covers). -/
lemma subordinationSection_existsUnique (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : IsCocycle X U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} {t : ∀ i : I, Γ(X, W ⊓ V i)}
    (ht : t ∈ sections X V g' W) (j : J) :
    ∃! sj : Γ(X, W ⊓ U j), ∀ i : I,
      res X (inf_le_left : W ⊓ U j ⊓ V i ≤ W ⊓ U j) sj
        = subordinationCandidate X g hσ t j i := by
  have hcover : W ⊓ U j ≤ ⨆ i : I, W ⊓ U j ⊓ V i := fun z hz => by
    obtain ⟨i, hi⟩ := hcov z
    exact Opens.mem_iSup.mpr ⟨i, hz, hi⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.val
      (fun i : I => W ⊓ U j ⊓ V i) (fun i => subordinationCandidate X g hσ t j i) := by
    intro i i'
    exact subordinationCandidate_compatible X hσ hg' hc ht j i i'
  obtain ⟨sj, hsj, hsju⟩ := TopCat.Sheaf.existsUnique_gluing'
    (X := (X : TopCat)) (C := CommRingCat.{u}) X.sheaf
    (fun i : I => W ⊓ U j ⊓ V i) (W ⊓ U j)
    (fun i => homOfLE inf_le_left) hcover
    (fun i => subordinationCandidate X g hσ t j i) hcompat
  exact ⟨sj, fun i => hsj i, fun y hy => hsju y fun i => hy i⟩

/-- The assembled `j`-th component of the inverse of the subordination map. -/
noncomputable def subordinationSection (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : IsCocycle X U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} {t : ∀ i : I, Γ(X, W ⊓ V i)}
    (ht : t ∈ sections X V g' W) (j : J) : Γ(X, W ⊓ U j) :=
  (subordinationSection_existsUnique X hσ hg' hc hcov ht j).exists.choose

/-- The defining property of the assembled component. -/
lemma subordinationSection_res (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : IsCocycle X U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} {t : ∀ i : I, Γ(X, W ⊓ V i)}
    (ht : t ∈ sections X V g' W) (j : J) (i : I) :
    res X (inf_le_left : W ⊓ U j ⊓ V i ≤ W ⊓ U j)
        (subordinationSection X hσ hg' hc hcov ht j)
      = subordinationCandidate X g hσ t j i :=
  (subordinationSection_existsUnique X hσ hg' hc hcov ht j).exists.choose_spec i

/-- Uniqueness of the assembled component. -/
lemma subordinationSection_unique (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : IsCocycle X U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} {t : ∀ i : I, Γ(X, W ⊓ V i)}
    (ht : t ∈ sections X V g' W) (j : J) {sj : Γ(X, W ⊓ U j)}
    (hsj : ∀ i : I, res X (inf_le_left : W ⊓ U j ⊓ V i ≤ W ⊓ U j) sj
      = subordinationCandidate X g hσ t j i) :
    sj = subordinationSection X hσ hg' hc hcov ht j :=
  (subordinationSection_existsUnique X hσ hg' hc hcov ht j).unique hsj
    (subordinationSection_res X hσ hg' hc hcov ht j)

/-- Separation over the subordinated cover: two sections of an open agreeing on every
`· ⊓ V i` agree. -/
private lemma sectionExt (hcov : ∀ z : X, ∃ i : I, z ∈ V i) {O : X.Opens}
    {s s' : Γ(X, O)}
    (h : ∀ i : I, res X (inf_le_left : O ⊓ V i ≤ O) s
      = res X inf_le_left s') : s = s' := by
  apply TopCat.Sheaf.eq_of_locally_eq' (X := (X : TopCat)) (C := CommRingCat.{u})
    X.sheaf (fun i : I => O ⊓ V i) O (fun i => homOfLE inf_le_left)
    (fun z hz => by
      obtain ⟨i, hi⟩ := hcov z
      exact Opens.mem_iSup.mpr ⟨i, hz, hi⟩)
  exact h

/-- **The assembled components match through `g`**: the inverse assembly is a
`U`-glued family (checked on the subordinated cover through the cocycle law at
`(j, j', σ i)`). -/
lemma subordinationSection_mem (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : IsCocycle X U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} {t : ∀ i : I, Γ(X, W ⊓ V i)}
    (ht : t ∈ sections X V g' W) :
    (fun j => subordinationSection X hσ hg' hc hcov ht j)
      ∈ sections X U g W := by
  intro j j'
  refine sectionExt X hcov (fun i => ?_)
  -- the left side restricts to the `(j, i)`-th candidate
  have hL := congrArg (res X (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      W ⊓ U j ⊓ U j' ⊓ V i ≤ W ⊓ U j ⊓ V i))
    (subordinationSection_res X hσ hg' hc hcov ht j i)
  -- the right side restricts to the `(j', i)`-th candidate
  have hR := congrArg (res X (le_inf (le_inf
      (inf_le_left.trans (inf_le_left.trans inf_le_left))
      (inf_le_left.trans inf_le_right)) inf_le_right :
      W ⊓ U j ⊓ U j' ⊓ V i ≤ W ⊓ U j' ⊓ V i))
    (subordinationSection_res X hσ hg' hc hcov ht j' i)
  rw [subordinationCandidate, map_mul] at hL hR
  simp only [res_res] at hL hR
  -- the cocycle law at `(j, j', σ i)`
  have hcoc := IsCocycle.mul_res_of_le X U g hc (le_inf (le_inf
      (inf_le_left.trans (inf_le_left.trans inf_le_right)) (inf_le_left.trans inf_le_right))
      (inf_le_right.trans (hσ i)) :
      W ⊓ U j ⊓ U j' ⊓ V i ≤ U j ⊓ U j' ⊓ U (σ i))
  change res X _ (res X (inf_le_left : W ⊓ U j ⊓ U j' ≤ W ⊓ U j)
      (subordinationSection X hσ hg' hc hcov ht j))
    = res X _ (res X (inclCoc X U W j j') (g j j' : Γ(X, U j ⊓ U j'))
        * res X (inclSnd X U W j j') (subordinationSection X hσ hg' hc hcov ht j'))
  rw [map_mul]
  simp only [res_res]
  rw [hL, hR, ← mul_assoc, hcoc]

/-! ## The equivalence -/

/-- **Left inverse**: the assembly of the componentwise restriction of a `U`-glued
family recovers its components (by the uniqueness of the gluing — `s j` restricts to
every candidate of its own image, through the matching of `s` at `(j, σ i)`). -/
lemma subordinationSection_fwd (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : IsCocycle X U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} (s : ↥(sections X U g W)) (j : J) :
    subordinationSection X hσ hg' hc hcov
        (subordinationFwd_mem X hσ hg' s.property) j = s.val j := by
  refine (subordinationSection_unique X hσ hg' hc hcov
    (subordinationFwd_mem X hσ hg' s.property) j (fun i => ?_)).symm
  have key := congrArg (res X (le_inf (le_inf
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
      (inf_le_right.trans (hσ i)) :
      W ⊓ U j ⊓ V i ≤ W ⊓ U j ⊓ U (σ i))) (s.property j (σ i))
  rw [map_mul] at key
  rw [subordinationCandidate]
  simp only [res_res] at key ⊢
  exact key

/-- **Right inverse**: the componentwise restriction of the assembly recovers the
`V`-glued family (by separation — over `W ⊓ V i ⊓ V i'` both sides are
`g (σ i) (σ i') · t i'`, through the defining property of the assembly and the
matching of `t`). -/
lemma subordinationFwd_assembled (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : IsCocycle X U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} (t : ↥(sections X V g' W)) (i : I) :
    res X (inf_le_inf_left W (hσ i))
        (subordinationSection X hσ hg' hc hcov t.property (σ i)) = t.val i := by
  refine sectionExt X hcov (fun i' => ?_)
  -- the restriction of the assembly is `g (σ i) (σ i') · t i'`
  have hL := congrArg (res X (le_inf
      (le_inf (inf_le_left.trans inf_le_left)
        ((inf_le_left.trans inf_le_right).trans (hσ i))) inf_le_right :
      W ⊓ V i ⊓ V i' ≤ W ⊓ U (σ i) ⊓ V i'))
    (subordinationSection_res X hσ hg' hc hcov t.property (σ i) i')
  rw [subordinationCandidate, map_mul] at hL
  simp only [res_res] at hL
  -- the matching of `t` gives the same value
  have hmatch := t.property i i'
  rw [hg' i i'] at hmatch
  simp only [res_res] at hmatch
  simp only [res_res]
  rw [hL, hmatch]

/-- **The subordination equivalence of glued sections**: componentwise restriction
along `σ`, with inverse the candidate assembly. -/
noncomputable def subordinationEquiv (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : IsCocycle X U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    (W : X.Opens) :
    ↥(sections X U g W) ≃ₗ[Γ(X, W)] ↥(sections X V g' W) :=
  LinearEquiv.ofBijective (subordinationFwd X hσ hg' W)
    (Function.bijective_iff_has_inverse.mpr
      ⟨fun t => ⟨fun j => subordinationSection X hσ hg' hc hcov t.property j,
          subordinationSection_mem X hσ hg' hc hcov t.property⟩,
        fun s => Subtype.ext (funext fun j =>
          subordinationSection_fwd X hσ hg' hc hcov s j),
        fun t => Subtype.ext (funext fun i =>
          subordinationFwd_assembled X hσ hg' hc hcov t i)⟩)

@[simp]
lemma subordinationEquiv_val (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : IsCocycle X U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} (s : ↥(sections X U g W)) (i : I) :
    (subordinationEquiv X hσ hg' hc hcov W s).val i
      = res X (inf_le_inf_left W (hσ i)) (s.val (σ i)) :=
  rfl

/-- The subordination equivalence commutes with restriction (the forward map is
componentwise restriction). -/
lemma subordinationEquiv_restrict (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : IsCocycle X U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W' W : X.Opens} (h : W' ≤ W) (s : ↥(sections X U g W)) :
    subordinationEquiv X hσ hg' hc hcov W' (restrict X U g h s)
      = restrict X V g' h (subordinationEquiv X hσ hg' hc hcov W s) := by
  refine Subtype.ext (funext fun i => ?_)
  rw [subordinationEquiv_val, restrict_val, restrict_val,
    subordinationEquiv_val]
  simp only [res_res]

/-- The inverse of the section equivalence is the explicitly glued family. -/
lemma subordinationEquiv_symm_val (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : IsCocycle X U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} (t : sections X V g' W) (j : J) :
    ((subordinationEquiv X hσ hg' hc hcov W).symm t).val j =
      subordinationSection X hσ hg' hc hcov t.property j := by
  let s : sections X U g W :=
    ⟨fun j => subordinationSection X hσ hg' hc hcov t.property j,
      subordinationSection_mem X hσ hg' hc hcov t.property⟩
  have hs : subordinationEquiv X hσ hg' hc hcov W s = t := by
    apply Subtype.ext
    funext i
    exact subordinationFwd_assembled X hσ hg' hc hcov t i
  have he : (subordinationEquiv X hσ hg' hc hcov W).symm t = s := by
    apply (subordinationEquiv X hσ hg' hc hcov W).injective
    rw [LinearEquiv.apply_symm_apply, hs]
  exact congrArg (fun q : sections X U g W => q.val j) he

/-- The actual module-sheaf isomorphism for prescribed restricted transition units. -/
def subordinationIso (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : IsCocycle X U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i) :
    moduleSheaf X U g ≅ moduleSheaf X V g' := by
  apply (_root_.SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
  refine _root_.PresheafOfModules.isoMk
    (fun W => (subordinationEquiv X hσ hg' hc hcov W.unop).toModuleIso) ?_
  intro A B f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change subordinationEquiv X hσ hg' hc hcov B.unop (restrict X U g f.unop.le s) =
    restrict X V g' f.unop.le (subordinationEquiv X hσ hg' hc hcov A.unop s)
  exact subordinationEquiv_restrict X hσ hg' hc hcov f.unop.le s

@[simp]
theorem subordinationIso_hom_app_val (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : IsCocycle X U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    (W : X.Opensᵒᵖ) (s : sections X U g W.unop) (i : I) :
    ((subordinationIso X hσ hg' hc hcov).hom.val.app W s).val i =
      res X (inf_le_inf_left W.unop (hσ i)) (s.val (σ i)) := rfl

/-- The refinement isomorphism with the target units constructed by actual pullback. -/
def refinementIso (U : J → X.Opens) (g : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ)
    (V : I → X.Opens) (σ : I → J) (hσ : ∀ i : I, V i ≤ U (σ i))
    (hc : IsCocycle X U g) (hV : (⨆ i, V i) = ⊤) :
    moduleSheaf X U g ≅ moduleSheaf X V (refinedUnits X U g V σ hσ) :=
  subordinationIso X hσ (fun i i' => refinedUnits_val X U g V σ hσ i i') hc
    (fun z => Opens.mem_iSup.mp (show z ∈ ⨆ i, V i from by rw [hV]; trivial))

/-- The constructed refinement map is exactly restriction along the chosen chart map. -/
@[simp]
theorem refinementIso_hom_app_val
    (U : J → X.Opens) (g : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ)
    (V : I → X.Opens) (σ : I → J) (hσ : ∀ i : I, V i ≤ U (σ i))
    (hc : IsCocycle X U g) (hV : (⨆ i, V i) = ⊤)
    (W : X.Opensᵒᵖ) (s : sections X U g W.unop) (i : I) :
    ((refinementIso X U g V σ hσ hc hV).hom.val.app W s).val i =
      res X (inf_le_inf_left W.unop (hσ i)) (s.val (σ i)) := rfl

end KltDP.Geometry.TransitionUnitGluing
