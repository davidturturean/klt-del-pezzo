import KltDP.Geometry.SeparatedAffineIntersections

/-!
# Actual affine refinements of arbitrary open covers

Every affine subopen of an original chart is retained as an index. The
existing affine-open basis theorem proves that these subopens cover the
original scheme. In particular, no affine triviality of an arbitrary
original chart is assumed. Separatedness supplies the pair and triple
intersection affineness required by the quadratic scheme-gluing atlas.

Reuse: pinned `isBasis_affine_open` and its `exists_subset_of_mem_open`
application in `AffineScheme.lean:904`; the newer official file at revision
80cbd0498ab39e21d24d6730b3f932cec672a702 retains the affine-open basis
(Apache 2.0). No newer implementation or dependency is imported.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.AffineOpenRefinement

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)

/-- An original chart together with an actual affine subopen. -/
def Index : Type u := Σ i : ι, {V : X.Opens // IsAffineOpen V ∧ V ≤ U i}

/-- The actual subordinate affine opens. -/
def opens (i : Index X U) : X.Opens := i.2.val

/-- The original chart retained by each refinement index. -/
def original (i : Index X U) : ι := i.1

theorem affine (i : Index X U) : IsAffineOpen (opens X U i) := i.2.property.1

theorem subordinate (i : Index X U) : opens X U i ≤ U (original X U i) :=
  i.2.property.2

/-- Affine subopens really cover an arbitrary original open cover. -/
theorem covers (hU : (⨆ i, U i) = ⊤) : (⨆ i, opens X U i) = ⊤ := by
  apply top_unique
  intro x hx
  have hxU : x ∈ ⨆ i, U i := by rw [hU]; exact hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open hi (U i).2
  exact Opens.mem_iSup.mpr ⟨⟨i, ⟨V, hV, hVU⟩⟩, hxV⟩

theorem pair_affine [X.IsSeparated] (i j : Index X U) :
    IsAffineOpen (opens X U i ⊓ opens X U j) :=
  SeparatedAffineIntersections.isAffineOpen_inf (affine X U i) (affine X U j)

theorem triple_affine [X.IsSeparated] (i j k : Index X U) :
    IsAffineOpen ((opens X U i ⊓ opens X U j) ⊓ opens X U k) :=
  SeparatedAffineIntersections.isAffineOpen_inf_inf
    (affine X U i) (affine X U j) (affine X U k)

end KltDP.Geometry.AffineOpenRefinement
