import KltDP.Geometry.TransitionUnitSections

/-!
# Restriction of transition units to a subordinate family

The refined units are the images of the original units under the actual
structure-sheaf restriction homomorphisms. Their normalization and triple
overlap equations follow by restricting the original cocycle equations.
No module-sheaf isomorphism or trivialization is assumed here.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

variable (X : Scheme.{u}) {J I : Type u} (U : J → X.Opens)
  (g : ∀ j j' : J, Γ(X, U j ⊓ U j')ˣ) (V : I → X.Opens)
  (σ : I → J) (hσ : ∀ i : I, V i ≤ U (σ i))

/-- The original transition units restricted to the subordinate intersections. -/
def refinedUnits (i i' : I) : Γ(X, V i ⊓ V i')ˣ :=
  Units.map
    (res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))).toMonoidHom
    (g (σ i) (σ i'))

@[simp]
theorem refinedUnits_val (i i' : I) :
    (refinedUnits X U g V σ hσ i i' : Γ(X, V i ⊓ V i')) =
      res X (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i')) := rfl

/-- Restricting a transition cocycle gives a transition cocycle on the subordinate family. -/
theorem refinedUnits_isCocycle (hg : IsCocycle X U g) :
    IsCocycle X V (refinedUnits X U g V σ hσ) := by
  refine ⟨?_, ?_⟩
  · intro i
    rw [refinedUnits_val, hg.unit_self, map_one]
  · intro i j l
    have hO : V i ⊓ V j ⊓ V l ≤ U (σ i) ⊓ U (σ j) ⊓ U (σ l) :=
      le_inf
        (le_inf ((inf_le_left.trans inf_le_left).trans (hσ i))
          ((inf_le_left.trans inf_le_right).trans (hσ j)))
        (inf_le_right.trans (hσ l))
    simpa only [refinedUnits_val, res_res] using
      (IsCocycle.mul_res_of_le X U g hg (i := σ i) (j := σ j) (l := σ l) hO)

include hσ in
/-- A covering subordinate family also covers through the original family. -/
theorem cover_of_refinement (hV : (⨆ i, V i) = ⊤) : (⨆ j, U j) = ⊤ := by
  apply top_unique
  rw [← hV]
  exact iSup_le fun i => (hσ i).trans (le_iSup U (σ i))

end KltDP.Geometry.TransitionUnitGluing
