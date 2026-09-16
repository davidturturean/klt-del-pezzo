import KltDP.Geometry.RationalTreePicardTreeInheritance

/-!
# Connectivity of the incidence graph of the complement of a leaf, and the tree

BRIEF11, task 11a. An interior vertex of a path in a simple graph has two distinct neighbours on
the path (`exists_two_adj_of_mem_support_of_isPath`, by induction on the path). In the tree
`componentPointIncidenceGraph X`, a path between two vertices in the image of the embedding
`incidenceGraphHom X {C}ᶜ` (for a leaf component `C` with node `q`,
`hcut : C ∩ Z_{Cᶜ} = {q}`) never passes through the leaf vertex `inl C`, whose only neighbour is
`inr q` (`inl_leaf_not_mem_support`); consequently every point vertex on the path lies on two
distinct components other than `C` (its two path-neighbours), so the whole support lies in the
image (`support_subset_range_incidenceGraphHom`). Lifting the path
(`reachable_of_walk_of_support_subset_range`) gives connectivity of the incidence graph of
`Z_{Cᶜ}`, and with the inherited acyclicity, `isTree_incidenceGraph_componentUnionScheme_compl`:
the tree hypothesis of `InheritsLeafHypotheses` is inherited.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

section PathLemma

variable {V : Type*} {G : SimpleGraph V}

/-- An interior vertex of a path has two distinct neighbours on the path. -/
theorem exists_two_adj_of_mem_support_of_isPath {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (x : V) (hx : x ∈ p.support) (ha : x ≠ a) (hb : x ≠ b) :
    ∃ y₁ y₂ : V, y₁ ≠ y₂ ∧ G.Adj x y₁ ∧ G.Adj x y₂ ∧ y₁ ∈ p.support ∧ y₂ ∈ p.support := by
  induction p with
  | nil =>
    rw [SimpleGraph.Walk.support_nil] at hx
    exact absurd (List.mem_singleton.mp hx) ha
  | @cons u c w h p' ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx'
    · exact absurd rfl ha
    · rw [SimpleGraph.Walk.cons_isPath_iff] at hp
      by_cases hxc : x = c
      · subst hxc
        cases p' with
        | nil => exact absurd rfl hb
        | @cons _ d _ h' p'' =>
          refine ⟨u, d, fun hud => hp.2 ?_, h.symm, h',
            SimpleGraph.Walk.start_mem_support _, ?_⟩
          · rw [hud, SimpleGraph.Walk.support_cons]
            exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support p'')
          · rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons]
            exact List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support p''))
      · obtain ⟨y₁, y₂, hne, h₁, h₂, hs₁, hs₂⟩ := ih hp.1 hx' hxc hb
        refine ⟨y₁, y₂, hne, h₁, h₂, ?_, ?_⟩
        · rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ hs₁
        · rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ hs₂

end PathLemma

section Connectivity

variable {X : Scheme.{u}} [NoetherianSpace X]

omit [NoetherianSpace X] in
/-- A neighbour of a point vertex is a component vertex through the point. -/
theorem adj_inr_exists (z : ↥(componentIntersectionPoints X))
    (y : ↥(irreducibleComponents X) ⊕ ↥(componentIntersectionPoints X))
    (h : (componentPointIncidenceGraph X).Adj (Sum.inr z) y) :
    ∃ E : ↥(irreducibleComponents X), y = Sum.inl E ∧ z.1 ∈ E.1 := by
  rcases y with E | z'
  · exact ⟨E, rfl, h⟩
  · exact h.elim

omit [NoetherianSpace X] in
/-- A neighbour of a component vertex is a point vertex on the component. -/
theorem adj_inl_exists (D : ↥(irreducibleComponents X))
    (y : ↥(irreducibleComponents X) ⊕ ↥(componentIntersectionPoints X))
    (h : (componentPointIncidenceGraph X).Adj (Sum.inl D) y) :
    ∃ z : ↥(componentIntersectionPoints X), y = Sum.inr z ∧ z.1 ∈ D.1 := by
  rcases y with D' | z
  · exact h.elim
  · exact ⟨z, rfl, h⟩

variable {C : ↥(irreducibleComponents X)} {q : X}

/-- A path between two vertices in the image of the embedding of the complement's graph never
passes through the leaf vertex: the leaf has a single neighbour. -/
theorem inl_leaf_not_mem_support (hcut : C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q})
    {a b : ↥(irreducibleComponents X) ⊕ ↥(componentIntersectionPoints X)}
    (p : (componentPointIncidenceGraph X).Walk a b) (hp : p.IsPath)
    (ha : a ∈ Set.range (incidenceGraphHom X ({C}ᶜ)))
    (hb : b ∈ Set.range (incidenceGraphHom X ({C}ᶜ))) :
    Sum.inl C ∉ p.support := by
  intro hmem
  have hnot : Sum.inl C ∉ Set.range (incidenceGraphHom X ({C}ᶜ)) := fun h =>
    (inl_mem_range_incidenceGraphHom_iff X ({C}ᶜ) C).mp h (Set.mem_singleton C)
  obtain ⟨y₁, y₂, hne, h₁, h₂, -, -⟩ := exists_two_adj_of_mem_support_of_isPath p hp (Sum.inl C)
    hmem (fun h => hnot (by rw [h]; exact ha)) (fun h => hnot (by rw [h]; exact hb))
  obtain ⟨z₁, rfl, -⟩ := adj_inl_exists C y₁ h₁
  obtain ⟨z₂, rfl, -⟩ := adj_inl_exists C y₂ h₂
  apply hne
  congr 1
  exact Subtype.ext ((adj_inl_leaf hcut z₁ h₁).trans (adj_inl_leaf hcut z₂ h₂).symm)

/-- The support of a path between two image vertices lies in the image of the embedding. -/
theorem support_subset_range_incidenceGraphHom
    (hcut : C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q})
    {a b : ↥(irreducibleComponents X) ⊕ ↥(componentIntersectionPoints X)}
    (p : (componentPointIncidenceGraph X).Walk a b) (hp : p.IsPath)
    (ha : a ∈ Set.range (incidenceGraphHom X ({C}ᶜ)))
    (hb : b ∈ Set.range (incidenceGraphHom X ({C}ᶜ))) :
    ∀ x ∈ p.support, x ∈ Set.range (incidenceGraphHom X ({C}ᶜ)) := by
  have hC := inl_leaf_not_mem_support hcut p hp ha hb
  intro x hx
  rcases x with D | z
  · rw [inl_mem_range_incidenceGraphHom_iff]
    intro hD
    rw [Set.mem_singleton_iff] at hD
    apply hC
    rw [← hD]
    exact hx
  · by_contra hz
    obtain ⟨y₁, y₂, hne, h₁, h₂, hs₁, hs₂⟩ := exists_two_adj_of_mem_support_of_isPath p hp
      (Sum.inr z) hx (fun h => hz (by rw [h]; exact ha)) (fun h => hz (by rw [h]; exact hb))
    obtain ⟨E₁, rfl, hE₁⟩ := adj_inr_exists z y₁ h₁
    obtain ⟨E₂, rfl, hE₂⟩ := adj_inr_exists z y₂ h₂
    apply hz
    rw [inr_mem_range_incidenceGraphHom_iff]
    refine ⟨E₁, E₂, fun h => hC ?_, fun h => hC ?_, fun h => hne (congrArg Sum.inl h), hE₁, hE₂⟩
    · rw [Set.mem_singleton_iff] at h
      rw [← h]
      exact hs₁
    · rw [Set.mem_singleton_iff] at h
      rw [← h]
      exact hs₂

/-- The incidence graph of the complement of a leaf component is connected. -/
theorem connected_incidenceGraph_componentUnionScheme_compl
    (hTree : (componentPointIncidenceGraph X).IsTree)
    (hcut : C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q}) :
    (componentPointIncidenceGraph (componentUnionScheme X ({C}ᶜ))).Connected := by
  classical
  have hq : q ∈ C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) := by
    rw [hcut]
    exact Set.mem_singleton q
  obtain ⟨D, hD, -⟩ := (mem_componentClosedUnion X ({C}ᶜ) q).mp hq.2
  obtain ⟨D', -⟩ := exists_componentImage_eq X ({C}ᶜ) D hD
  haveI : Nonempty (↥(irreducibleComponents (componentUnionScheme X ({C}ᶜ))) ⊕
      ↥(componentIntersectionPoints (componentUnionScheme X ({C}ᶜ)))) := ⟨Sum.inl D'⟩
  refine SimpleGraph.Connected.mk fun u w => ?_
  obtain ⟨walk⟩ := hTree.isConnected.preconnected (incidenceGraphHom X ({C}ᶜ) u)
    (incidenceGraphHom X ({C}ᶜ) w)
  exact reachable_of_walk_of_support_subset_range (incidenceGraphHom X ({C}ᶜ))
    (incidenceGraphHom_injective X ({C}ᶜ))
    (fun a b h => (incidenceGraphHom_adj_iff X ({C}ᶜ) a b).mp h) walk.toPath.1
    (support_subset_range_incidenceGraphHom hcut walk.toPath.1 walk.toPath.2 ⟨u, rfl⟩ ⟨w, rfl⟩)
    rfl rfl

/-- The component-point incidence graph of the complement of a leaf component is a tree: the
tree hypothesis of `InheritsLeafHypotheses` is inherited. -/
theorem isTree_incidenceGraph_componentUnionScheme_compl
    (hTree : (componentPointIncidenceGraph X).IsTree)
    (hcut : C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q}) :
    (componentPointIncidenceGraph (componentUnionScheme X ({C}ᶜ))).IsTree :=
  ⟨connected_incidenceGraph_componentUnionScheme_compl hTree hcut,
    isAcyclic_incidenceGraph_componentUnionScheme X ({C}ᶜ) hTree.IsAcyclic⟩

end Connectivity

end KltDP.Geometry.RationalTreePicard
