import KltDP.Geometry.RationalTreePicardClosedImmersionLift

/-!
# The component-point incidence graph of a closed union of components

Towards `InheritsLeafHypotheses` (BRIEF10, task 10b): the incidence graph of the closed union
`Z_S = componentUnionScheme X S` embeds into the incidence graph of `X` by an injective graph
homomorphism `incidenceGraphHom X S` (components through `componentImage`, intersection points
through the closed immersion `ι_S`), which reflects adjacency (`incidenceGraphHom_adj_iff`).
Acyclicity is pulled back along it (`isAcyclic_incidenceGraph_componentUnionScheme`): a cycle
in the graph of `Z_S` maps to a cycle in the graph of `X`.

Connectivity of the graph of `Z_{Cᶜ}` for a leaf `C` (the lifting of the unique tree path
between two image vertices, which avoids the leaf and, when the node lies on only one other
component, the then-degree-one node vertex) and the transverse germs on `Z_{Cᶜ}` remain; see
`LEMMA22_PROGRESS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (X : Scheme.{u}) [NoetherianSpace X] (S : Set ↥(irreducibleComponents X))

/-- An intersection point of the closed union maps to an intersection point of `X`. -/
def intersectionPointImage
    (z : ↥(componentIntersectionPoints (componentUnionScheme X S))) :
    ↥(componentIntersectionPoints X) :=
  ⟨(componentUnionInclusion X S).base z.1,
    image_componentIntersectionPoints_subset X S ⟨z.1, z.2, rfl⟩⟩

theorem intersectionPointImage_injective : Function.Injective (intersectionPointImage X S) := by
  intro z₁ z₂ h
  exact Subtype.ext ((componentUnionInclusion X S).isClosedEmbedding.injective
    (congrArg Subtype.val h))

/-- The graph homomorphism from the incidence graph of the closed union to that of `X`. -/
def incidenceGraphHom :
    componentPointIncidenceGraph (componentUnionScheme X S) →g componentPointIncidenceGraph X where
  toFun := Sum.map (componentImage X S) (intersectionPointImage X S)
  map_rel' := by
    intro v w h
    rcases v with D' | z <;> rcases w with D'' | z'
    · exact h.elim
    · change (intersectionPointImage X S z').1 ∈ (componentImage X S D').1
      change z'.1 ∈ D'.1 at h
      rw [← image_componentImage]
      exact ⟨z'.1, h, rfl⟩
    · change (intersectionPointImage X S z).1 ∈ (componentImage X S D'').1
      change z.1 ∈ D''.1 at h
      rw [← image_componentImage]
      exact ⟨z.1, h, rfl⟩
    · exact h.elim

theorem incidenceGraphHom_injective : Function.Injective (incidenceGraphHom X S) :=
  Sum.map_injective.mpr ⟨componentImage_injective X S, intersectionPointImage_injective X S⟩

/-- The homomorphism reflects adjacency: it is an embedding of graphs. -/
theorem incidenceGraphHom_adj_iff
    (v w : ↥(irreducibleComponents (componentUnionScheme X S)) ⊕
      ↥(componentIntersectionPoints (componentUnionScheme X S))) :
    (componentPointIncidenceGraph X).Adj (incidenceGraphHom X S v) (incidenceGraphHom X S w) ↔
      (componentPointIncidenceGraph (componentUnionScheme X S)).Adj v w := by
  refine ⟨fun h => ?_, fun h => (incidenceGraphHom X S).map_rel h⟩
  rcases v with D' | z <;> rcases w with D'' | z'
  · exact h.elim
  · change (intersectionPointImage X S z').1 ∈ (componentImage X S D').1 at h
    change z'.1 ∈ D'.1
    rw [componentImage_preimage X S D']
    exact h
  · change (intersectionPointImage X S z).1 ∈ (componentImage X S D'').1 at h
    change z.1 ∈ D''.1
    rw [componentImage_preimage X S D'']
    exact h
  · exact h.elim

/-- Acyclicity of the incidence graph is inherited by every closed union of components. -/
theorem isAcyclic_incidenceGraph_componentUnionScheme
    (hX : (componentPointIncidenceGraph X).IsAcyclic) :
    (componentPointIncidenceGraph (componentUnionScheme X S)).IsAcyclic :=
  fun _ c hc => hX (c.map (incidenceGraphHom X S)) (hc.map (incidenceGraphHom_injective X S))

/-- The image of the embedding on component vertices: exactly the selected components. -/
theorem inl_mem_range_incidenceGraphHom_iff (D : ↥(irreducibleComponents X)) :
    Sum.inl D ∈ Set.range (incidenceGraphHom X S) ↔ D ∈ S := by
  constructor
  · rintro ⟨v, hv⟩
    rcases v with D' | z
    · have h : componentImage X S D' = D := Sum.inl.inj hv
      exact h ▸ componentImage_mem X S D'
    · exact (Sum.inr_ne_inl hv).elim
  · intro hD
    obtain ⟨D', hD'⟩ := exists_componentImage_eq X S D hD
    exact ⟨Sum.inl D', congrArg Sum.inl hD'⟩

/-- The image of the embedding on point vertices: the points lying on two distinct selected
components. -/
theorem inr_mem_range_incidenceGraphHom_iff (x : ↥(componentIntersectionPoints X)) :
    Sum.inr x ∈ Set.range (incidenceGraphHom X S) ↔
      ∃ D₁ D₂ : ↥(irreducibleComponents X), D₁ ∈ S ∧ D₂ ∈ S ∧ D₁ ≠ D₂ ∧
        x.1 ∈ D₁.1 ∧ x.1 ∈ D₂.1 := by
  constructor
  · rintro ⟨v, hv⟩
    rcases v with D' | z
    · exact (Sum.inl_ne_inr hv).elim
    · have hz : intersectionPointImage X S z = x := Sum.inr.inj hv
      obtain ⟨D₁, D₂, hne, hz₁, hz₂⟩ := z.2
      refine ⟨componentImage X S D₁, componentImage X S D₂, componentImage_mem X S D₁,
        componentImage_mem X S D₂, fun h => hne (componentImage_injective X S h), ?_, ?_⟩
      · rw [← hz, ← image_componentImage]
        exact ⟨z.1, hz₁, rfl⟩
      · rw [← hz, ← image_componentImage]
        exact ⟨z.1, hz₂, rfl⟩
  · rintro ⟨D₁, D₂, hD₁, hD₂, hne, hx₁, hx₂⟩
    obtain ⟨z, hz, hzx⟩ :=
      exists_componentIntersectionPoint_of_two_components X S x.1 D₁ D₂ hD₁ hD₂ hne hx₁ hx₂
    exact ⟨Sum.inr ⟨z, hz⟩, congrArg Sum.inr (Subtype.ext hzx)⟩

section Lifting

/-- Walks in the target of an injective, adjacency-reflecting graph homomorphism whose vertices
all lie in the image lift to reachability in the source. -/
theorem reachable_of_walk_of_support_subset_range {V V' : Type*} {G : SimpleGraph V}
    {G' : SimpleGraph V'} (f : G →g G') (hinj : Function.Injective f)
    (hrefl : ∀ a b, G'.Adj (f a) (f b) → G.Adj a b) {a b : V'} (p : G'.Walk a b)
    (hsupp : ∀ x ∈ p.support, x ∈ Set.range f) {u w : V} (hu : f u = a) (hw : f w = b) :
    G.Reachable u w := by
  induction p generalizing u w with
  | nil =>
    exact (hinj (hu.trans hw.symm)) ▸ SimpleGraph.Reachable.refl u
  | cons hadj p' ih =>
    obtain ⟨u', hu'⟩ := hsupp _ (List.mem_cons_of_mem _ p'.start_mem_support)
    have h1 : G.Adj u u' := hrefl u u' (by rw [hu, hu']; exact hadj)
    exact h1.reachable.trans
      (ih (fun x hx => hsupp x (List.mem_cons_of_mem _ hx)) hu' hw)

end Lifting

section Leaf

variable {X}

/-- The only neighbour of a leaf component in the incidence graph is its node. -/
theorem adj_inl_leaf {C : ↥(irreducibleComponents X)} {q : X}
    (hcut : C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q})
    (x : ↥(componentIntersectionPoints X))
    (h : (componentPointIncidenceGraph X).Adj (Sum.inl C) (Sum.inr x)) : x.1 = q := by
  change x.1 ∈ C.1 at h
  obtain ⟨D₁, D₂, hne, hx₁, hx₂⟩ := x.2
  have hZ : x.1 ∈ (componentClosedUnion X ({C}ᶜ) : Set X) := by
    by_cases hD₁ : D₁ = C
    · subst hD₁
      exact (mem_componentClosedUnion X _ x.1).mpr ⟨D₂, fun h' => hne h'.symm, hx₂⟩
    · exact (mem_componentClosedUnion X _ x.1).mpr ⟨D₁, hD₁, hx₁⟩
  have hmem : x.1 ∈ C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) := ⟨h, hZ⟩
  rw [hcut] at hmem
  exact hmem

end Leaf

end KltDP.Geometry.RationalTreePicard
