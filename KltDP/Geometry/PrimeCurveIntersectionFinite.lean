import KltDP.Geometry.ZeroDimensionalSchemeSections
import KltDP.Topology.DimensionOneClosedSubsets

/-!
# `C ∩ Supp D` is a finite set of closed points

For a prime curve `C ⊄ Supp D`, the preimage of `Supp D` in the curve scheme is a
proper closed subset of the integral one-dimensional Noetherian scheme `C.toScheme`
(`dimension_one_toScheme`), hence a finite set of closed points by the chain argument
of `KltDP.Topology.DimensionOneClosedSubsets`. Its image under the closed immersion
`C → X` is `C ∩ Supp D`, the underlying set of the intersection subscheme.

Consequently the sum formula `intersectionDegree = Σ_z dim_k Γ(C ∩ D, {z})` holds with
no finiteness or closedness hypotheses.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
  (hC : C.NotInSupport D hD)

/-- The underlying set of `C ∩ D` in the surface is finite and consists of closed points. -/
theorem range_intersectionToSurface_finite_and_isClosed :
    (Set.range (C.intersectionToSurface D hD hC).base).Finite ∧
      ∀ x ∈ Set.range (C.intersectionToSurface D hD hC).base,
        IsClosed ({x} : Set X.toScheme) := by
  set I := effectiveCartierIdealDataOfRegularEquations X.toScheme D hD with hI
  set T : Set C.toScheme := C.inclusion.base ⁻¹' (I.support : Set X.toScheme) with hTdef
  have hTc : IsClosed T := I.isClosed_supportSet.preimage C.inclusion.continuous
  have hTne : T ≠ Set.univ := by
    intro h
    have hmem : C.genericLift ∈ T := h ▸ Set.mem_univ _
    rw [hTdef, Set.mem_preimage, C.inclusion_genericLift] at hmem
    exact hC hmem
  obtain ⟨hfin, hcl⟩ := KltDP.Topology.finite_and_isClosed_singleton_of_isClosed_of_ne_univ
    (le_of_eq C.dimension_one_toScheme) hTc hTne
  have hrange : Set.range (C.intersectionToSurface D hD hC).base = C.inclusion.base '' T := by
    rw [C.range_intersectionToSurface D hD hC, hTdef, Set.image_preimage_eq_inter_range,
      C.range_inclusion, Set.inter_comm]
  refine ⟨by rw [hrange]; exact hfin.image _, ?_⟩
  intro x hx
  rw [hrange] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← Set.image_singleton]
  exact (IsClosedImmersion.base_closed (f := C.inclusion)).isClosedMap _ (hcl y hy)

/-- The intersection subscheme has finitely many points. -/
theorem intersectionScheme_finite' : Finite (C.intersectionScheme D hD hC) :=
  C.intersectionScheme_finite D hD hC (C.range_intersectionToSurface_finite_and_isClosed D hD hC).1

/-- Every point of the intersection subscheme is closed. -/
theorem intersectionScheme_isClosed_singleton' (z : C.intersectionScheme D hD hC) :
    IsClosed ({z} : Set (C.intersectionScheme D hD hC)) :=
  C.intersectionScheme_isClosed_singleton D hD hC
    (C.range_intersectionToSurface_finite_and_isClosed D hD hC).2 z

/-- The sum formula over the points of `C ∩ D`, with no hypotheses beyond `C ⊄ Supp D`:
`intersectionDegree = Σ_z dim_k Γ(C ∩ D, {z})`. -/
theorem intersectionDegree_eq_sum_points'' :
    letI : Fintype (C.intersectionScheme D hD hC) :=
      haveI := C.intersectionScheme_finite D hD hC
        (C.range_intersectionToSurface_finite_and_isClosed D hD hC).1
      Fintype.ofFinite _
    letI : DiscreteTopology (C.intersectionScheme D hD hC) :=
      DiscreteTopology.of_finite_of_isClosed_singleton
        (C.intersectionScheme_isClosed_singleton D hD hC
          (C.range_intersectionToSurface_finite_and_isClosed D hD hC).2)
    letI : ∀ z : C.intersectionScheme D hD hC,
        Module k Γ(C.intersectionScheme D hD hC, singletonOpen (C.intersectionScheme D hD hC) z) :=
      fun z => sectionsBaseModule (C.intersectionScheme D hD hC)
        (baseFieldToGlobalSections (C.intersectionToSpec D hD hC))
        (singletonOpen (C.intersectionScheme D hD hC) z)
    C.intersectionDegree D hD hC = ∑ z : C.intersectionScheme D hD hC,
      Module.finrank k Γ(C.intersectionScheme D hD hC, singletonOpen (C.intersectionScheme D hD hC) z) :=
  C.intersectionDegree_eq_sum_points_of_finite D hD hC
    (C.range_intersectionToSurface_finite_and_isClosed D hD hC).1
    (C.range_intersectionToSurface_finite_and_isClosed D hD hC).2

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
