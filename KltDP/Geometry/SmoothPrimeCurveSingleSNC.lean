import KltDP.Geometry.PrimeCurveCrossingCoefficient
import KltDP.Geometry.StrictNormalCrossings
import KltDP.Geometry.ClosedPointDimension

/-!
# One original smooth prime curve gives a local SNC equation

At a closed point, an actual uniformizer of the smooth curve's DVR stalk
lifts through the original inclusion stalk map. Its lift and the original
Cartier equation generate the ambient maximal ideal. At the curve generic
point the target stalk is the actual function field, so the original
kernel is itself the ambient maximal ideal, of dimension one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.SmoothPrimeCurveSingleSNC

private theorem span_pair_of_local_surjection
    {R T : Type u} [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]
    (φ : R →+* T) [IsLocalHom φ] (hsurj : Function.Surjective φ)
    (f g : R) (hker : RingHom.ker φ = Ideal.span {f})
    (hmax : maximalIdeal T = Ideal.span {φ g}) :
    Ideal.span {f, g} = maximalIdeal R := by
  have hmap : (Ideal.span {g}).map φ = Ideal.span {φ g} := by
    rw [Ideal.map_span, Set.image_singleton]
  have h := congrArg (Ideal.comap φ) hmax
  rw [← hmap, Ideal.comap_map_of_surjective φ hsurj,
    ← RingHom.ker_eq_comap_bot, hker] at h
  have hcomap : (maximalIdeal T).comap φ = maximalIdeal R := by
    ext r
    change ¬ IsUnit (φ r) ↔ ¬ IsUnit r
    exact not_congr (isUnit_map_iff φ r)
  calc
    Ideal.span {f, g} = Ideal.span {f} ⊔ Ideal.span {g} := Ideal.span_insert _ _
    _ = Ideal.span {g} ⊔ Ideal.span {f} := sup_comm _ _
    _ = (maximalIdeal T).comap φ := h.symm
    _ = maximalIdeal R := hcomap

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) (C : X.PrimeCurve)

local instance singleSNC_stalkIsDomain (y : C.toScheme) :
    IsDomain (C.toScheme.presheaf.stalk y) := integralSchemeStalk_isDomain C.toScheme y

/-- The original scheme generic point maps to the actual curve generic point. -/
theorem inclusion_genericPoint :
    C.inclusion.base (_root_.genericPoint C.toScheme) = C.genericPoint := by
  apply (inseparable_iff_closure_eq.mpr ?_).eq
  rw [← Set.image_singleton, C.inclusion.isClosedEmbedding.closure_image_eq,
    genericPoint_closure, Set.image_univ, C.range_inclusion, C.closure_genericPoint]

private theorem inclusion_kernel_eq_span (y : C.toScheme)
    (c : RegularCartierEquationChart X.toScheme (X.primeCurveCartier hregular C))
    (hc : C.inclusion.base y ∈ c.chart.openSet) :
    RingHom.ker (C.inclusion.stalkMap y).hom =
      Ideal.span {X.toScheme.presheaf.germ c.chart.openSet (C.inclusion.base y) hc c.coefficient} := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, _⟩ :=
    (isBasis_affine_open X.toScheme).exists_subset_of_mem_open
      (Set.mem_univ (C.inclusion.base y)) isOpen_univ
  exact (C.vanishingIdeal.stalkMap_gluedTo_ker_eq_map ⟨U, hU⟩ hyU).trans
    (PrimeCurveCrossingCoefficient.vanishingIdeal_map_germ_eq_span_coefficient
      X hregular C ⟨U, hU⟩ (C.inclusion.base y) hyU c hc)

private theorem inclusion_comap_maximalIdeal (y : C.toScheme) :
    (maximalIdeal (C.toScheme.presheaf.stalk y)).comap (C.inclusion.stalkMap y).hom =
      maximalIdeal (X.toScheme.presheaf.stalk (C.inclusion.base y)) := by
  ext r
  change ¬ IsUnit ((C.inclusion.stalkMap y).hom r) ↔ ¬ IsUnit r
  exact not_congr (isUnit_map_iff (C.inclusion.stalkMap y).hom r)

/-- The actual equation of a smooth prime curve extends to a parameter
pair at every closed curve point, by lifting an actual curve uniformizer. -/
theorem equation_snc_of_closed [IsSmooth C.toSpec]
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme))
    (c : RegularCartierEquationChart X.toScheme (X.primeCurveCartier hregular C))
    (hc : C.inclusion.base y ∈ c.chart.openSet) :
    IsStrictNormalCrossingsEquation (X.toScheme.presheaf.stalk (C.inclusion.base y))
      (X.toScheme.presheaf.germ c.chart.openSet (C.inclusion.base y) hc c.coefficient) := by
  let f := X.toScheme.presheaf.germ c.chart.openSet (C.inclusion.base y) hc c.coefficient
  let φ := (C.inclusion.stalkMap y).hom
  letI := C.stalk_isDiscreteValuationRing_of_isSmooth y hy
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (C.toScheme.presheaf.stalk y)
  obtain ⟨g, hg⟩ := C.inclusion.stalkMap_surjective y t
  have hmax : maximalIdeal (C.toScheme.presheaf.stalk y) = Ideal.span {φ g} := by
    rw [hg]
    exact ht.maximalIdeal_eq
  have hspan : Ideal.span {f, g} =
      maximalIdeal (X.toScheme.presheaf.stalk (C.inclusion.base y)) :=
    span_pair_of_local_surjection φ (C.inclusion.stalkMap_surjective y) f g
      (inclusion_kernel_eq_span X hregular C y c hc) hmax
  have hclosed : IsClosed ({C.inclusion.base y} : Set X.toScheme) := by
    rw [← Set.image_singleton]
    exact C.inclusion.isClosedEmbedding.isClosedMap _ hy
  exact IsStrictNormalCrossingsEquation.of_first_parameter (hregular _)
    (X.closed_stalk_dimension_two _ hclosed) f g hspan

/-- The original equation at the actual curve generic point is the sole
regular parameter in its one-dimensional original surface stalk. -/
theorem equation_snc_at_genericPoint
    (c : RegularCartierEquationChart X.toScheme (X.primeCurveCartier hregular C))
    (hc : C.inclusion.base (_root_.genericPoint C.toScheme) ∈ c.chart.openSet) :
    IsStrictNormalCrossingsEquation
      (X.toScheme.presheaf.stalk (C.inclusion.base (_root_.genericPoint C.toScheme)))
      (X.toScheme.presheaf.germ c.chart.openSet
        (C.inclusion.base (_root_.genericPoint C.toScheme)) hc c.coefficient) := by
  have hspan := inclusion_kernel_eq_span X hregular C (_root_.genericPoint C.toScheme) c hc
  have hmax := inclusion_comap_maximalIdeal X C (_root_.genericPoint C.toScheme)
  rw [IsLocalRing.maximalIdeal_eq_bot] at hmax
  have hdim : ringKrullDim
      (X.toScheme.presheaf.stalk (C.inclusion.base (_root_.genericPoint C.toScheme))) = 1 := by
    rw [inclusion_genericPoint X C]
    exact C.ringKrullDim_stalk_genericPoint
  exact IsStrictNormalCrossingsEquation.of_single_parameter (hregular _) hdim _
    (hspan.symm.trans hmax)

/-- Every original regular Cartier equation of a smooth prime curve is
an SNC equation at every original point on that curve. -/
theorem equation_snc [IsSmooth C.toSpec]
    (y : C.toScheme)
    (c : RegularCartierEquationChart X.toScheme (X.primeCurveCartier hregular C))
    (hc : C.inclusion.base y ∈ c.chart.openSet) :
    IsStrictNormalCrossingsEquation (X.toScheme.presheaf.stalk (C.inclusion.base y))
      (X.toScheme.presheaf.germ c.chart.openSet (C.inclusion.base y) hc c.coefficient) := by
  by_cases hy : y = _root_.genericPoint C.toScheme
  · subst y
    exact equation_snc_at_genericPoint X hregular C c hc
  · have hne : closure ({y} : Set C.toScheme) ≠ Set.univ := by
      intro h
      exact hy (inseparable_iff_closure_eq.mpr (h.trans (genericPoint_closure C.toScheme).symm)).eq
    have hclosed := (KltDP.Topology.finite_and_isClosed_singleton_of_isClosed_of_ne_univ
      C.dimension_one_toScheme.le isClosed_closure hne).2 y
      (subset_closure (Set.mem_singleton y))
    exact equation_snc_of_closed X hregular C y hclosed c hc

end KltDP.Geometry.SmoothPrimeCurveSingleSNC

#print axioms KltDP.Geometry.SmoothPrimeCurveSingleSNC.equation_snc
