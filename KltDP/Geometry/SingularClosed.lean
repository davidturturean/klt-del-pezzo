import KltDP.Geometry.SingularPoints
import KltDP.Topology.Dimension
import Mathlib.RingTheory.Ideal.Height

/-!
# Closedness of singular points on normal surfaces

A nonclosed point has a strict specialization. An affine neighborhood of
that specialization contains both points, giving a strict inclusion of their
prime ideals. The local dimension at the first point is therefore at most
one when the ambient scheme has topological Krull dimension at most two.

Normality then makes the first point regular. This proves closedness of each
singular point, independently of openness of the regular locus.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace Topology

universe u

namespace KltDP.Geometry

/-- The coordinate ring of an affine open has Krull dimension at most the
topological Krull dimension of the ambient scheme. -/
theorem ringKrullDim_sections_le_topologicalKrullDim (X : Scheme.{u})
    (U : X.Opens) (hU : IsAffineOpen U) :
    ringKrullDim Γ(X, U) ≤ topologicalKrullDim X := by
  let e : U ≃ₜ PrimeSpectrum Γ(X, U) := hU.isoSpec.hom.homeomorph
  calc
    ringKrullDim Γ(X, U) = topologicalKrullDim (PrimeSpectrum Γ(X, U)) :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)).symm
    _ ≤ topologicalKrullDim U :=
      KltDP.Topology.topologicalKrullDim_le_of_isInducing e.symm e.symm.isInducing
    _ ≤ topologicalKrullDim X := KltDP.Topology.topologicalKrullDim_opens_le U

/-- Below a strictly larger prime in a ring of dimension at most two, the
prime height is at most one. No Noetherianity assumption is needed. -/
theorem primeHeight_le_one_of_lt_of_ringKrullDim_le_two
    {R : Type u} [CommRing R] (p q : PrimeSpectrum R) (hpq : p < q)
    (hdim : ringKrullDim R ≤ 2) :
    (p.asIdeal.primeHeight : WithBot ℕ∞) ≤ 1 := by
  have hq : (q.asIdeal.primeHeight : WithBot ℕ∞) ≤ 2 :=
    Ideal.primeHeight_le_ringKrullDim.trans hdim
  have hq' : Order.height q ≤ (2 : ℕ∞) := WithBot.coe_le_coe.mp hq
  have hp' : Order.height p < (2 : ℕ∞) :=
    (Order.height_le_coe_iff (x := q) (n := 2)).mp hq' p hpq
  have hp : Order.height p ≤ (1 : ℕ∞) := by
    apply (ENat.lt_add_one_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mp
    simpa only [one_add_one_eq_two] using hp'
  exact WithBot.coe_le_coe.mpr hp

/-- A nonclosed point in a scheme of topological Krull dimension at most
two has a structure-sheaf stalk of Krull dimension at most one. -/
theorem ringKrullDim_stalk_le_one_of_not_isClosed_singleton
    (X : Scheme.{u}) (hdim : topologicalKrullDim X ≤ 2)
    (x : X) (hx : ¬ IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  have hnot : ¬ closure ({x} : Set X) ⊆ {x} :=
    fun h ↦ hx (isClosed_of_closure_subset h)
  obtain ⟨y, hy, hyne⟩ := Set.not_subset.mp hnot
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  let U : X.Opens := (X.affineCover.map y).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.map y)
  have hyU : y ∈ U := X.affineCover.covers y
  have hxU : x ∈ U := hxy.mem_open U.isOpen hyU
  let xu : U := ⟨x, hxU⟩
  let yu : U := ⟨y, hyU⟩
  let p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf xu
  let q : PrimeSpectrum Γ(X, U) := hU.primeIdealOf yu
  have hxyU : xu ⤳ yu := (subtype_specializes_iff xu yu).mpr hxy
  have hpq_le : p ≤ q :=
    (PrimeSpectrum.le_iff_specializes p q).mpr (hxyU.map hU.isoSpec.hom.continuous)
  have hpq_ne : p ≠ q := by
    intro hpq
    have heq : (xu : X) = (yu : X) := by
      calc
        (xu : X) = hU.fromSpec.base p := (hU.fromSpec_primeIdealOf xu).symm
        _ = hU.fromSpec.base q := congrArg hU.fromSpec.base hpq
        _ = (yu : X) := hU.fromSpec_primeIdealOf yu
    exact hyne heq.symm
  have hpq : p < q := lt_of_le_of_ne hpq_le hpq_ne
  have hchart : ringKrullDim Γ(X, U) ≤ 2 :=
    (ringKrullDim_sections_le_topologicalKrullDim X U hU).trans hdim
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk xu
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk xu
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk x),
    Ideal.height_eq_primeHeight]
  exact primeHeight_le_one_of_lt_of_ringKrullDim_le_two p q hpq hchart

/-- In dimension at most two, a singular point of a normal scheme is closed
when its actual stalk is Noetherian. -/
theorem singularPoint_isClosed_of_dimension_le_two (X : Scheme.{u})
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 2)
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (hx : x ∈ singularLocus X) : IsClosed ({x} : Set X) := by
  by_contra hclosed
  exact hx (regularPoint_of_normal_of_ringKrullDim_le_one X hnormal x
    (ringKrullDim_stalk_le_one_of_not_isClosed_singleton X hdim x hclosed))

/-- Every actual singular scheme point of a normal projective surface is
closed. No finiteness or regular-locus openness hypothesis is used. -/
theorem singularPoint_isClosed {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (x : X.Point)
    (hx : x ∈ singularLocus X.toScheme) : IsClosed ({x} : Set X.Point) :=
  singularPoint_isClosed_of_dimension_le_two X.toScheme X.normal
    X.dimension_two.le x hx

end KltDP.Geometry
