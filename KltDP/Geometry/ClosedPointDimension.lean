import KltDP.Compatibility.FiniteTypeMaximalHeight
import KltDP.Geometry.FiniteTypeNoetherian
import KltDP.Geometry.SingularClosed
import KltDP.Topology.DimensionOpenCover
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Dimension at actual closed points of an algebraic surface

The finite-type maximal-height theorem identifies a closed-point stalk
dimension with the dimension of any actual affine neighborhood. Nonempty
affine opens on an integral scheme meet in a nonempty open set. The pinned
Jacobson theorem supplies a common closed point, so their dimensions agree.
The already proved open-cover dimension bound identifies this common
dimension with the original scheme's topological Krull dimension.

This implements the closed-point and open-dimension argument of Stacks
0A21(2)–(3) using proved algebraic facts and actual scheme maps. No
dimension formula or closed-point dimension is introduced as an axiom.
The algebraically closed field hypothesis is explicit, as required by the
reused polynomial maximal-height proof.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : Scheme.{u}) [IsIntegral X]
variable (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]

/-- A globally closed point has maximal prime in every actual affine
neighborhood containing it. -/
theorem isMaximal_primeIdealOf_of_isClosed {U : X.Opens} (hU : IsAffineOpen U)
    (x : U) (hx : IsClosed ({(x : X)} : Set X)) :
    (hU.primeIdealOf x).asIdeal.IsMaximal := by
  have hxu : IsClosed ({x} : Set U) := by
    have hpre : IsClosed ((Subtype.val : U → X) ⁻¹' ({(x : X)} : Set X)) :=
      hx.preimage continuous_subtype_val
    have heq : (Subtype.val : U → X) ⁻¹' ({(x : X)} : Set X) = {x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact Subtype.ext_iff.symm
    rwa [heq] at hpre
  have hclosed := hU.isoSpec.hom.homeomorph.isClosedMap _ hxu
  rw [Set.image_singleton] at hclosed
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hclosed

include f

/-- The actual closed-point stalk has the dimension of its actual affine
neighborhood, by the proved finite-type domain theorem. -/
theorem closed_stalk_dimension_eq_affine {U : X.Opens} (hU : IsAffineOpen U)
    (x : U) (hx : IsClosed ({(x : X)} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim Γ(X, U) := by
  letI : Nonempty U := ⟨x⟩
  letI := affineSectionsAlgebra f hU
  letI := affineSectionsAlgebra_finiteType f hU
  letI : (hU.primeIdealOf x).asIdeal.IsMaximal :=
    isMaximal_primeIdealOf_of_isClosed X hU x hx
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk x
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf x).asIdeal]
  exact KltDP.Compatibility.maximal_height_eq_ringKrullDim k Γ(X, U)
    (hU.primeIdealOf x).asIdeal

/-- Any two actual nonempty affine opens have equal dimension. A common
closed point exists by the actual finite-type Jacobson theorem. -/
theorem nonempty_affine_dimensions_eq {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) [Nonempty U] [Nonempty V] :
    ringKrullDim Γ(X, U) = ringKrullDim Γ(X, V) := by
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hUV : ((U : Set X) ∩ (V : Set X)).Nonempty :=
    ⟨genericPoint X,
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›),
      ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)⟩
  obtain ⟨x, hxUV, hxclosed⟩ := nonempty_inter_closedPoints hUV
    (U.isOpen.inter V.isOpen).isLocallyClosed
  exact (closed_stalk_dimension_eq_affine X f hU ⟨x, hxUV.1⟩ hxclosed).symm.trans
    (closed_stalk_dimension_eq_affine X f hV ⟨x, hxUV.2⟩ hxclosed)

/-- Every actual nonempty affine chart has the global dimension of the
integral scheme. The upper comparison uses the proved open-cover theorem. -/
theorem nonempty_affine_dimension_eq_global {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] :
    ringKrullDim Γ(X, U) = topologicalKrullDim X := by
  apply le_antisymm (ringKrullDim_sections_le_topologicalKrullDim X U hU)
  apply KltDP.Topology.topologicalKrullDim_le_of_open_cover
    (fun x : X => (X.affineCover.map x).opensRange)
    (fun x => ⟨x, X.affineCover.covers x⟩)
  intro x
  let V : X.Opens := (X.affineCover.map x).opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange (X.affineCover.map x)
  letI : Nonempty V := ⟨⟨x, X.affineCover.covers x⟩⟩
  have htop : topologicalKrullDim V = ringKrullDim Γ(X, V) := by
    exact (_root_.IsHomeomorph.topologicalKrullDim_eq hV.isoSpec.hom.homeomorph
      hV.isoSpec.hom.homeomorph.isHomeomorph).trans
        (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, V))
  exact htop.le.trans (nonempty_affine_dimensions_eq X f hV hU).le

/-- The actual stalk dimension at every globally closed point is the
global dimension of the integral scheme of finite type over the field. -/
theorem closed_stalk_dimension_eq_global (x : X)
    (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = topologicalKrullDim X := by
  let U : X.Opens := (X.affineCover.map x).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.map x)
  let xu : U := ⟨x, X.affineCover.covers x⟩
  letI : Nonempty U := ⟨xu⟩
  exact (closed_stalk_dimension_eq_affine X f hU xu hx).trans
    (nonempty_affine_dimension_eq_global X f hU)

omit f

namespace NormalProjectiveSurface

/-- Closed points of the actual surface have two-dimensional stalks. -/
theorem closed_stalk_dimension_two (X : NormalProjectiveSurface k) (x : X.toScheme)
    (hx : IsClosed ({x} : Set X.toScheme)) : ringKrullDim (X.stalk x) = 2 := by
  letI : LocallyOfFiniteType X.structureMorphism := X.projective.locallyOfFiniteType
  exact (closed_stalk_dimension_eq_global X.toScheme X.structureMorphism x hx).trans
    X.dimension_two

end NormalProjectiveSurface

end KltDP.Geometry
