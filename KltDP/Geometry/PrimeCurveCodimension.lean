import KltDP.Geometry.PrimeDivisor
import KltDP.Geometry.SingularClosed
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Local dimension at the generic point of an actual prime curve

The indexing curves remain the dimension-one irreducible closed subsets
defined in `PrimeDivisor`. Their actual generic points have stalk dimension
one. The upper bound uses a strict specialization and the ambient dimension
two. The lower bound uses the strict inclusion between the zero prime and
the point's prime in an affine chart of the integral surface.

This proves the dimension-one-to-codimension-one direction needed for
divisor orders. It does not assume a dimension formula, a DVR structure,
or an equivalence with every codimension-one point. Finite type and
Noetherianity are not needed for this direction.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace Topology

universe u

namespace KltDP.Geometry

/-- A space with at most one point has no positive-dimensional chain of
irreducible closed subsets. -/
theorem topologicalKrullDim_nonpos_of_subsingleton
    (T : Type u) [TopologicalSpace T] [Subsingleton T] :
    topologicalKrullDim T ≤ 0 := by
  letI : Subsingleton (IrreducibleCloseds T) := ⟨fun A B ↦ by
    apply IrreducibleCloseds.ext
    apply Set.ext
    intro x
    obtain ⟨a, ha⟩ := A.isIrreducible.nonempty
    obtain ⟨b, hb⟩ := B.isIrreducible.nonempty
    exact ⟨fun _ ↦ (Subsingleton.elim b x) ▸ hb,
      fun _ ↦ (Subsingleton.elim a x) ▸ ha⟩⟩
  exact Order.krullDim_nonpos_of_subsingleton

/-- Every nongeneric point of an integral scheme has a stalk of Krull
dimension at least one. The comparison uses its actual affine prime. -/
theorem one_le_ringKrullDim_stalk_of_ne_genericPoint
    (X : Scheme.{u}) [IsIntegral X] (x : X) (hx : x ≠ genericPoint X) :
    1 ≤ ringKrullDim (X.presheaf.stalk x) := by
  let U : X.Opens := (X.affineCover.map x).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.map x)
  have hxU : x ∈ U := X.affineCover.covers x
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  let xu : U := ⟨x, hxU⟩
  let p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf xu
  have hgU : genericPoint X ∈ U :=
    (genericPoint_specializes x).mem_open U.isOpen hxU
  let gu : U := ⟨genericPoint X, hgU⟩
  have hgbot : hU.primeIdealOf gu = ⊥ :=
    hU.primeIdealOf_genericPoint.trans (genericPoint_eq_bot_of_affine _)
  have hpne : p ≠ ⊥ := by
    intro hp
    apply hx
    calc
      x = hU.fromSpec.base p := (hU.fromSpec_primeIdealOf xu).symm
      _ = hU.fromSpec.base (hU.primeIdealOf gu) := by rw [hp, hgbot]
      _ = genericPoint X := hU.fromSpec_primeIdealOf gu
  have hpheight : (1 : ℕ∞) ≤ Order.height p := by
    simpa only [Order.height_bot, zero_add] using
      (Order.height_add_one_le (bot_lt_iff_ne_bot.mpr hpne))
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk xu
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk xu
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk x),
    Ideal.height_eq_primeHeight]
  exact WithBot.coe_le_coe.mpr hpheight

namespace NormalProjectiveSurface.PrimeCurve

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}

/-- Dimension one distinguishes the curve from the whole surface. -/
theorem ne_univ (C : X.PrimeCurve) : (C : Set X.toScheme) ≠ Set.univ := by
  intro hC
  have hdim := C.dimension_one
  rw [hC] at hdim
  have heq : topologicalKrullDim (Set.univ : Set X.toScheme) =
      topologicalKrullDim X.toScheme :=
    IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ X.toScheme)
      (Homeomorph.Set.univ X.toScheme).isHomeomorph
  rw [heq, X.dimension_two] at hdim
  norm_num at hdim

/-- The curve's generic point is distinct from the surface's generic point. -/
theorem genericPoint_ne_surface_genericPoint (C : X.PrimeCurve) :
    C.genericPoint ≠ _root_.genericPoint X.toScheme := by
  intro h
  apply C.ne_univ
  rw [← C.closure_genericPoint, h, genericPoint_closure]

/-- A dimension-one curve's generic point is not a closed point. -/
theorem not_isClosed_singleton_genericPoint (C : X.PrimeCurve) :
    ¬ IsClosed ({C.genericPoint} : Set X.toScheme) := by
  intro hclosed
  have hC : (C : Set X.toScheme) = {C.genericPoint} := by
    rw [← C.closure_genericPoint, hclosed.closure_eq]
  have hdim := C.dimension_one
  rw [hC] at hdim
  have hnonpos := topologicalKrullDim_nonpos_of_subsingleton
    ({C.genericPoint} : Set X.toScheme)
  rw [hdim] at hnonpos
  have hpositive : (0 : WithBot ℕ∞) < 1 :=
    WithBot.coe_lt_coe.mpr (by simp : (0 : ℕ∞) < 1)
  exact hpositive.not_le hnonpos

/-- The actual structure-sheaf stalk at a prime curve's generic point has
Krull dimension exactly one. -/
theorem ringKrullDim_stalk_genericPoint (C : X.PrimeCurve) :
    ringKrullDim (X.stalk C.genericPoint) = 1 := by
  apply le_antisymm
  · exact ringKrullDim_stalk_le_one_of_not_isClosed_singleton
      X.toScheme X.dimension_two.le C.genericPoint C.not_isClosed_singleton_genericPoint
  · exact one_le_ringKrullDim_stalk_of_ne_genericPoint
      X.toScheme C.genericPoint C.genericPoint_ne_surface_genericPoint

/-- In every affine neighborhood, the curve's generic point corresponds
to an actual height-one prime ideal. -/
theorem primeIdealOf_height_eq_one (C : X.PrimeCurve) {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (hmem : C.genericPoint ∈ U) :
    (hU.primeIdealOf ⟨C.genericPoint, hmem⟩).asIdeal.height = 1 := by
  let xu : U := ⟨C.genericPoint, hmem⟩
  let p : PrimeSpectrum Γ(X.toScheme, U) := hU.primeIdealOf xu
  letI : Algebra Γ(X.toScheme, U) (X.stalk C.genericPoint) :=
    X.toScheme.presheaf.algebra_section_stalk xu
  letI : IsLocalization.AtPrime (X.stalk C.genericPoint) p.asIdeal :=
    hU.isLocalization_stalk xu
  apply WithBot.coe_injective
  change (p.asIdeal.height : WithBot ℕ∞) = 1
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
    (X.stalk C.genericPoint)]
  exact C.ringKrullDim_stalk_genericPoint

/-- Taking the actual generic point loses no curve information. -/
theorem genericPoint_injective :
    Function.Injective (genericPoint (X := X)) := by
  intro C D h
  apply PrimeCurve.ext
  rw [← C.closure_genericPoint, ← D.closure_genericPoint, h]

end NormalProjectiveSurface.PrimeCurve

end KltDP.Geometry
