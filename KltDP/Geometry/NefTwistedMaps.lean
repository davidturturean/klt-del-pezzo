import KltDP.Geometry.NefTwistedSections
import KltDP.Geometry.CompleteLinearSystemSectionTuple
import KltDP.Geometry.InvertibleSheafSectionPowers
import KltDP.Geometry.InvertibleSectionTwistMap

/-!
# Eventual actual maps from any original line bundle into powers of a nef line

Original Cartier representatives turn the compiled eventual twisted-H0
bound into actual nonzero compatible sections. Their tensor with the
original source line has the Picard class of the actual power of A, hence
an actual sheaf isomorphism to that power. The existing faithful tensor
construction then gives nonzero maps H → A^n for all sufficiently large n.

The RR input remains in its existing private, unaccepted dependency branch.
This module introduces no axiom, section/vanishing premise, changed
bigness predicate, or admission claim.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Geometry.InvertibleSheafSectionPowers KltDP.Geometry.InvertibleSheafTensor

universe u

namespace KltDP.Geometry.NefTwistedMaps

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance tensorModules (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Every sufficiently large actual power of a nef line of positive
square receives a nonzero actual sheaf map from any original line H. -/
theorem eventually_nonzero_map_of_isCanonical (K : X.WeilDivisor)
    (hK : IsCanonical X hregular K) (A H : InvertibleSheaf X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism A)
    (hpositive : 0 < X.selfIntersection hregular A) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ g : H.obj ⟶ (power A n).obj, g ≠ 0 := by
  letI : IsProper X.structureMorphism := X.projective.isProper
  let D := X.picardRepresentative A.toPic
  let E := X.picardRepresentative H.toPic
  have hDclass : cartierPicardClass X.toScheme D = A.toPic :=
    X.cartierPicardClass_picardRepresentative A.toPic
  have hEclass : cartierPicardClass X.toScheme E = H.toPic :=
    X.cartierPicardClass_picardRepresentative H.toPic
  have hDnef : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme D) := by
    apply (Positivity.isNef_iff_forall_primeCurve X _).mpr
    intro C
    have h := (Positivity.isNef_iff_forall_primeCurve X A).mp hA C
    rw [← C.picardRestrictionDegree_toPic] at h ⊢
    change 0 ≤ C.picardRestrictionDegree (cartierPicardClass X.toScheme D)
    rw [hDclass]
    exact h
  have hDpositive : 0 < intersectionPairing X hregular D D := hpositive
  obtain ⟨N, hN, hsections⟩ := NefTwistedSections.eventually_hDimension_pos
    X hregular K hK D (-E) hDnef hDpositive
  refine ⟨N, hN, ?_⟩
  intro n hn
  let Ltwist := cartierDivisorInvertibleSheaf X.toScheme (n • D - E)
  have hdimension : 0 < CompleteLinearSystemSections.dimension X.structureMorphism Ltwist := by
    have h := hsections n hn
    unfold hDimension divisorModule at h
    rw [RiemannRochEffectiveMultiple.inverse_toWeil] at h
    change 0 < cohomologyDimension X.structureMorphism
      (cartierDivisorModule X.toScheme (n • D - E)) 0
    simpa only [sub_eq_add_neg] using h
  obtain ⟨s, hs⟩ :=
    (CompleteLinearSystemSections.dimension_pos_iff_exists_nonzero_top_section
      X.structureMorphism Ltwist).mp hdimension
  have hDpower : cartierPicardClass X.toScheme (n • D) = A.toPic ^ n := by
    calc
      cartierPicardClass X.toScheme (n • D) =
          (cartierPicardClass X.toScheme D) ^ n :=
        congrArg Additive.toMul ((cartierPicardHom X.toScheme).map_nsmul D n)
      _ = A.toPic ^ n := by rw [hDclass]
  have htensor : (tensorInvertibleSheaf Ltwist H).toPic = (power A n).toPic := by
    rw [AmpleSerreDegreeBound.tensorInvertibleSheaf_toPic, power_toPic]
    change cartierPicardClass X.toScheme (n • D - E) * H.toPic = A.toPic ^ n
    rw [cartierPicardClass_sub, hDpower, hEclass, div_mul_cancel]
  have hskeleton : toSkeleton (Ltwist.obj ⊗ H.obj) = toSkeleton (power A n).obj := by
    have h := congrArg (fun p : X.toScheme.Pic => (p : Skeleton X.toScheme.Modules)) htensor
    simpa only [InvertibleSheaf.toPic_val] using h
  obtain ⟨e⟩ : Nonempty (Ltwist.obj ⊗ H.obj ≅ (power A n).obj) :=
    Quotient.exact hskeleton
  exact InvertibleSectionTwistMap.exists_nonzero_map H Ltwist.obj (power A n).obj e s hs

section Smooth

variable [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- On the original smooth surface, regularity and the canonical divisor
are supplied by the existing geometric constructions. -/
theorem eventually_nonzero_map (A H : InvertibleSheaf X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism A)
    (hpositive : 0 < X.selfIntersection X.regularPoints_of_isSmooth A) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ g : H.obj ⟶ (power A n).obj, g ≠ 0 :=
  eventually_nonzero_map_of_isCanonical X X.regularPoints_of_isSmooth
    (SmoothCanonicalCartierRepresentative.weilRepresentative X)
    (SurfaceRiemannRochSource.constructedCanonical_isCanonical X) A H hA hpositive

end Smooth

end KltDP.Geometry.NefTwistedMaps
