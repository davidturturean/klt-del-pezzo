import KltDP.Geometry.CartierIdealSheafData
import KltDP.Geometry.ReducedWeilCartierEquations
import KltDP.Geometry.PrimeCurveSubscheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Reducedness of the original effective Cartier subscheme

Principal-ideal membership of an actual section germ is represented on
an actual smaller open: represent the stalk multiplier and use the
existing zero-germ restriction theorem. This needs no integral, affine
or Noetherian hypothesis on the scheme.

For the original effective Cartier divisor with Weil coefficients at
most one, the preceding actual stalk-quotient theorem therefore makes
the independently defined divisor ideal radical on every original open.
Its original scheme ideal data is radical. The existing quotient-chart
gluing theorem then proves reducedness of that actual glued subscheme.

The regular equation cover is derived from original effectiveness and
factoriality of the actual stalks. Separatedness is derived from the
original closed projective embedding. The original square-root data is
retained by the scheme ideal construction. No reduced scheme, stalk
isomorphism, local lifting, or desired ideal identity is an input.

This does not identify the actual closed subscheme with the manuscript's
named node union or identify its canonical section with the original
quadratic atlas. Smoothness and the branch regular-immersion statement
remain separate. Reuse: pinned original germs and radical ideals; the
project's original Cartier ideal, actual quotient reducedness, and
already constructed IdealSheafData.glueData/gluedTo.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Actual principal-ideal membership at a stalk holds on an actual
neighborhood with the original restriction maps and original generator. -/
theorem exists_restrict_mem_span_of_germ_mem_span
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hx : x ∈ U) (s d : Γ(X, U))
    (h : X.presheaf.germ U x hx s ∈
      Ideal.span ({X.presheaf.germ U x hx d} : Set (X.presheaf.stalk x))) :
    ∃ (V : X.Opens) (i : V ⟶ U), x ∈ V ∧
      X.presheaf.map i.op s ∈
        Ideal.span ({X.presheaf.map i.op d} : Set Γ(X, V)) := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp h
  obtain ⟨W, hxW, t, ht⟩ := X.presheaf.germ_exist x a
  let T : X.Opens := U ⊓ W
  let iU : T ⟶ U := homOfLE inf_le_left
  let iW : T ⟶ W := homOfLE inf_le_right
  have hxT : x ∈ T := ⟨hx, hxW⟩
  let z : Γ(X, T) := X.presheaf.map iU.op s -
    X.presheaf.map iU.op d * X.presheaf.map iW.op t
  have hz : X.presheaf.germ T x hxT z = 0 := by
    dsimp only [z]
    rw [map_sub, map_mul, X.presheaf.germ_res_apply iU x hxT s,
      X.presheaf.germ_res_apply iU x hxT d,
      X.presheaf.germ_res_apply iW x hxT t, ht, ha, sub_self]
  obtain ⟨V, i, hxV, hi⟩ :=
    X.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero T z ⟨x, hxT⟩ hz
  have hcomp (q : Γ(X, U)) : X.presheaf.map (i ≫ iU).op q =
      X.presheaf.map i.op (X.presheaf.map iU.op q) :=
    ConcreteCategory.congr_hom (X.presheaf.map_comp iU.op i.op) q
  refine ⟨V, i ≫ iU, hxV, Ideal.mem_span_singleton.mpr
    ⟨X.presheaf.map i.op (X.presheaf.map iW.op t), ?_⟩⟩
  rw [hcomp s, hcomp d]
  dsimp only [z] at hi
  rw [map_sub, map_mul, sub_eq_zero] at hi
  exact hi

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

local instance surfaceSeparated : X.toScheme.IsSeparated := by
  obtain ⟨n, i, hi, _⟩ := X.projective
  letI : IsClosedImmersion i := hi
  letI : (projectiveSpace k n).IsSeparated := by
    letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) :=
      MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := k)
    unfold projectiveSpace
    infer_instance
  constructor
  rw [← Limits.terminal.comp_from i]
  infer_instance

local instance surfaceMonoidal : MonoidalCategory X.toScheme.Modules :=
  Scheme.Modules.monoidalCategory X.toScheme

/-- The original divisor ideal is radical on every original open, by
the actual reduced coefficient-germ quotients and original sheaf locality. -/
theorem cartierSectionIdeal_isRadical
    [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]
    (E : CartierDivisor X.toScheme) (hE : EffectiveDivisor (X.cartierToWeilHom E))
    (hE_one : ∀ C, X.cartierToWeilHom E C ≤ 1) (W : X.toScheme.Opens) :
    (cartierSectionIdeal X.toScheme E W).IsRadical := by
  intro s hs
  obtain ⟨n, hn⟩ := hs
  apply cartierSectionIdeal_of_locally_mem X.toScheme E W s
  intro x hx
  obtain ⟨c, hxc⟩ := X.hasRegularCartierEquations_of_effective_weil E hE x
  let V : X.toScheme.Opens := W ⊓ c.chart.openSet
  have hxV : x ∈ V := ⟨hx, hxc⟩
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let i : V ⟶ W := homOfLE inf_le_left
  let d := RegularCartierEquationChart.restrict X.toScheme E c V
    (show V ≤ c.chart.openSet from inf_le_right)
  let t : Γ(X.toScheme, V) := X.toScheme.presheaf.map i.op s
  have hpow : t ^ n ∈ Ideal.span ({d.coefficient} : Set Γ(X.toScheme, V)) := by
    have h := cartierSectionIdeal_restrict X.toScheme E i (s ^ n) hn
    rw [map_pow] at h
    have heq : cartierSectionIdeal X.toScheme E V =
        Ideal.span ({d.coefficient} : Set Γ(X.toScheme, V)) :=
      cartierSectionIdeal_eq_span X.toScheme E d
    exact heq.le h
  have hgpow : (X.toScheme.presheaf.germ V x hxV t) ^ n ∈
      Ideal.span ({X.toScheme.presheaf.germ V x hxV d.coefficient} : Set (X.stalk x)) := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hpow
    refine Ideal.mem_span_singleton.mpr ⟨X.toScheme.presheaf.germ V x hxV a, ?_⟩
    simpa only [map_pow, map_mul] using
      congrArg (X.toScheme.presheaf.germ V x hxV) ha
  have hrad : (Ideal.span
      ({X.toScheme.presheaf.germ V x hxV d.coefficient} : Set (X.stalk x))).IsRadical :=
    (Ideal.isRadical_iff_quotient_reduced _).mpr
      (X.regularCartierEquation_stalk_quotient_isReduced E hE hE_one d ⟨x, hxV⟩)
  have hg : X.toScheme.presheaf.germ V x hxV t ∈ Ideal.span
      ({X.toScheme.presheaf.germ V x hxV d.coefficient} : Set (X.stalk x)) :=
    hrad ⟨n, hgpow⟩
  obtain ⟨N, j, hxN, hN⟩ := exists_restrict_mem_span_of_germ_mem_span
    X.toScheme V x hxV t d.coefficient hg
  letI : Nonempty N := ⟨⟨x, hxN⟩⟩
  let e := RegularCartierEquationChart.restrict X.toScheme E d N j.le
  refine ⟨N, j ≫ i, hxN, ?_⟩
  have heq : cartierSectionIdeal X.toScheme E N =
      Ideal.span ({e.coefficient} : Set Γ(X.toScheme, N)) :=
    cartierSectionIdeal_eq_span X.toScheme E e
  apply heq.ge
  change X.toScheme.presheaf.map (j ≫ i).op s ∈
    Ideal.span ({X.toScheme.presheaf.map j.op d.coefficient} : Set Γ(X.toScheme, N))
  rw [show X.toScheme.presheaf.map (j ≫ i).op s =
    X.toScheme.presheaf.map j.op (X.toScheme.presheaf.map i.op s) from
    ConcreteCategory.congr_hom (X.toScheme.presheaf.map_comp i.op j.op) s]
  exact hN

/-- The actual scheme ideal data of the original divisor is radical.
Its regular equation cover is derived from the original Weil effectivity. -/
theorem effectiveCartierIdealData_radical
    [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]
    (E : CartierDivisor X.toScheme) (hE : EffectiveDivisor (X.cartierToWeilHom E))
    (hE_one : ∀ C, X.cartierToWeilHom E C ≤ 1) (L : InvertibleSheaf X.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X.toScheme E) :
    let hD := X.hasRegularCartierEquations_of_effective_weil E hE
    let I := effectiveCartierIdealData X.toScheme E hD L e
    I.radical = I := by
  dsimp only
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.radical_ideal, effectiveCartierIdealData_ideal]
  exact (X.cartierSectionIdeal_isRadical E hE hE_one U.1).radical

/-- The original quotient-chart gluing is a reduced scheme. No different
subscheme, supplied stalk comparison, or supplied reducedness is used. -/
theorem effectiveCartierSubscheme_isReduced
    [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]
    (E : CartierDivisor X.toScheme) (hE : EffectiveDivisor (X.cartierToWeilHom E))
    (hE_one : ∀ C, X.cartierToWeilHom E C ≤ 1) (L : InvertibleSheaf X.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X.toScheme E) :
    let hD := X.hasRegularCartierEquations_of_effective_weil E hE
    let I := effectiveCartierIdealData X.toScheme E hD L e
    AlgebraicGeometry.IsReduced I.glueData.glued := by
  dsimp only
  apply Scheme.IdealSheafData.glued_isReduced
  exact X.effectiveCartierIdealData_radical E hE hE_one L e

end NormalProjectiveSurface
end KltDP.Geometry
