import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Algebra.Algebra.Prod
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Tactic.Ring

/-!
# A split quadratic algebra and its actual affine scheme

For a unit `u` of a commutative ring in which two is invertible, the actual
quotient `R[t]/(t²-u²)` is isomorphic as an `R`-algebra to `R × R`.
The two coordinates evaluate polynomials at `u` and `-u`. Applying the
pinned spectrum and coproduct constructions gives an actual scheme
isomorphism and identifies its two inclusion maps.

The proof reuses the pinned Chinese remainder theorem, the linear-factor
polynomial quotient equivalence, and `coprodSpec`. It does not assume or
prove splitting of arbitrary covers, line bundles, rational trees, or
branched surface covers. The required tree trivialization and compatibility
of local algebra isomorphisms with restrictions remain separate adapters.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace KltDP.Geometry

variable {R : Type u} [CommRing R]

/-- The original quadratic polynomial, before taking any quotient. -/
def splitQuadraticPolynomial (u : Rˣ) : R[X] :=
  X ^ 2 - C ((u : R) ^ 2)

/-- The actual polynomial quotient, with its existing ring and algebra structures. -/
abbrev SplitQuadraticAlgebra (u : Rˣ) : Type u :=
  AdjoinRoot (splitQuadraticPolynomial u)

private def positiveRootIdeal (u : Rˣ) : Ideal R[X] :=
  Ideal.span {X - C (u : R)}

private def negativeRootIdeal (u : Rˣ) : Ideal R[X] :=
  Ideal.span {X - C (-(u : R))}

theorem splitQuadraticPolynomial_factor (u : Rˣ) :
    splitQuadraticPolynomial u = (X - C (u : R)) * (X - C (-(u : R))) := by
  simp only [splitQuadraticPolynomial, map_pow, map_neg]
  ring

private theorem rootIdeals_coprime (u : Rˣ) (h2 : IsUnit (2 : R)) :
    IsCoprime (positiveRootIdeal u) (negativeRootIdeal u) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
  apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
  have hdiff : (u : R) - (-(u : R)) = (2 : R) * (u : R) := by ring
  rw [hdiff]
  exact h2.mul u.isUnit

private theorem quadratic_span_eq (u : Rˣ) :
    Ideal.span {splitQuadraticPolynomial u} = positiveRootIdeal u * negativeRootIdeal u := by
  rw [positiveRootIdeal, negativeRootIdeal,
    Ideal.span_singleton_mul_span_singleton, splitQuadraticPolynomial_factor]

private def splitQuadraticCRT (u : Rˣ) (h2 : IsUnit (2 : R)) :
    SplitQuadraticAlgebra u ≃+*
      (R[X] ⧸ positiveRootIdeal u) × (R[X] ⧸ negativeRootIdeal u) :=
  (Ideal.quotEquivOfEq (quadratic_span_eq u)).trans
    (Ideal.quotientMulEquivQuotientProd _ _ (rootIdeals_coprime u h2))

private theorem quotient_factor_quotEquivOfEq_mk {A : Type u} [CommRing A]
    (I J K : Ideal A) (h : I = J) (hJK : J ≤ K) (p : A) :
    Ideal.Quotient.factor hJK (Ideal.quotEquivOfEq h (Ideal.Quotient.mk I p)) =
      Ideal.Quotient.mk K p :=
  (congrArg (Ideal.Quotient.factor hJK) (Ideal.quotEquivOfEq_mk h p)).trans
    (Ideal.Quotient.factor_mk hJK p)

private theorem splitQuadraticCRT_fst_mk (u : Rˣ) (h2 : IsUnit (2 : R)) (p : R[X]) :
    (splitQuadraticCRT u h2 (AdjoinRoot.mk (splitQuadraticPolynomial u) p)).1 =
      Ideal.Quotient.mk (positiveRootIdeal u) p := by
  simp only [splitQuadraticCRT, RingEquiv.trans_apply, AdjoinRoot.mk,
    Ideal.quotientMulEquivQuotientProd_fst]
  exact quotient_factor_quotEquivOfEq_mk (Ideal.span {splitQuadraticPolynomial u})
    (positiveRootIdeal u * negativeRootIdeal u) (positiveRootIdeal u)
    (quadratic_span_eq u) Ideal.mul_le_right p

private theorem splitQuadraticCRT_snd_mk (u : Rˣ) (h2 : IsUnit (2 : R)) (p : R[X]) :
    (splitQuadraticCRT u h2 (AdjoinRoot.mk (splitQuadraticPolynomial u) p)).2 =
      Ideal.Quotient.mk (negativeRootIdeal u) p := by
  simp only [splitQuadraticCRT, RingEquiv.trans_apply, AdjoinRoot.mk,
    Ideal.quotientMulEquivQuotientProd_snd]
  exact quotient_factor_quotEquivOfEq_mk (Ideal.span {splitQuadraticPolynomial u})
    (positiveRootIdeal u * negativeRootIdeal u) (negativeRootIdeal u)
    (quadratic_span_eq u) Ideal.mul_le_left p

private def splitQuadraticRingEquiv (u : Rˣ) (h2 : IsUnit (2 : R)) :
    SplitQuadraticAlgebra u ≃+* R × R :=
  (splitQuadraticCRT u h2).trans
    (RingEquiv.prodCongr
      (Polynomial.quotientSpanXSubCAlgEquiv (u : R)).toRingEquiv
      (Polynomial.quotientSpanXSubCAlgEquiv (-(u : R))).toRingEquiv)

private theorem splitQuadraticRingEquiv_mk (u : Rˣ) (h2 : IsUnit (2 : R)) (p : R[X]) :
    splitQuadraticRingEquiv u h2 (AdjoinRoot.mk (splitQuadraticPolynomial u) p) =
      (p.eval (u : R), p.eval (-(u : R))) := by
  apply Prod.ext
  · change Polynomial.quotientSpanXSubCAlgEquiv (u : R)
      ((splitQuadraticCRT u h2 (AdjoinRoot.mk (splitQuadraticPolynomial u) p)).1) = _
    rw [splitQuadraticCRT_fst_mk]
    change Polynomial.quotientSpanXSubCAlgEquiv (u : R)
      (Ideal.Quotient.mk (Ideal.span {X - C (u : R)}) p) = p.eval (u : R)
    exact Polynomial.quotientSpanXSubCAlgEquiv_mk (u : R) p
  · change Polynomial.quotientSpanXSubCAlgEquiv (-(u : R))
      ((splitQuadraticCRT u h2 (AdjoinRoot.mk (splitQuadraticPolynomial u) p)).2) = _
    rw [splitQuadraticCRT_snd_mk]
    change Polynomial.quotientSpanXSubCAlgEquiv (-(u : R))
      (Ideal.Quotient.mk (Ideal.span {X - C (-(u : R))}) p) = p.eval (-(u : R))
    exact Polynomial.quotientSpanXSubCAlgEquiv_mk (-(u : R)) p

/-- The quadratic quotient splits as an actual algebra over the original ring. -/
def splitQuadraticAlgEquiv (u : Rˣ) (h2 : IsUnit (2 : R)) :
    SplitQuadraticAlgebra u ≃ₐ[R] R × R :=
  AlgEquiv.ofRingEquiv (f := splitQuadraticRingEquiv u h2) (by
    intro r
    change splitQuadraticRingEquiv u h2
      (AdjoinRoot.mk (splitQuadraticPolynomial u) (C r)) = (r, r)
    rw [splitQuadraticRingEquiv_mk]
    simp only [Polynomial.eval_C])

@[simp]
theorem splitQuadraticAlgEquiv_mk (u : Rˣ) (h2 : IsUnit (2 : R)) (p : R[X]) :
    splitQuadraticAlgEquiv u h2 (AdjoinRoot.mk (splitQuadraticPolynomial u) p) =
      (p.eval (u : R), p.eval (-(u : R))) :=
  splitQuadraticRingEquiv_mk u h2 p

/-- The original base ring maps diagonally, not through a chosen scalar action. -/
@[simp]
theorem splitQuadraticAlgEquiv_algebraMap (u : Rˣ) (h2 : IsUnit (2 : R)) (r : R) :
    splitQuadraticAlgEquiv u h2 (algebraMap R (SplitQuadraticAlgebra u) r) = (r, r) :=
  (splitQuadraticAlgEquiv u h2).commutes r

/-- The two actual values of the adjoined root. -/
@[simp]
theorem splitQuadraticAlgEquiv_root (u : Rˣ) (h2 : IsUnit (2 : R)) :
    splitQuadraticAlgEquiv u h2 (AdjoinRoot.root (splitQuadraticPolynomial u)) =
      ((u : R), -(u : R)) := by
  simpa only [AdjoinRoot.root, Polynomial.eval_X] using splitQuadraticAlgEquiv_mk u h2 X

/-- The first actual algebra map is evaluation at the positive root. -/
def splitQuadraticEvalPositive (u : Rˣ) (h2 : IsUnit (2 : R)) :
    SplitQuadraticAlgebra u →ₐ[R] R :=
  (AlgHom.fst R R R).comp (splitQuadraticAlgEquiv u h2).toAlgHom

/-- The second actual algebra map is evaluation at the negative root. -/
def splitQuadraticEvalNegative (u : Rˣ) (h2 : IsUnit (2 : R)) :
    SplitQuadraticAlgebra u →ₐ[R] R :=
  (AlgHom.snd R R R).comp (splitQuadraticAlgEquiv u h2).toAlgHom

@[simp]
theorem splitQuadraticEvalPositive_mk (u : Rˣ) (h2 : IsUnit (2 : R)) (p : R[X]) :
    splitQuadraticEvalPositive u h2 (AdjoinRoot.mk (splitQuadraticPolynomial u) p) =
      p.eval (u : R) :=
  congrArg Prod.fst (splitQuadraticAlgEquiv_mk u h2 p)

@[simp]
theorem splitQuadraticEvalNegative_mk (u : Rˣ) (h2 : IsUnit (2 : R)) (p : R[X]) :
    splitQuadraticEvalNegative u h2 (AdjoinRoot.mk (splitQuadraticPolynomial u) p) =
      p.eval (-(u : R)) :=
  congrArg Prod.snd (splitQuadraticAlgEquiv_mk u h2 p)

/-- Spectrum of the actual quadratic quotient is the actual coproduct of two affine schemes. -/
def splitQuadraticSpecIso (u : Rˣ) (h2 : IsUnit (2 : R)) :
    Spec (.of (SplitQuadraticAlgebra u)) ≅ Spec (.of R) ⨿ Spec (.of R) :=
  (Scheme.Spec.mapIso (splitQuadraticAlgEquiv u h2).toRingEquiv.symm.toCommRingCatIso.op) ≪≫
    (asIso (AlgebraicGeometry.coprodSpec R R)).symm

/-- The first component is the morphism induced by evaluation at `u`. -/
@[simp, reassoc]
theorem splitQuadraticSpecIso_inl (u : Rˣ) (h2 : IsUnit (2 : R)) :
    coprod.inl ≫ (splitQuadraticSpecIso u h2).inv =
      Spec.map (CommRingCat.ofHom (splitQuadraticEvalPositive u h2).toRingHom) := by
  change coprod.inl ≫
      (coprodSpec R R ≫ Spec.map
        (CommRingCat.ofHom (splitQuadraticAlgEquiv u h2).toRingHom)) = _
  rw [← Category.assoc, coprodSpec_inl, ← Spec.map_comp]
  rfl

/-- The second component is the morphism induced by evaluation at `-u`. -/
@[simp, reassoc]
theorem splitQuadraticSpecIso_inr (u : Rˣ) (h2 : IsUnit (2 : R)) :
    coprod.inr ≫ (splitQuadraticSpecIso u h2).inv =
      Spec.map (CommRingCat.ofHom (splitQuadraticEvalNegative u h2).toRingHom) := by
  change coprod.inr ≫
      (coprodSpec R R ≫ Spec.map
        (CommRingCat.ofHom (splitQuadraticAlgEquiv u h2).toRingHom)) = _
  rw [← Category.assoc, coprodSpec_inr, ← Spec.map_comp]
  rfl

end KltDP.Geometry
