import KltDP.Geometry.SplitQuadraticCover

/-!
# Restriction compatibility of the split quadratic algebra

A homomorphism of the original base rings sending the chosen unit `u` to
`v` induces the actual coefficient-map homomorphism between the polynomial
quotients. It commutes with both evaluations and with the split product
equivalences. The resulting square of actual affine schemes also commutes.

This supplies the algebra and affine-scheme compatibility required when
gluing already trivialized local covers. It does not construct a global
line-bundle trivialization, a cover atlas, or its descent datum.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace KltDP.Geometry

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

theorem splitQuadraticPolynomial_map (f : R →+* S) (a : Rˣ) (b : Sˣ)
    (hab : f (a : R) = (b : S)) :
    (splitQuadraticPolynomial a).map f = splitQuadraticPolynomial b := by
  simp only [splitQuadraticPolynomial, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, map_pow, hab]

private theorem splitQuadraticIdeal_le_comap (f : R →+* S) (a : Rˣ) (b : Sˣ)
    (hab : f (a : R) = (b : S)) :
    Ideal.span {splitQuadraticPolynomial a} ≤
      (Ideal.span {splitQuadraticPolynomial b}).comap (Polynomial.mapRingHom f) := by
  apply (Ideal.span_singleton_le_iff_mem
    ((Ideal.span {splitQuadraticPolynomial b}).comap (Polynomial.mapRingHom f))).mpr
  change (splitQuadraticPolynomial a).map f ∈ Ideal.span {splitQuadraticPolynomial b}
  rw [splitQuadraticPolynomial_map f a b hab]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The actual quotient map induced by applying `f` to polynomial coefficients. -/
def splitQuadraticMap (f : R →+* S) (a : Rˣ) (b : Sˣ)
    (hab : f (a : R) = (b : S)) :
    SplitQuadraticAlgebra a →+* SplitQuadraticAlgebra b :=
  Ideal.quotientMap (Ideal.span {splitQuadraticPolynomial b})
    (Polynomial.mapRingHom f) (splitQuadraticIdeal_le_comap f a b hab)

@[simp]
theorem splitQuadraticMap_mk (f : R →+* S) (a : Rˣ) (b : Sˣ)
    (hab : f (a : R) = (b : S)) (p : R[X]) :
    splitQuadraticMap f a b hab (AdjoinRoot.mk (splitQuadraticPolynomial a) p) =
      AdjoinRoot.mk (splitQuadraticPolynomial b) (p.map f) :=
  Ideal.quotientMap_mk

@[simp]
theorem splitQuadraticMap_root (f : R →+* S) (a : Rˣ) (b : Sˣ)
    (hab : f (a : R) = (b : S)) :
    splitQuadraticMap f a b hab (AdjoinRoot.root (splitQuadraticPolynomial a)) =
      AdjoinRoot.root (splitQuadraticPolynomial b) := by
  simp only [AdjoinRoot.root, splitQuadraticMap_mk, Polynomial.map_X]

/-- The quotient map respects the actual base-ring maps. -/
@[simp]
theorem splitQuadraticMap_algebraMap (f : R →+* S) (a : Rˣ) (b : Sˣ)
    (hab : f (a : R) = (b : S)) (r : R) :
    splitQuadraticMap f a b hab (algebraMap R (SplitQuadraticAlgebra a) r) =
      algebraMap S (SplitQuadraticAlgebra b) (f r) := by
  change splitQuadraticMap f a b hab
    (AdjoinRoot.mk (splitQuadraticPolynomial a) (C r)) =
      AdjoinRoot.mk (splitQuadraticPolynomial b) (C (f r))
  rw [splitQuadraticMap_mk, Polynomial.map_C]

theorem splitQuadraticMap_id (a : Rˣ) :
    splitQuadraticMap (RingHom.id R) a a rfl = RingHom.id (SplitQuadraticAlgebra a) := by
  apply RingHom.ext
  intro x
  refine AdjoinRoot.induction_on (splitQuadraticPolynomial a) x ?_
  intro p
  simp only [splitQuadraticMap_mk, Polynomial.map_id, RingHom.id_apply]

/-- The coefficient-induced maps satisfy the actual composition law. -/
theorem splitQuadraticMap_comp (f : R →+* S) (g : S →+* T)
    (a : Rˣ) (b : Sˣ) (c : Tˣ)
    (hab : f (a : R) = (b : S)) (hbc : g (b : S) = (c : T)) :
    (splitQuadraticMap g b c hbc).comp (splitQuadraticMap f a b hab) =
      splitQuadraticMap (g.comp f) a c ((congrArg g hab).trans hbc) := by
  apply RingHom.ext
  intro x
  refine AdjoinRoot.induction_on (splitQuadraticPolynomial a) x ?_
  intro p
  simp only [RingHom.comp_apply, splitQuadraticMap_mk, Polynomial.map_map]

/-- Both evaluations commute with coefficient restriction. -/
theorem splitQuadraticAlgEquiv_naturality (f : R →+* S) (a : Rˣ) (b : Sˣ)
    (hab : f (a : R) = (b : S)) (hR : IsUnit (2 : R)) (hS : IsUnit (2 : S))
    (x : SplitQuadraticAlgebra a) :
    splitQuadraticAlgEquiv b hS (splitQuadraticMap f a b hab x) =
      (RingHom.prodMap f f) (splitQuadraticAlgEquiv a hR x) := by
  refine AdjoinRoot.induction_on (splitQuadraticPolynomial a) x ?_
  intro p
  rw [splitQuadraticMap_mk, splitQuadraticAlgEquiv_mk, splitQuadraticAlgEquiv_mk]
  apply Prod.ext
  · change (p.map f).eval (b : S) = f (p.eval (a : R))
    rw [← hab, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  · change (p.map f).eval (-(b : S)) = f (p.eval (-(a : R)))
    have hneg : f (-(a : R)) = -(b : S) := (f.map_neg _).trans (congrArg Neg.neg hab)
    rw [← hneg, Polynomial.eval_map, Polynomial.eval₂_at_apply]

theorem splitQuadraticEvalPositive_naturality (f : R →+* S) (a : Rˣ) (b : Sˣ)
    (hab : f (a : R) = (b : S)) (hR : IsUnit (2 : R)) (hS : IsUnit (2 : S)) :
    (splitQuadraticEvalPositive b hS).toRingHom.comp (splitQuadraticMap f a b hab) =
      f.comp (splitQuadraticEvalPositive a hR).toRingHom := by
  apply RingHom.ext
  intro x
  exact congrArg Prod.fst (splitQuadraticAlgEquiv_naturality f a b hab hR hS x)

theorem splitQuadraticEvalNegative_naturality (f : R →+* S) (a : Rˣ) (b : Sˣ)
    (hab : f (a : R) = (b : S)) (hR : IsUnit (2 : R)) (hS : IsUnit (2 : S)) :
    (splitQuadraticEvalNegative b hS).toRingHom.comp (splitQuadraticMap f a b hab) =
      f.comp (splitQuadraticEvalNegative a hR).toRingHom := by
  apply RingHom.ext
  intro x
  exact congrArg Prod.snd (splitQuadraticAlgEquiv_naturality f a b hab hR hS x)

/-- The two affine splittings are compatible with the actual base restriction morphism. -/
theorem splitQuadraticSpecIso_naturality (f : R →+* S) (a : Rˣ) (b : Sˣ)
    (hab : f (a : R) = (b : S)) (hR : IsUnit (2 : R)) (hS : IsUnit (2 : S)) :
    (splitQuadraticSpecIso b hS).inv ≫
        Spec.map (CommRingCat.ofHom (splitQuadraticMap f a b hab)) =
      coprod.map (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom f)) ≫
        (splitQuadraticSpecIso a hR).inv := by
  apply coprod.hom_ext
  · simp only [splitQuadraticSpecIso_inl_assoc,
      coprod.inl_map_assoc, splitQuadraticSpecIso_inl]
    rw [← Spec.map_comp, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
        ((splitQuadraticEvalPositive b hS).toRingHom.comp (splitQuadraticMap f a b hab))) =
      Spec.map (CommRingCat.ofHom (f.comp (splitQuadraticEvalPositive a hR).toRingHom))
    exact congrArg (fun h : SplitQuadraticAlgebra a →+* S => Spec.map (CommRingCat.ofHom h))
      (splitQuadraticEvalPositive_naturality f a b hab hR hS)
  · simp only [splitQuadraticSpecIso_inr_assoc,
      coprod.inr_map_assoc, splitQuadraticSpecIso_inr]
    rw [← Spec.map_comp, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
        ((splitQuadraticEvalNegative b hS).toRingHom.comp (splitQuadraticMap f a b hab))) =
      Spec.map (CommRingCat.ofHom (f.comp (splitQuadraticEvalNegative a hR).toRingHom))
    exact congrArg (fun h : SplitQuadraticAlgebra a →+* S => Spec.map (CommRingCat.ofHom h))
      (splitQuadraticEvalNegative_naturality f a b hab hR hS)

end KltDP.Geometry
