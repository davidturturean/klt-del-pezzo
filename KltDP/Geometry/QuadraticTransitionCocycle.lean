import KltDP.Geometry.TransitionUnitSections
import KltDP.Geometry.QuadraticCoverRescaling
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Actual quadratic transition maps on arbitrary common open subsets

The inputs are sections of the original structure sheaf, transition units,
and their literal branch equations. Restricting these equations constructs
the quotient algebra equivalences. The unit cocycle then proves composition
of the actual equivalences and the contravariant spectrum isomorphisms.

This adapter reuses `TransitionUnitGluing.IsCocycle.mul_res_of_le` and
`QuadraticCover.rescaleEquiv_trans`; it does not assume quotient transition
maps or their cocycle laws. The pinned `Scheme.Spec` functor supplies the
scheme maps. No affineness of the opens or global glued scheme is asserted.

Reuse review: pinned Mathlib's gluing and algebra-equivalence APIs were
checked against official Mathlib revision
80cbd0498ab39e21d24d6730b3f932cec672a702, `CategoryTheory/GlueData.lean`
and `AlgebraicGeometry/Gluing.lean` (Apache 2.0). The actual two-chart
construction in Vilin97/MazurTheorem revision
9327963d4ec14fba49c7b14b004fd00707ffc2e9,
`MazurTorsion/AlgebraicGeometry/XOneThirteenProjectiveCurve.lean`, was
also inspected (Apache 2.0). The new obligation here is the arbitrary-index
quadratic transition cocycle; no newer source is copied or imported.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.QuadraticTransitionCocycle

open TransitionUnitGluing QuadraticCover

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)

/-- The original transition unit restricted to an actual common open subset. -/
def restrictedUnit {i j : ι} {W : X.Opens} (hi : W ≤ U i) (hj : W ≤ U j) :
    Γ(X, W)ˣ :=
  Units.map (res X (le_inf hi hj)).toMonoidHom (g i j)

@[simp]
theorem restrictedUnit_val {i j : ι} {W : X.Opens} (hi : W ≤ U i) (hj : W ≤ U j) :
    (restrictedUnit X U g hi hj : Γ(X, W)) = res X (le_inf hi hj) (g i j) := rfl

/-- The original unit cocycle remains valid on every actual common open subset. -/
theorem restrictedUnit_mul (hc : IsCocycle X U g) {i j k : ι} {W : X.Opens}
    (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    restrictedUnit X U g hi hj * restrictedUnit X U g hj hk =
      restrictedUnit X U g hi hk := by
  apply Units.ext
  change res X (le_inf hi hj) (g i j) * res X (le_inf hj hk) (g j k) =
    res X (le_inf hi hk) (g i k)
  exact IsCocycle.mul_res_of_le X U g hc (le_inf (le_inf hi hj) hk)

@[simp]
theorem restrictedUnit_self (hc : IsCocycle X U g) {i : ι} {W : X.Opens}
    (hi : W ≤ U i) : restrictedUnit X U g hi hi = 1 := by
  apply Units.ext
  change res X (le_inf hi hi) (g i i) = 1
  rw [hc.unit_self i, map_one]

variable (s : ∀ i : ι, Γ(X, U i))
    (hs : ∀ i j : ι,
      res X (inf_le_left : U i ⊓ U j ≤ U i) (s i) =
        (g i j : Γ(X, U i ⊓ U j)) ^ 2 *
          res X (inf_le_right : U i ⊓ U j ≤ U j) (s j))

include hs in
/-- Restriction of the literal branch equation to a smaller actual open subset. -/
theorem branchCondition_of_le {i j : ι} {W : X.Opens}
    (hi : W ≤ U i) (hj : W ≤ U j) :
    res X hi (s i) = (restrictedUnit X U g hi hj : Γ(X, W)) ^ 2 * res X hj (s j) := by
  have h := congrArg (res X (le_inf hi hj)) (hs i j)
  simpa only [map_mul, map_pow, res_res, restrictedUnit_val] using h

/-- The actual quotient equivalence induced by a restricted transition unit. -/
def transitionEquiv {i j : ι} {W : X.Opens} (hi : W ≤ U i) (hj : W ≤ U j) :
    CoverAlgebra (res X hi (s i)) ≃ₐ[Γ(X, W)] CoverAlgebra (res X hj (s j)) :=
  rescaleEquiv (res X hi (s i)) (res X hj (s j)) (restrictedUnit X U g hi hj)
    (branchCondition_of_le X U g s hs hi hj)

@[simp]
theorem transitionEquiv_root {i j : ι} {W : X.Opens}
    (hi : W ≤ U i) (hj : W ≤ U j) :
    transitionEquiv X U g s hs hi hj (root (res X hi (s i))) =
      algebraMap Γ(X, W) (CoverAlgebra (res X hj (s j)))
        (res X (le_inf hi hj) (g i j)) * root (res X hj (s j)) :=
  rescaleEquiv_root _ _ _ _

@[simp]
theorem transitionEquiv_algebraMap {i j : ι} {W : X.Opens}
    (hi : W ≤ U i) (hj : W ≤ U j) (a : Γ(X, W)) :
    transitionEquiv X U g s hs hi hj
        (algebraMap Γ(X, W) (CoverAlgebra (res X hi (s i))) a) =
      algebraMap Γ(X, W) (CoverAlgebra (res X hj (s j))) a :=
  (transitionEquiv X U g s hs hi hj).commutes a

/-- The actual quotient transitions satisfy the arbitrary triple-overlap law. -/
theorem transitionEquiv_trans (hc : IsCocycle X U g) {i j k : ι} {W : X.Opens}
    (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    (transitionEquiv X U g s hs hi hj).trans (transitionEquiv X U g s hs hj hk) =
      transitionEquiv X U g s hs hi hk := by
  simpa only [transitionEquiv, restrictedUnit_mul X U g hc hi hj hk] using
    (rescaleEquiv_trans (res X hi (s i)) (res X hj (s j)) (res X hk (s k))
      (restrictedUnit X U g hi hj) (restrictedUnit X U g hj hk)
      (branchCondition_of_le X U g s hs hi hj)
      (branchCondition_of_le X U g s hs hj hk))

@[simp]
theorem transitionEquiv_self (hc : IsCocycle X U g) {i : ι} {W : X.Opens}
    (hi : W ≤ U i) :
    transitionEquiv X U g s hs hi hi =
      (AlgEquiv.refl : CoverAlgebra (res X hi (s i)) ≃ₐ[Γ(X, W)]
        CoverAlgebra (res X hi (s i))) := by
  simpa only [transitionEquiv, restrictedUnit_self X U g hc hi] using
    (rescaleEquiv_one (res X hi (s i)))

/-- Reversing the chart indices gives the inverse actual quotient equivalence. -/
theorem transitionEquiv_symm (hc : IsCocycle X U g) {i j : ι} {W : X.Opens}
    (hi : W ≤ U i) (hj : W ≤ U j) :
    (transitionEquiv X U g s hs hi hj).symm = transitionEquiv X U g s hs hj hi := by
  apply AlgEquiv.ext
  intro x
  apply (transitionEquiv X U g s hs hi hj).injective
  rw [AlgEquiv.apply_symm_apply]
  have h := AlgEquiv.congr_fun (transitionEquiv_trans X U g s hs hc hj hi hj) x
  rw [transitionEquiv_self X U g s hs hc hj] at h
  exact h.symm

/-- The induced spectrum isomorphism has the contravariant chart orientation. -/
def transitionSpecIso {i j : ι} {W : X.Opens} (hi : W ≤ U i) (hj : W ≤ U j) :
    Spec (.of (CoverAlgebra (res X hj (s j)))) ≅
      Spec (.of (CoverAlgebra (res X hi (s i)))) :=
  Scheme.Spec.mapIso
    (transitionEquiv X U g s hs hi hj).toRingEquiv.toCommRingCatIso.op

theorem transitionSpecIso_hom {i j : ι} {W : X.Opens}
    (hi : W ≤ U i) (hj : W ≤ U j) :
    (transitionSpecIso X U g s hs hi hj).hom =
      Spec.map (CommRingCat.ofHom (transitionEquiv X U g s hs hi hj).toRingHom) := rfl

/-- The spectrum transitions satisfy the actual contravariant triple-overlap law. -/
theorem transitionSpecIso_trans (hc : IsCocycle X U g) {i j k : ι} {W : X.Opens}
    (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    transitionSpecIso X U g s hs hj hk ≪≫ transitionSpecIso X U g s hs hi hj =
      transitionSpecIso X U g s hs hi hk := by
  apply Iso.ext
  change Spec.map (CommRingCat.ofHom (transitionEquiv X U g s hs hj hk).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (transitionEquiv X U g s hs hi hj).toRingHom) =
    Spec.map (CommRingCat.ofHom (transitionEquiv X U g s hs hi hk).toRingHom)
  rw [← Spec.map_comp]
  apply congrArg (fun f : CoverAlgebra (res X hi (s i)) →+*
      CoverAlgebra (res X hk (s k)) => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  exact AlgEquiv.congr_fun (transitionEquiv_trans X U g s hs hc hi hj hk) x

/-- Each spectrum transition preserves the actual common coefficient spectrum. -/
@[reassoc]
theorem transitionSpecIso_hom_toBase {i j : ι} {W : X.Opens}
    (hi : W ≤ U i) (hj : W ≤ U j) :
    (transitionSpecIso X U g s hs hi hj).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) (CoverAlgebra (res X hi (s i))))) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) (CoverAlgebra (res X hj (s j))))) := by
  rw [transitionSpecIso_hom, ← Spec.map_comp]
  apply congrArg (fun f : Γ(X, W) →+* CoverAlgebra (res X hj (s j)) =>
    Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro a
  exact transitionEquiv_algebraMap X U g s hs hi hj a

end KltDP.Geometry.QuadraticTransitionCocycle
