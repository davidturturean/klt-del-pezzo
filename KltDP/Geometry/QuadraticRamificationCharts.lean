import KltDP.Geometry.QuadraticRootIdeals
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual root-zero and branch quotient schemes

Killing the quadratic root gives exactly the original branch quotient.
The induced scheme isomorphism is over the original base. It commutes
with actual coefficient restrictions and unit generator changes, so it
retains the maps used in the original quadratic atlas. When two is a
unit, the actual derivative-zero subscheme is this same root-zero scheme.

This identifies actual quotient schemes and the Jacobian ideal of the
presentation. It does not substitute a reduced subscheme for the pulled
back branch (defined by the squared root ideal), or assert smoothness,
normality, a general Cartier-divisor pullback, or an unproved intrinsic
differential/Fitting-ideal characterization of ramification.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.QuadraticCover

variable {R S : Type u} [CommRing R] [CommRing S]

def branchScheme (s : R) : Scheme.{u} := Spec (.of (R ⧸ branchIdeal s))

def branchι (s : R) : branchScheme s ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (branchIdeal s)))

instance branchι_isClosedImmersion (s : R) : IsClosedImmersion (branchι s) := by
  unfold branchι
  exact IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (branchIdeal s))) Ideal.Quotient.mk_surjective

def rootZeroScheme (s : R) : Scheme.{u} :=
  Spec (.of (CoverAlgebra s ⧸ rootIdeal s))

def rootZeroι (s : R) : rootZeroScheme s ⟶ affineScheme s :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (rootIdeal s)))

instance rootZeroι_isClosedImmersion (s : R) : IsClosedImmersion (rootZeroι s) := by
  unfold rootZeroι
  exact IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (rootIdeal s))) Ideal.Quotient.mk_surjective

/-- The actual root-zero scheme is isomorphic to the original branch scheme. -/
def rootZeroIsoBranch (s : R) : rootZeroScheme s ≅ branchScheme s :=
  Scheme.Spec.mapIso (rootQuotientEquiv s).symm.toRingEquiv.toCommRingCatIso.op

/-- The quotient-scheme identification retains the actual original base map. -/
@[reassoc]
theorem rootZeroIsoBranch_hom_toBase (s : R) :
    (rootZeroIsoBranch s).hom ≫ branchι s = rootZeroι s ≫ toBase s := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg (fun f : R →+* (CoverAlgebra s ⧸ rootIdeal s) =>
    Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro a
  exact rootQuotientEquiv_symm_mk s a

/-- The actual quotient map of branch schemes under a coefficient restriction. -/
def branchQuotientMap (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) : (R ⧸ branchIdeal s) →+* (S ⧸ branchIdeal t) :=
  Ideal.quotientMap (branchIdeal t) f
    (Ideal.map_le_iff_le_comap.mp (le_of_eq (map_branchIdeal_rescale f s t v h)))

/-- The original quadratic coordinate map descends to the actual root-zero quotients. -/
def rootZeroQuotientMap (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) :
    (CoverAlgebra s ⧸ rootIdeal s) →+* (CoverAlgebra t ⧸ rootIdeal t) :=
  Ideal.quotientMap (rootIdeal t) (mappedRescaleHom f s t v h)
    (Ideal.map_le_iff_le_comap.mp
      (le_of_eq (map_rootIdeal_mappedRescaleHom f s t v h)))

/-- Evaluation at the actual zero root commutes with the original coefficient and rescaling maps. -/
theorem rootQuotientEquiv_naturality (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) :
    (rootQuotientEquiv t).toRingHom.comp (rootZeroQuotientMap f s t v h) =
      (branchQuotientMap f s t v h).comp (rootQuotientEquiv s).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply coverRingHom_ext
  · intro a
    change (rootQuotientEquiv t)
        (rootZeroQuotientMap f s t v h
          (Ideal.Quotient.mk (rootIdeal s) (algebraMap R (CoverAlgebra s) a))) =
      branchQuotientMap f s t v h
        ((rootQuotientEquiv s)
          (Ideal.Quotient.mk (rootIdeal s) (algebraMap R (CoverAlgebra s) a)))
    simp only [RingHom.comp_apply, rootZeroQuotientMap, branchQuotientMap,
      Ideal.quotientMap_mk, mappedRescaleHom_algebraMap, rootQuotientEquiv_mk_algebraMap]
  · simp only [RingHom.comp_apply, rootZeroQuotientMap, branchQuotientMap,
      Ideal.quotientMap_mk, mappedRescaleHom_root, map_mul, rootQuotient_mk_root,
      mul_zero, map_zero]

def branchSchemeMap (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) : branchScheme t ⟶ branchScheme s :=
  Spec.map (CommRingCat.ofHom (branchQuotientMap f s t v h))

def rootZeroSchemeMap (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) : rootZeroScheme t ⟶ rootZeroScheme s :=
  Spec.map (CommRingCat.ofHom (rootZeroQuotientMap f s t v h))

/-- The branch/root scheme identifications commute with the original atlas coordinate maps. -/
@[reassoc]
theorem rootZeroIsoBranch_naturality (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) :
    rootZeroSchemeMap f s t v h ≫ (rootZeroIsoBranch s).hom =
      (rootZeroIsoBranch t).hom ≫ branchSchemeMap f s t v h := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg (fun k : (R ⧸ branchIdeal s) →+* (CoverAlgebra t ⧸ rootIdeal t) =>
    Spec.map (CommRingCat.ofHom k))
  apply RingHom.ext
  intro a
  apply (rootQuotientEquiv t).injective
  have h' := RingHom.congr_fun (rootQuotientEquiv_naturality f s t v h)
    ((rootQuotientEquiv s).symm a)
  change (rootQuotientEquiv t)
      (rootZeroQuotientMap f s t v h ((rootQuotientEquiv s).symm a)) =
    (rootQuotientEquiv t)
      ((rootQuotientEquiv t).symm (branchQuotientMap f s t v h a))
  change (rootQuotientEquiv t)
      (rootZeroQuotientMap f s t v h ((rootQuotientEquiv s).symm a)) =
    branchQuotientMap f s t v h
      ((rootQuotientEquiv s) ((rootQuotientEquiv s).symm a)) at h'
  simpa only [AlgEquiv.apply_symm_apply] using h'

/-- The quotient chart map commutes with the actual original quadratic scheme map. -/
@[reassoc]
theorem rootZeroSchemeMap_ι (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) :
    rootZeroSchemeMap f s t v h ≫ rootZeroι s =
      rootZeroι t ≫ mappedRescaleMap f s t v h := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The actual Jacobian-zero scheme of the chosen quadratic presentation. -/
def derivativeZeroScheme (s : R) : Scheme.{u} :=
  Spec (.of (CoverAlgebra s ⧸ derivativeIdeal s))

/-- In characteristic away from two, the derivative-zero scheme is the root-zero scheme. -/
def derivativeZeroIsoRoot (s : R) (h2 : IsUnit (2 : R)) :
    derivativeZeroScheme s ≅ rootZeroScheme s :=
  Scheme.Spec.mapIso
    (Ideal.quotEquivOfEq (derivativeIdeal_eq_rootIdeal s h2)).symm.toCommRingCatIso.op

/-- Consequently its actual quotient scheme is isomorphic to the original branch quotient. -/
def derivativeZeroIsoBranch (s : R) (h2 : IsUnit (2 : R)) :
    derivativeZeroScheme s ≅ branchScheme s :=
  derivativeZeroIsoRoot s h2 ≪≫ rootZeroIsoBranch s

end KltDP.Geometry.QuadraticCover

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover QuadraticTransitionCocycle

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- The actual root-zero chart map induced by the original quadratic atlas map. -/
def rootZeroFrameMap {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V) :
    rootZeroScheme (res X hj (D.sections j)) ⟶ rootZeroScheme (res X hi (D.sections i)) :=
  rootZeroSchemeMap (res X hWV) (res X hi (D.sections i)) (res X hj (D.sections j))
    (restrictedUnit X D.opens D.units (hWV.trans hi) hj)
    (by simpa only [res_res] using
      branchCondition_of_le X D.opens D.units D.sections D.branch (hWV.trans hi) hj)

/-- Its closed inclusion commutes with the original actual map of cover charts. -/
@[reassoc]
theorem rootZeroFrameMap_ι {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V) :
    D.rootZeroFrameMap hi hj hWV ≫ rootZeroι (res X hi (D.sections i)) =
      rootZeroι (res X hj (D.sections j)) ≫ D.map hi hj hWV :=
  rootZeroSchemeMap_ι _ _ _ _ _

end KltDP.Geometry.QuadraticCoverAtlas.Data
