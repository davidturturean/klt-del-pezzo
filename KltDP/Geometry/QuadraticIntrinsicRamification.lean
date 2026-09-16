import KltDP.Geometry.QuadraticKaehlerRamification
import KltDP.Geometry.QuadraticRootBaseChange

/-!
# The actual annihilator ramification scheme of a quadratic chart

The ideal here is the annihilator of the actual relative Kähler module.
Its actual quotient scheme is identified with the original root-zero and
branch quotient schemes, retaining the original closed immersion and base
map. The equality with the evaluated Jacobian ideal is proved, not assumed.

This uses the existing annihilator theorem and quotient-Spec maps. It does
not assert an unproved Fitting-ideal convention or global ideal-sheaf gluing.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.QuadraticCover

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The intrinsic annihilator of the original relative differential module. -/
def ramificationIdeal (s : R) : Ideal (CoverAlgebra s) :=
  Module.annihilator (CoverAlgebra s) (KaehlerDifferential R (CoverAlgebra s))

theorem ramificationIdeal_eq_rootIdeal (s : R) (h2 : IsUnit (2 : R)) :
    ramificationIdeal s = rootIdeal s :=
  kaehler_annihilator_eq_rootIdeal s h2

/-- The original evaluated Jacobian and intrinsic differential annihilator agree. -/
theorem derivativeIdeal_eq_ramificationIdeal (s : R) (h2 : IsUnit (2 : R)) :
    derivativeIdeal s = ramificationIdeal s :=
  (derivativeIdeal_eq_rootIdeal s h2).trans (ramificationIdeal_eq_rootIdeal s h2).symm

/-- The actual closed scheme defined by the intrinsic annihilator. -/
def ramificationScheme (s : R) : Scheme.{u} :=
  Spec (.of (CoverAlgebra s ⧸ ramificationIdeal s))

def ramificationι (s : R) : ramificationScheme s ⟶ affineScheme s :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ramificationIdeal s)))

instance ramificationι_isClosedImmersion (s : R) : IsClosedImmersion (ramificationι s) := by
  unfold ramificationι
  exact IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (ramificationIdeal s)))
    Ideal.Quotient.mk_surjective

/-- The intrinsic annihilator quotient is the actual root-zero scheme. -/
def ramificationIsoRoot (s : R) (h2 : IsUnit (2 : R)) :
    ramificationScheme s ≅ rootZeroScheme s :=
  Scheme.Spec.mapIso
    (Ideal.quotEquivOfEq (ramificationIdeal_eq_rootIdeal s h2)).symm.toCommRingCatIso.op

/-- The isomorphism preserves the original closed inclusion into the cover. -/
@[reassoc]
theorem ramificationIsoRoot_hom_ι (s : R) (h2 : IsUnit (2 : R)) :
    (ramificationIsoRoot s h2).hom ≫ rootZeroι s = ramificationι s := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  apply congrArg (fun f : CoverAlgebra s →+* (CoverAlgebra s ⧸ ramificationIdeal s) =>
    Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro a
  change (Ideal.quotEquivOfEq (ramificationIdeal_eq_rootIdeal s h2)).symm
    (Ideal.Quotient.mk (rootIdeal s) a) = Ideal.Quotient.mk (ramificationIdeal s) a
  rw [Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk]

/-- The actual annihilator ramification scheme maps isomorphically to the original branch. -/
def ramificationIsoBranch (s : R) (h2 : IsUnit (2 : R)) :
    ramificationScheme s ≅ branchScheme s :=
  ramificationIsoRoot s h2 ≪≫ rootZeroIsoBranch s

@[reassoc]
theorem ramificationIsoBranch_hom_toBase (s : R) (h2 : IsUnit (2 : R)) :
    (ramificationIsoBranch s h2).hom ≫ branchι s = ramificationι s ≫ toBase s := by
  simp only [ramificationIsoBranch, Iso.trans_hom, Category.assoc,
    rootZeroIsoBranch_hom_toBase, ramificationIsoRoot_hom_ι_assoc]

/-- The original coefficient/rescaling map preserves the actual intrinsic ideals. -/
theorem map_ramificationIdeal (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) (h2 : IsUnit (2 : R)) :
    Ideal.map (mappedRescaleHom f s t v h) (ramificationIdeal s) = ramificationIdeal t := by
  have h2S : IsUnit (2 : S) := by simpa only [map_ofNat] using h2.map f
  rw [ramificationIdeal_eq_rootIdeal s h2, ramificationIdeal_eq_rootIdeal t h2S]
  exact map_rootIdeal_mappedRescaleHom f s t v h

end KltDP.Geometry.QuadraticCover

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- The original atlas's coefficient map preserves the intrinsic ramification ideals. -/
theorem map_frame_ramificationIdeal {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V)
    (h2 : IsUnit (2 : Γ(X, V))) :
    Ideal.map (Spec.preimage (D.map hi hj hWV)).hom
        (ramificationIdeal (res X hi (D.sections i))) =
      ramificationIdeal (res X hj (D.sections j)) := by
  simp only [map, localMap, mappedRescaleMap, Spec.preimage_map, CommRingCat.hom_ofHom]
  exact map_ramificationIdeal _ _ _ _ _ h2

end KltDP.Geometry.QuadraticCoverAtlas.Data
