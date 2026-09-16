import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.RingTheory.Localization.Module

/-!
# The tilde of the ring is the actual structure-sheaf unit

The pinned tilde construction uses localized modules as its fibers, whereas
the structure sheaf uses localizations of rings. The canonical localization
equivalence identifies these two fibers for the module R. It preserves the
original numerator maps and the local-ring scalar actions.

The same local fraction witnesses then give maps in both directions on every
open. These maps are linear over the original section rings, are inverse,
and commute with the actual restrictions. They define the stated isomorphism
of module sheaves without assuming affine reconstruction or a unit comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable (R : Type u) [CommRing R]

/-- The canonical comparison between module and ring localizations at a prime,
linear over the original localized ring. -/
def unitFiberEquiv (p : PrimeSpectrum R) :
    LocalizedModule p.asIdeal.primeCompl R ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal :=
  (IsLocalizedModule.iso p.asIdeal.primeCompl
    (Algebra.linearMap R (Localization.AtPrime p.asIdeal))).extendScalarsOfIsLocalization
      p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)

/-- The fiber comparison preserves the original numerator map. -/
@[simp]
theorem unitFiberEquiv_mkLinearMap (p : PrimeSpectrum R) (r : R) :
    unitFiberEquiv R p (LocalizedModule.mkLinearMap p.asIdeal.primeCompl R r) =
      algebraMap R (Localization.AtPrime p.asIdeal) r := by
  change IsLocalizedModule.iso p.asIdeal.primeCompl
      (Algebra.linearMap R (Localization.AtPrime p.asIdeal)) (LocalizedModule.mk r 1) = _
  exact IsLocalizedModule.iso_mk_one p.asIdeal.primeCompl
    (Algebra.linearMap R (Localization.AtPrime p.asIdeal)) r

/-- Original R-scalars become their images in the local ring. -/
theorem unitFiberEquiv_smul (p : PrimeSpectrum R) (r : R)
    (s : LocalizedModule p.asIdeal.primeCompl R) :
    unitFiberEquiv R p (r • s) =
      algebraMap R (Localization.AtPrime p.asIdeal) r * unitFiberEquiv R p s := by
  change IsLocalizedModule.iso p.asIdeal.primeCompl
      (Algebra.linearMap R (Localization.AtPrime p.asIdeal)) (r • s) =
    algebraMap R (Localization.AtPrime p.asIdeal) r *
      IsLocalizedModule.iso p.asIdeal.primeCompl
        (Algebra.linearMap R (Localization.AtPrime p.asIdeal)) s
  rw [map_smul, Algebra.smul_def]

/-- Locally fractional module sections give locally fractional structure sections. -/
private def unitToStructure (U : (Spec (CommRingCat.of R)).Opens)
    (s : (ModuleCat.of R R).tilde.val.obj (op U)) :
    Γ(Spec (CommRingCat.of R), U) :=
  ⟨fun p => unitFiberEquiv R p.val (s.val p), by
    intro x
    obtain ⟨V, hx, i, m, d, hd⟩ := s.property x
    refine ⟨V, hx, i, m, d, ?_⟩
    intro y
    refine ⟨(hd y).1, ?_⟩
    have key := congrArg (unitFiberEquiv R y.val) (hd y).2
    rw [unitFiberEquiv_smul, unitFiberEquiv_mkLinearMap] at key
    exact (mul_comm _ _).trans key⟩

/-- Original structure sections give locally fractional module sections. -/
private def structureToUnit (U : (Spec (CommRingCat.of R)).Opens)
    (s : Γ(Spec (CommRingCat.of R), U)) :
    (ModuleCat.of R R).tilde.val.obj (op U) :=
  ⟨fun p => (unitFiberEquiv R p.val).symm (s.val p), by
    intro x
    obtain ⟨V, hx, i, m, d, hd⟩ := s.property x
    refine ⟨V, hx, i, m, d, ?_⟩
    intro y
    refine ⟨(hd y).1, ?_⟩
    apply (unitFiberEquiv R y.val).injective
    change unitFiberEquiv R y.val
        (d • (unitFiberEquiv R y.val).symm (s.val (i y))) =
      unitFiberEquiv R y.val (LocalizedModule.mkLinearMap y.val.asIdeal.primeCompl R m)
    rw [unitFiberEquiv_smul, LinearEquiv.apply_symm_apply, unitFiberEquiv_mkLinearMap]
    exact (mul_comm _ _).trans (hd y).2⟩

/-- The canonical equivalence on every open, with the actual section-ring scalars. -/
def unitSectionsEquiv (U : (Spec (CommRingCat.of R)).Opens) :
    (ModuleCat.of R R).tilde.val.obj (op U) ≃ₗ[Γ(Spec (CommRingCat.of R), U)]
      Γ(Spec (CommRingCat.of R), U) where
  toFun := unitToStructure R U
  invFun := structureToUnit R U
  left_inv s := by
    apply Subtype.ext
    funext p
    exact (unitFiberEquiv R p.val).symm_apply_apply (s.val p)
  right_inv s := by
    apply Subtype.ext
    funext p
    exact (unitFiberEquiv R p.val).apply_symm_apply (s.val p)
  map_add' s t := by
    apply Subtype.ext
    funext p
    exact (unitFiberEquiv R p.val).map_add (s.val p) (t.val p)
  map_smul' a s := by
    apply Subtype.ext
    funext p
    exact (unitFiberEquiv R p.val).map_smul (a.val p) (s.val p)

@[simp]
theorem unitSectionsEquiv_apply_val (U : (Spec (CommRingCat.of R)).Opens)
    (s : (ModuleCat.of R R).tilde.val.obj (op U)) (p : U) :
    (unitSectionsEquiv R U s).val p = unitFiberEquiv R p.val (s.val p) := rfl

@[simp]
theorem unitSectionsEquiv_symm_apply_val (U : (Spec (CommRingCat.of R)).Opens)
    (s : Γ(Spec (CommRingCat.of R), U)) (p : U) :
    ((unitSectionsEquiv R U).symm s).val p =
      (unitFiberEquiv R p.val).symm (s.val p) := rfl

/-- The tilde of R is the original structure sheaf regarded as its unit module. -/
def unitIso :
    (ModuleCat.of R R).tilde ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf := by
  apply (_root_.SheafOfModules.fullyFaithfulForget
    (Spec (CommRingCat.of R)).ringCatSheaf).preimageIso
  refine _root_.PresheafOfModules.isoMk
    (fun U => (unitSectionsEquiv R U.unop).toModuleIso) ?_
  intro U V i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext p
  rfl

/-- The sheaf isomorphism evaluates through the original localization equivalence. -/
@[simp]
theorem unitIso_hom_app_val (U : (Spec (CommRingCat.of R)).Opens)
    (s : (ModuleCat.of R R).tilde.val.obj (op U)) (p : U) :
    ((unitIso R).hom.val.app (op U) s).val p =
      unitFiberEquiv R p.val (s.val p) := rfl

/-- The inverse uses the inverse original localization equivalence on each fiber. -/
@[simp]
theorem unitIso_inv_app_val (U : (Spec (CommRingCat.of R)).Opens)
    (s : Γ(Spec (CommRingCat.of R), U)) (p : U) :
    ((unitIso R).inv.val.app (op U) s).val p =
      (unitFiberEquiv R p.val).symm (s.val p) := rfl

end KltDP.Geometry.AffineModuleTilde
