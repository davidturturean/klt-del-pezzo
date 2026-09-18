import KltDP.Geometry.ProperGlobalSectionsFinite
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Actual affine images of proper integral schemes

The original global section ring is a field. The original Gamma-Spec
adjunction factors a morphism to an affine scheme through its spectrum,
whose underlying point space is a singleton. This also applies when
the image lies in an actual affine open of an arbitrary target scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProperIntegralAffineImage

variable {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
  (f : Y ⟶ Spec (CommRingCat.of k)) [UniversallyClosed f]

include f

/-- The image of any actual morphism from the original universally
closed integral scheme to an affine scheme has at most one point. -/
theorem range_subsingleton {Z : Scheme.{u}} [IsAffine Z] (g : Y ⟶ Z) :
    (Set.range g.base).Subsingleton := by
  letI := (isField_of_universallyClosed k f).toField
  letI : Subsingleton (Spec Γ(Y, ⊤)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Γ(Y, ⊤)))
  have hfac : Y.toSpecΓ ≫ Spec.map g.appTop ≫ Z.isoSpec.inv = g := by
    rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv,
      Category.comp_id]
  have heval (y : Y) : g.base y =
      Z.isoSpec.inv.base ((Spec.map g.appTop).base (Y.toSpecΓ.base y)) := by
    simpa only [Scheme.comp_base_apply] using
      (congrArg (fun a : Y ⟶ Z => a.base y) hfac).symm
  rintro _ ⟨y, rfl⟩ _ ⟨z, rfl⟩
  exact (heval y).trans ((congrArg
    (fun a : Spec Γ(Y, ⊤) => Z.isoSpec.inv.base ((Spec.map g.appTop).base a))
    (Subsingleton.elim (Y.toSpecΓ.base y) (Y.toSpecΓ.base z))).trans (heval z).symm)

/-- An original morphism whose image lies in one original affine open
has singleton image; the lift through that open is constructed. -/
theorem range_subsingleton_of_affine_open {Z : Scheme.{u}} (g : Y ⟶ Z)
    (U : Z.Opens) (hU : IsAffineOpen U) (himage : Set.range g.base ⊆ U) :
    (Set.range g.base).Subsingleton := by
  letI : IsAffine U.toScheme := hU
  have hlift : Set.range g.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact himage
  let l : Y ⟶ U.toScheme := IsOpenImmersion.lift U.ι g hlift
  have hfac : l ≫ U.ι = g := IsOpenImmersion.lift_fac U.ι g hlift
  have hs := range_subsingleton f l
  rintro _ ⟨y, rfl⟩ _ ⟨z, rfl⟩
  have h := congrArg U.ι.base (hs (Set.mem_range_self y) (Set.mem_range_self z))
  simpa only [← Scheme.comp_base_apply, hfac] using h

end KltDP.Geometry.ProperIntegralAffineImage
