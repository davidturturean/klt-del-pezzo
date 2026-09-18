import KltDP.Geometry.QCartierPullbackClass
import KltDP.Geometry.DominantCartierPullbackModule
import KltDP.Geometry.PicardWeilClassHom
import KltDP.Geometry.InvertibleSheafSectionPowers

/-!
An actual pullback-line isomorphism with an original tensor power computes
the rational class of the original signed Cartier pullback. The module
comparison and both Cartier representatives are actual sheaf isomorphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.QCartierPullback

open InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : NormalProjectiveSurface k}
    (π : X.toScheme ⟶ Y.toScheme) [GenericPointPreserving π]

/-- An original tensor-power pullback isomorphism determines the actual
rational Cartier-Weil class, with the original exponent retained. -/
theorem rational_class_signed_pullback_of_power_iso
    (M : InvertibleSheaf X.toScheme) (C : CartierDivisor X.toScheme)
    (eM : M.obj ≅ cartierDivisorModule X.toScheme C)
    (A : InvertibleSheaf Y.toScheme) (B : CartierDivisor Y.toScheme)
    (eB : A.obj ≅ cartierDivisorModule Y.toScheme B)
    (m : ℕ) (e : (pullbackInvertibleSheaf π A).obj ≅ (power M m).obj) :
    X.rationalWeilClassMap
        (X.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom π B)) =
      (m : ℚ) • X.rationalWeilClassMap (X.rationalCartierToWeilHom C) := by
  let eSource : (power M m).obj ≅ cartierDivisorModule X.toScheme
      (DominantCartierPullback.pullbackHom π B) :=
    e.symm ≪≫ (schemeModulePullback π).mapIso eB ≪≫
      DominantCartierPullback.modulePullbackIso π B
  have hpower : Additive.ofMul (power M m).toPic = m • Additive.ofMul M.toPic := by
    rw [power_toPic, _root_.ofMul_pow]
  have hBclass := X.picardToWeilClassHom_of_module_iso
    (power M m) (DominantCartierPullback.pullbackHom π B) eSource
  have hCclass := X.picardToWeilClassHom_of_module_iso M C eM
  have hdiv : X.weilClassMap
      (X.cartierToWeilHom (DominantCartierPullback.pullbackHom π B)) =
      m • X.weilClassMap (X.cartierToWeilHom C) :=
    hBclass.symm.trans (((congrArg X.picardToWeilClassHom hpower).trans
      (X.picardToWeilClassHom.map_nsmul _ m)).trans
        (congrArg (fun v : X.WeilClassGroup => m • v) hCclass))
  exact ((congrArg X.weilClassRationalization hdiv).trans
    (X.weilClassRationalization.map_nsmul _ m)).trans
      (Nat.cast_smul_eq_nsmul ℚ m _).symm

end KltDP.Geometry.QCartierPullback
