/-
Original project adapter developed for KltDelPezzoLean.
Released under Apache 2.0; the license text is archived at
docs/reuse_sources/sheaf_generating_sections_map/sources/LICENSE.
This proof composes existing proved APIs; it is not a port of an upstream
finite-module-to-tilde implementation. API sources are bound in the dossier
docs/reuse_sources/sheaf_generating_sections_map/source_bindings.json.
-/
import KltDP.Compatibility.SheafGeneratingSectionsMap
import KltDP.Geometry.AffineModulePresentationCounit
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite modules give finite-type original tilde sheaves

The pinned finite-free surjection is transported through the original finite
module coproduct and the actual tilde functor. Its proved left adjoint preserves
the epimorphism, and the existing coproduct comparison identifies the source
with the actual free sheaf. Finite generating sections then restrict to the
original Over-site by `SheafGeneratingSectionsMap`.

The conclusion concerns the pinned `M.tilde`, with no Noetherian assumption,
replacement sheaf, coherent-sheaf assertion, or finite-type conclusion as input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (R : Type u) [CommRing R]

/-- The finite categorical coproduct is the actual finite product module.
Using the arbitrary-universe product comparison retains `ULift` indices. -/
def finiteCoproductIsoPi (I : Type u) [Finite I] :
    (∐ (fun _ : I => ModuleCat.of R R)) ≅ ModuleCat.of R (I → R) :=
  (biproductIso (fun _ : I => ModuleCat.of R R)).symm ≪≫
    ModuleCat.piIsoPi (fun _ : I => ModuleCat.of R R)

/-- Every actual finite module has a finite original sheaf-free epimorphism
onto its original tilde sheaf. -/
theorem exists_finite_free_epi (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ (n : ℕ)
      (p : _root_.SheafOfModules.free
        (R := (Spec (.of R)).ringCatSheaf) (ULift.{u} (Fin n)) ⟶ M.tilde),
      Epi p := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let q : ModuleCat.of R (ULift.{u} (Fin n) → R) ⟶ M := ModuleCat.ofHom
    { toFun x := f (fun i => x ⟨i⟩)
      map_add' x y := by
        change f ((fun i => x ⟨i⟩) + fun i => y ⟨i⟩) = _
        exact f.map_add _ _
      map_smul' r x := by
        change f (r • fun i => x ⟨i⟩) = _
        exact f.map_smul r _ }
  have hq : Function.Surjective q := by
    intro m
    obtain ⟨x, hx⟩ := hf m
    exact ⟨fun i => x i.down, hx⟩
  letI : Epi q := (ModuleCat.epi_iff_surjective q).mpr hq
  let e := finiteCoproductIsoPi R (ULift.{u} (Fin n))
  let p₀ := e.hom ≫ q
  letI : Epi p₀ := inferInstanceAs (Epi (e.hom ≫ q))
  let p := (freeCoproductIso R (ULift.{u} (Fin n))).inv ≫ (functor R).map p₀
  exact ⟨n, p, inferInstanceAs (Epi
    ((freeCoproductIso R (ULift.{u} (Fin n))).inv ≫ (functor R).map p₀))⟩

/-- Finite generation of the actual module gives finite type of its original
tilde sheaf, using the actual finite-free epimorphism and Over-site generators. -/
theorem isFiniteType_of_finite (M : ModuleCat.{u} R) [Module.Finite R M] :
    _root_.SheafOfModules.IsFiniteType M.tilde := by
  obtain ⟨n, p, hp⟩ := exists_finite_free_epi R M
  letI : Epi p := hp
  exact _root_.SheafOfModules.isFiniteType_of_free_epi
    (R := (Spec (.of R)).ringCatSheaf) (M := M.tilde)
    (I := ULift.{u} (Fin n)) (p := p)

end KltDP.Geometry.AffineModuleTilde
