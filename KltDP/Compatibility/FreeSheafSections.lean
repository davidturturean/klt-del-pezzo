import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.LinearAlgebra.StdBasis

/-!
# The sections of a finite free sheaf of modules, and their tautological basis

`SheafOfModules.free I` is a **sheaf** coproduct, `∐ (fun _ : I => unit R)`, so its sections over an
object of the site are not definitionally `I → R.val.obj W`. For a **finite** index they are
isomorphic to it: a finite coproduct in a preadditive category is a biproduct, hence also a product,
and evaluation of sheaves of modules preserves limits (pinned
`SheafOfModules.evaluationPreservesLimitsOfSize`).

* **`evalFan`, `evalFanIsLimit`**: the evaluated free sheaf, exhibited as a limit fan over the
  evaluated summands. Stating it as a fan rather than composing comparison isomorphisms is what
  makes the coordinates computable: the fan's legs are written down, and
  `IsLimit.conePointUniqueUpToIso_hom_comp` reads them off in one step.
* **`freeEvalIso`**: `(free I).val.obj W ≅ ModuleCat.of (R.val.obj W) (I → R.val.obj W)`, with
  **`freeEvalIso_hom_apply`** giving its coordinates.
* **`freeEvalIso_hom_freeSection`**: it carries the pinned tautological section `freeSection i` to
  the standard vector `Pi.single i 1`.
* **`freeSectionsBasis`**: hence `Basis I (R.val.obj W) ((free I).val.obj W)`, and
  **`freeSectionsBasis_apply`** identifies its vectors with the tautological sections.
* **`freeSectionsBasis_map`**: **the basis is compatible with restriction** — the basis vector over
  `W` restricts to the basis vector over `W'` along every arrow. This is not an extra argument: the
  basis vectors are the values of *one* element of `(free I).sections`, so the compatibility is the
  `sections` property itself.

That last point is why the basis is stated through `freeSection` rather than through the isomorphism
alone. A consumer that needs a frame on every object below a chart needs its frames to restrict to
one another, and reading them off a fixed family of sections is what makes that free rather than a
naturality chase.

Nothing is admitted here. Nothing in this module is specific to schemes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u₁

namespace KltDP.Compatibility.FreeSheafSections

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}

/-- Finite biproducts exist in a category of sheaves of modules: it is preadditive and has finite
limits, hence finite products. -/
local instance sheafOfModulesHasFiniteBiproducts (R : Sheaf J RingCat.{u}) :
    HasFiniteBiproducts (_root_.SheafOfModules.{u} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- Evaluation of sheaves of modules at an object is additive: it is the composite of the additive
forgetful functor with the additive evaluation of presheaves of modules. The pinned `evaluation` is
a plain `def`, so instance search does not see through it. -/
local instance evaluationAdditive (R : Sheaf J RingCat.{u}) (W : Cᵒᵖ) :
    (_root_.SheafOfModules.evaluation R W).Additive :=
  inferInstanceAs ((_root_.SheafOfModules.forget R ⋙
    PresheafOfModules.evaluation R.val W).Additive)

variable (R)

section

variable (I : Type u) [Fintype I] (W : Cᵒᵖ)

/-- The evaluated free sheaf, presented as a fan over the evaluated summands. -/
def evalFan : Fan (fun _ : I => (_root_.SheafOfModules.evaluation R W).obj
    (_root_.SheafOfModules.unit R)) :=
  Fan.mk ((_root_.SheafOfModules.free (R := R) I).val.obj W)
    (fun j => (_root_.SheafOfModules.evaluation R W).map
      ((biproduct.isoCoproduct (fun _ : I => _root_.SheafOfModules.unit R)).inv ≫
        biproduct.π (fun _ : I => _root_.SheafOfModules.unit R) j))

/-- **That fan is a limit fan.** The coproduct of finitely many copies of the unit sheaf is also
their product, and evaluation preserves limits. -/
def evalFanIsLimit : IsLimit (evalFan R I W) := by
  have t : IsLimit (Fan.mk (∐ (fun _ : I => _root_.SheafOfModules.unit R))
      (fun j : I => (biproduct.isoCoproduct (fun _ : I => _root_.SheafOfModules.unit R)).inv ≫
        biproduct.π (fun _ : I => _root_.SheafOfModules.unit R) j)) :=
    IsLimit.ofIsoLimit (biproduct.isLimit (fun _ : I => _root_.SheafOfModules.unit R))
      (Cones.ext (biproduct.isoCoproduct (fun _ : I => _root_.SheafOfModules.unit R))
        (fun j => by
          change biproduct.π (fun _ : I => _root_.SheafOfModules.unit R) j.as =
            (biproduct.isoCoproduct (fun _ : I => _root_.SheafOfModules.unit R)).hom ≫
              (biproduct.isoCoproduct (fun _ : I => _root_.SheafOfModules.unit R)).inv ≫
                biproduct.π (fun _ : I => _root_.SheafOfModules.unit R) j.as
          rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]))
  exact isLimitFanMkObjOfIsLimit (_root_.SheafOfModules.evaluation R W) _ _ t

/-- **The sections of a finite free sheaf of modules over an object are the free module on the
index.** -/
def freeEvalIso :
    (_root_.SheafOfModules.free (R := R) I).val.obj W ≅
      ModuleCat.of (R.val.obj W) (I → R.val.obj W) :=
  IsLimit.conePointUniqueUpToIso (evalFanIsLimit R I W)
    (ModuleCat.productConeIsLimit
      (fun _ : I => (_root_.SheafOfModules.evaluation R W).obj
        (_root_.SheafOfModules.unit R)))

/-- The coordinates of the comparison are the evaluated biproduct projections. -/
theorem freeEvalIso_hom_apply
    (x : (_root_.SheafOfModules.free (R := R) I).val.obj W) (j : I) :
    (freeEvalIso R I W).hom x j =
      (_root_.SheafOfModules.evaluation R W).map
        ((biproduct.isoCoproduct (fun _ : I => _root_.SheafOfModules.unit R)).inv ≫
          biproduct.π (fun _ : I => _root_.SheafOfModules.unit R) j) x := by
  have h := IsLimit.conePointUniqueUpToIso_hom_comp (evalFanIsLimit R I W)
    (ModuleCat.productConeIsLimit
      (fun _ : I => (_root_.SheafOfModules.evaluation R W).obj
        (_root_.SheafOfModules.unit R)))
    (Discrete.mk j)
  exact ConcreteCategory.congr_hom h x

/-- The tautological section is the image of `1` under the coproduct inclusion. -/
theorem freeSection_val (i : I) :
    (_root_.SheafOfModules.freeSection (R := R) i).val W =
      (_root_.SheafOfModules.evaluation R W).map
        (Sigma.ι (fun _ : I => _root_.SheafOfModules.unit R) i) (1 : R.val.obj W) := by
  change ((_root_.SheafOfModules.free (R := R) I).unitHomEquiv
    (Sigma.ι (fun _ : I => _root_.SheafOfModules.unit R) i ≫
      𝟙 (_root_.SheafOfModules.free (R := R) I))).val W = _
  exact congrArg
    (fun φ : _root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.free (R := R) I =>
      ((_root_.SheafOfModules.free (R := R) I).unitHomEquiv φ).val W)
    (Category.comp_id (Sigma.ι (fun _ : I => _root_.SheafOfModules.unit R) i))

variable [DecidableEq I]

/-- The comparison sends the `i`-th tautological section to the `i`-th standard vector. -/
theorem freeEvalIso_hom_freeSection (i : I) :
    (freeEvalIso R I W).hom ((_root_.SheafOfModules.freeSection (R := R) i).val W) =
      Pi.single i (1 : R.val.obj W) := by
  funext j
  have hcat : Sigma.ι (fun _ : I => _root_.SheafOfModules.unit R) i ≫
      (biproduct.isoCoproduct (fun _ : I => _root_.SheafOfModules.unit R)).inv ≫
        biproduct.π (fun _ : I => _root_.SheafOfModules.unit R) j =
      biproduct.ι (fun _ : I => _root_.SheafOfModules.unit R) i ≫
        biproduct.π (fun _ : I => _root_.SheafOfModules.unit R) j := by
    rw [biproduct.isoCoproduct_inv, ← Category.assoc, Sigma.ι_desc]
  rw [freeEvalIso_hom_apply, freeSection_val R I W i, ← ModuleCat.comp_apply,
    ← Functor.map_comp, hcat]
  by_cases h : i = j
  · subst h
    rw [biproduct.ι_π_self, CategoryTheory.Functor.map_id, Pi.single_eq_same]
    simp
  · rw [biproduct.ι_π_ne _ h, Functor.map_zero, Pi.single_eq_of_ne (Ne.symm h)]
    simp

/-- **The tautological sections of a finite free sheaf of modules are a basis of its sections over
every object of the site.** -/
def freeSectionsBasis : Basis I (R.val.obj W)
    ((_root_.SheafOfModules.free (R := R) I).val.obj W) :=
  (Pi.basisFun (R.val.obj W) I).map (freeEvalIso R I W).toLinearEquiv.symm

/-- The basis vectors are the tautological sections. -/
@[simp]
theorem freeSectionsBasis_apply (i : I) :
    freeSectionsBasis R I W i =
      (_root_.SheafOfModules.freeSection (R := R) i).val W := by
  show ((Pi.basisFun (R.val.obj W) I).map
    (freeEvalIso R I W).toLinearEquiv.symm) i = _
  rw [Basis.map_apply, Pi.basisFun_apply, ← freeEvalIso_hom_freeSection R I W i]
  exact (freeEvalIso R I W).toLinearEquiv.symm_apply_apply _

end

/-- **The basis is compatible with restriction along every arrow of the site.** No naturality
argument is needed: the vectors are the values of one compatible family of sections. -/
theorem freeSectionsBasis_map (I : Type u) [Fintype I] [DecidableEq I] {W W' : Cᵒᵖ}
    (g : W ⟶ W') (i : I) :
    (_root_.SheafOfModules.free (R := R) I).val.map g (freeSectionsBasis R I W i) =
      freeSectionsBasis R I W' i := by
  rw [freeSectionsBasis_apply, freeSectionsBasis_apply]
  exact PresheafOfModules.sections_property _ g

end KltDP.Compatibility.FreeSheafSections
