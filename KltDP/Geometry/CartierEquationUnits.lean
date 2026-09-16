import KltDP.Geometry.CartierDivisorSheaf
import KltDP.Compatibility.SheafMonoKernel

/-!
# Actual regular units between Cartier equations

The actual regular-unit inclusion is a monomorphism. In the abelian sheaf
category it is therefore the kernel of its cokernel. Section evaluation
preserves that kernel, so a rational equation has zero Cartier class
precisely when it is the image of an actual regular unit on the same open.
This is left exactness; surjectivity of quotient maps on sections is not
asserted.

On nonempty opens of an integral scheme, the function-field comparison
identifies equal equation classes with a unique regular unit whose image
is their ratio. These actual units satisfy identity, cocycle, and
restriction laws. Constructing the associated invertible module sheaf and
its Picard class remains separate work.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual inclusion of regular units into rational units is mono,
also after transporting the groups to additive notation. -/
instance regularToRationalUnitsAdd_mono : Mono (regularToRationalUnitsAdd X) := by
  apply CategoryTheory.Sheaf.mono_of_injective
  intro U a b hab
  exact congrArg Additive.ofMul
    (regularToRationalUnits_app_injective X U.unop (congrArg Additive.toMul hab))

/-- A rational equation has zero Cartier class if and only if it is
the image of an actual regular unit on that same nonempty open. -/
theorem cartierEquationClassHom_eq_zero_iff
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ) :
    cartierEquationClassHom X U (Additive.ofMul f) = 0 ↔
      ∃ a : Γ(X, U)ˣ, Units.map (X.germToFunctionField U).hom.toMonoidHom a = f := by
  constructor
  · intro hf
    obtain ⟨a, ha⟩ :=
      (KltDP.Sheaf.toQuotientSheaf_app_eq_zero_iff_of_mono
        (regularToRationalUnitsAdd X) U
        ((rationalUnitsAddSectionsIso X U).inv (Additive.ofMul f))).mp hf
    refine ⟨a.toMul, ?_⟩
    have hmap := regularToRationalUnitsAdd_app_comp_sectionsIso X U
    have hvalue : (rationalUnitsAddSectionsIso X U).hom
        ((regularToRationalUnitsAdd X).val.app (op U) a) =
          Additive.ofMul (Units.map (X.germToFunctionField U).hom.toMonoidHom a.toMul) :=
      congrArg (fun q : (regularUnitsAddSheaf X).val.obj (op U) ⟶
        AddCommGrp.of (Additive X.functionFieldˣ) => q a) hmap
    apply congrArg Additive.toMul
    calc
      Additive.ofMul (Units.map (X.germToFunctionField U).hom.toMonoidHom a.toMul) =
          (rationalUnitsAddSectionsIso X U).hom
            ((regularToRationalUnitsAdd X).val.app (op U) a) := hvalue.symm
      _ = (rationalUnitsAddSectionsIso X U).hom
          ((rationalUnitsAddSectionsIso X U).inv (Additive.ofMul f)) :=
        congrArg (rationalUnitsAddSectionsIso X U).hom ha
      _ = Additive.ofMul f := Iso.inv_hom_id_apply _ _
  · rintro ⟨a, rfl⟩
    exact cartierEquationClassHom_map_regular_unit X U a

/-- Two rational equations define the same Cartier section exactly when
their ratio is the image of an actual regular unit. The orientation is
`f / g`, in that order. -/
theorem cartierEquationClassHom_eq_iff
    (U : X.Opens) [Nonempty U] (f g : X.functionFieldˣ) :
    cartierEquationClassHom X U (Additive.ofMul f) =
        cartierEquationClassHom X U (Additive.ofMul g) ↔
      ∃ a : Γ(X, U)ˣ, Units.map (X.germToFunctionField U).hom.toMonoidHom a = f / g := by
  rw [← sub_eq_zero, ← map_sub]
  exact cartierEquationClassHom_eq_zero_iff X U (f / g)

/-- The regular transition unit is unique because the actual germ map
of an integral scheme is injective. -/
theorem existsUnique_cartierTransitionUnit
    (U : X.Opens) [Nonempty U] (f g : X.functionFieldˣ)
    (hfg : cartierEquationClassHom X U (Additive.ofMul f) =
      cartierEquationClassHom X U (Additive.ofMul g)) :
    ∃! a : Γ(X, U)ˣ, Units.map (X.germToFunctionField U).hom.toMonoidHom a = f / g := by
  obtain ⟨a, ha⟩ := (cartierEquationClassHom_eq_iff X U f g).mp hfg
  refine ⟨a, ha, fun b hb => ?_⟩
  exact Units.map_injective (X.germToFunctionField_injective U) (hb.trans ha.symm)

/-- The actual regular unit whose rational image is the ratio `f / g`
of two representatives of the same Cartier section. -/
def cartierTransitionUnit
    (U : X.Opens) [Nonempty U] (f g : X.functionFieldˣ)
    (hfg : cartierEquationClassHom X U (Additive.ofMul f) =
      cartierEquationClassHom X U (Additive.ofMul g)) : Γ(X, U)ˣ :=
  ((cartierEquationClassHom_eq_iff X U f g).mp hfg).choose

@[simp]
theorem map_cartierTransitionUnit
    (U : X.Opens) [Nonempty U] (f g : X.functionFieldˣ)
    (hfg : cartierEquationClassHom X U (Additive.ofMul f) =
      cartierEquationClassHom X U (Additive.ofMul g)) :
    Units.map (X.germToFunctionField U).hom.toMonoidHom (cartierTransitionUnit X U f g hfg) = f / g :=
  ((cartierEquationClassHom_eq_iff X U f g).mp hfg).choose_spec

@[simp]
theorem cartierTransitionUnit_self (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ) :
    cartierTransitionUnit X U f f rfl = 1 := by
  apply Units.map_injective (X.germToFunctionField_injective U)
  rw [map_cartierTransitionUnit, map_one, div_self']

/-- The actual transition units satisfy the multiplicative cocycle law
on any nonempty common open. -/
theorem cartierTransitionUnit_mul
    (U : X.Opens) [Nonempty U] (f g h : X.functionFieldˣ)
    (hfg : cartierEquationClassHom X U (Additive.ofMul f) =
      cartierEquationClassHom X U (Additive.ofMul g))
    (hgh : cartierEquationClassHom X U (Additive.ofMul g) =
      cartierEquationClassHom X U (Additive.ofMul h)) :
    cartierTransitionUnit X U f g hfg * cartierTransitionUnit X U g h hgh =
      cartierTransitionUnit X U f h (hfg.trans hgh) := by
  apply Units.map_injective (X.germToFunctionField_injective U)
  rw [map_mul, map_cartierTransitionUnit, map_cartierTransitionUnit,
    map_cartierTransitionUnit, div_mul_div_cancel]

/-- The existing rational-section comparison also commutes with
restriction after passing to units and then additive notation. -/
theorem rationalUnitsAddSectionsIso_naturality
    {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U) :
    (rationalUnitsAddSheaf X).val.map (homOfLE h).op ≫
        (rationalUnitsAddSectionsIso X V).hom =
      (rationalUnitsAddSectionsIso X U).hom := by
  change (KltDP.Sheaf.commRingUnitsFunctor ⋙ commGroupAddCommGroupEquivalence.functor).map
      ((rationalFunctionSheaf X).val.map (homOfLE h).op) ≫
      (KltDP.Sheaf.commRingUnitsFunctor ⋙ commGroupAddCommGroupEquivalence.functor).map
        (rationalFunctionSectionsIso X V).hom =
      (KltDP.Sheaf.commRingUnitsFunctor ⋙ commGroupAddCommGroupEquivalence.functor).map
        (rationalFunctionSectionsIso X U).hom
  rw [← Functor.map_comp, rationalFunctionSectionsIso_naturality]

/-- Restricting an actual equation class keeps the same rational function. -/
theorem cartierEquationClassHom_restrict
    {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U) (f : X.functionFieldˣ) :
    (cartierDivisorSheaf X).val.map (homOfLE h).op
        (cartierEquationClassHom X U (Additive.ofMul f)) =
      cartierEquationClassHom X V (Additive.ofMul f) := by
  have hinv : (rationalUnitsAddSectionsIso X U).inv ≫
      (rationalUnitsAddSheaf X).val.map (homOfLE h).op =
        (rationalUnitsAddSectionsIso X V).inv := by
    apply (cancel_mono (rationalUnitsAddSectionsIso X V).hom).mp
    rw [Category.assoc, rationalUnitsAddSectionsIso_naturality,
      Iso.inv_hom_id, Iso.inv_hom_id]
  have hnat := (rationalUnitsToCartier X).val.naturality (homOfLE h).op
  change (cartierDivisorSheaf X).val.map (homOfLE h).op
      ((rationalUnitsToCartier X).val.app (op U)
        ((rationalUnitsAddSectionsIso X U).inv (Additive.ofMul f))) = _
  calc
    _ = (rationalUnitsToCartier X).val.app (op V)
        ((rationalUnitsAddSheaf X).val.map (homOfLE h).op
          ((rationalUnitsAddSectionsIso X U).inv (Additive.ofMul f))) :=
      (congrArg (fun q : (rationalUnitsAddSheaf X).val.obj (op U) ⟶
        (cartierDivisorSheaf X).val.obj (op V) =>
          q ((rationalUnitsAddSectionsIso X U).inv (Additive.ofMul f))) hnat).symm
    _ = (rationalUnitsToCartier X).val.app (op V)
        ((rationalUnitsAddSectionsIso X V).inv (Additive.ofMul f)) :=
      congrArg ((rationalUnitsToCartier X).val.app (op V))
        (congrArg (fun q : AddCommGrp.of (Additive X.functionFieldˣ) ⟶
          (rationalUnitsAddSheaf X).val.obj (op V) => q (Additive.ofMul f)) hinv)

/-- Equality of actual rational equation classes persists under restriction. -/
theorem cartierEquationClassHom_eq_on_restriction
    {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    {f g : X.functionFieldˣ}
    (hfg : cartierEquationClassHom X U (Additive.ofMul f) =
      cartierEquationClassHom X U (Additive.ofMul g)) :
    cartierEquationClassHom X V (Additive.ofMul f) =
      cartierEquationClassHom X V (Additive.ofMul g) := by
  simpa only [cartierEquationClassHom_restrict] using
    congrArg ((cartierDivisorSheaf X).val.map (homOfLE h).op) hfg

/-- The original germ-to-function-field map on units commutes with the
actual structure-sheaf restriction. -/
theorem germToFunctionField_map_unit_restriction
    {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U) (a : Γ(X, U)ˣ) :
    Units.map (X.germToFunctionField V).hom.toMonoidHom
        (Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom a) =
      Units.map (X.germToFunctionField U).hom.toMonoidHom a := by
  apply Units.ext
  change X.germToFunctionField V ((X.presheaf.map (homOfLE h).op) (a : Γ(X, U))) =
    X.germToFunctionField U (a : Γ(X, U))
  exact X.presheaf.germ_res_apply (homOfLE h) (genericPoint X)
    (genericPoint_mem_nonempty_open X V) (a : Γ(X, U))

/-- Actual transition units restrict to the actual transition units
of the same equations on a smaller nonempty open. -/
theorem cartierTransitionUnit_restrict
    {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (f g : X.functionFieldˣ)
    (hfg : cartierEquationClassHom X U (Additive.ofMul f) =
      cartierEquationClassHom X U (Additive.ofMul g)) :
    Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom (cartierTransitionUnit X U f g hfg) =
      cartierTransitionUnit X V f g (cartierEquationClassHom_eq_on_restriction X h hfg) := by
  apply Units.map_injective (X.germToFunctionField_injective V)
  rw [germToFunctionField_map_unit_restriction, map_cartierTransitionUnit,
    map_cartierTransitionUnit]

end KltDP.Geometry
