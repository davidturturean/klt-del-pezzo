import KltDP.Geometry.RationalFunctionSheaf
import KltDP.Compatibility.SheafLocalQuotient
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
# The actual Cartier divisor sheaf on an integral scheme

We take the cokernel, in the category of sheaves of abelian groups, of the
actual inclusion of regular units into rational units. Multiplicative unit
groups are first transported through Mathlib's additive group equivalence.
The cokernel is a sheaf; no pointwise quotient is asserted to be a sheaf.

Its sections are locally represented by actual nonzero rational functions.
This follows from the proved local surjectivity of the actual cokernel map,
followed by the canonical nonempty-open identification of rational sections
with the original function field. Global Cartier divisors are the actual
global sections of this quotient sheaf. They are not defined to be global
rational functions modulo global units, and global surjectivity of the
principal-divisor map is not assumed or asserted.

Associated line bundles, transition-unit gluing, comparison with the local
equation quotient at each stalk, and comparison with Weil/Picard classes
remain separate constructions. No literature input is used here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- Reinterpret actual commutative-group sheaves as additive-group sheaves
through the existing equivalence; no quotient is involved in this step. -/
def additiveGroupSheafFunctor : TopCat.Sheaf CommGrp.{u} X ⥤
    TopCat.Sheaf AddCommGrp.{u} X :=
  sheafCompose (Opens.grothendieckTopology X) commGroupAddCommGroupEquivalence.functor

/-- The actual regular units, in additive notation. -/
def regularUnitsAddSheaf : TopCat.Sheaf AddCommGrp.{u} X :=
  (additiveGroupSheafFunctor X).obj (regularUnitsSheaf X)

/-- The actual rational units, in additive notation. -/
def rationalUnitsAddSheaf : TopCat.Sheaf AddCommGrp.{u} X :=
  (additiveGroupSheafFunctor X).obj (rationalUnitsSheaf X)

/-- The actual unit inclusion, transported through the additive equivalence. -/
def regularToRationalUnitsAdd : regularUnitsAddSheaf X ⟶ rationalUnitsAddSheaf X :=
  (additiveGroupSheafFunctor X).map (regularToRationalUnits X)

/-- The quotient sheaf of rational units by regular units, constructed
as an actual cokernel in the abelian category of sheaves. -/
def cartierDivisorSheaf : TopCat.Sheaf AddCommGrp.{u} X :=
  KltDP.Sheaf.quotientSheaf (regularToRationalUnitsAdd X)

/-- The canonical sheaf map from rational equations to Cartier classes. -/
def rationalUnitsToCartier : rationalUnitsAddSheaf X ⟶ cartierDivisorSheaf X :=
  KltDP.Sheaf.toQuotientSheaf (regularToRationalUnitsAdd X)

/-- The canonical quotient kills the actual regular-unit sheaf map. -/
@[simp]
theorem regularToRationalUnitsAdd_comp_quotient :
    regularToRationalUnitsAdd X ≫ rationalUnitsToCartier X = 0 :=
  KltDP.Sheaf.toQuotientSheaf_condition (regularToRationalUnitsAdd X)

/-- The actual sheaf quotient map is locally surjective. This does not
assert surjectivity on any prescribed open's sections. -/
theorem rationalUnitsToCartier_isLocallySurjective :
    CategoryTheory.Sheaf.IsLocallySurjective (rationalUnitsToCartier X) :=
  KltDP.Sheaf.toQuotientSheaf_isLocallySurjective (regularToRationalUnitsAdd X)

/-- Additive rational-unit sections on a nonempty open are exactly the
additive version of the original function-field unit group. -/
def rationalUnitsAddSectionsIso (U : X.Opens) [Nonempty U] :
    (rationalUnitsAddSheaf X).val.obj (op U) ≅ AddCommGrp.of (Additive X.functionFieldˣ) :=
  commGroupAddCommGroupEquivalence.functor.mapIso (rationalUnitSectionsIso X U)

/-- The transported unit map still agrees with the original germ map,
now regarded as an additive homomorphism on multiplicative unit groups. -/
theorem regularToRationalUnitsAdd_app_comp_sectionsIso
    (U : X.Opens) [Nonempty U] :
    (regularToRationalUnitsAdd X).val.app (op U) ≫
        (rationalUnitsAddSectionsIso X U).hom =
      AddCommGrp.ofHom (Units.map (X.germToFunctionField U).hom.toMonoidHom).toAdditive := by
  change commGroupAddCommGroupEquivalence.functor.map
      ((regularToRationalUnits X).val.app (op U)) ≫
        commGroupAddCommGroupEquivalence.functor.map (rationalUnitSectionsIso X U).hom = _
  rw [← Functor.map_comp, regularToRationalUnits_app_comp_sectionsIso]
  rfl

/-- The Cartier section defined by an actual rational equation on a
nonempty open, as an additive homomorphism on function-field units. -/
def cartierEquationClassHom (U : X.Opens) [Nonempty U] :
    Additive X.functionFieldˣ →+ (cartierDivisorSheaf X).val.obj (op U) :=
  ((rationalUnitsToCartier X).val.app (op U)).hom.comp
    (rationalUnitsAddSectionsIso X U).inv.hom

/-- The actual quotient class of a regular unit vanishes on its open. -/
@[simp]
theorem cartierEquationClassHom_map_regular_unit
    (U : X.Opens) [Nonempty U] (a : Γ(X, U)ˣ) :
    cartierEquationClassHom X U
      (Additive.ofMul (Units.map (X.germToFunctionField U).hom.toMonoidHom a)) = 0 := by
  have hmap := regularToRationalUnitsAdd_app_comp_sectionsIso X U
  have hvalue : (rationalUnitsAddSectionsIso X U).hom
      ((regularToRationalUnitsAdd X).val.app (op U) (Additive.ofMul a)) =
        Additive.ofMul (Units.map (X.germToFunctionField U).hom.toMonoidHom a) :=
    congrArg (fun q : (regularUnitsAddSheaf X).val.obj (op U) ⟶
      AddCommGrp.of (Additive X.functionFieldˣ) => q (Additive.ofMul a)) hmap
  change (rationalUnitsToCartier X).val.app (op U)
    ((rationalUnitsAddSectionsIso X U).inv
      (Additive.ofMul (Units.map (X.germToFunctionField U).hom.toMonoidHom a))) = 0
  have hinv : (rationalUnitsAddSectionsIso X U).inv
      (Additive.ofMul (Units.map (X.germToFunctionField U).hom.toMonoidHom a)) =
        (regularToRationalUnitsAdd X).val.app (op U) (Additive.ofMul a) :=
    (congrArg (fun z : Additive X.functionFieldˣ =>
      (rationalUnitsAddSectionsIso X U).inv z) hvalue.symm).trans
        (ConcreteCategory.congr_hom (rationalUnitsAddSectionsIso X U).hom_inv_id
          ((regularToRationalUnitsAdd X).val.app (op U) (Additive.ofMul a)))
  exact (congrArg
    (fun z : (rationalUnitsAddSheaf X).val.obj (op U) =>
      (rationalUnitsToCartier X).val.app (op U) z) hinv).trans
        (congrArg
          (fun q : regularUnitsAddSheaf X ⟶ cartierDivisorSheaf X =>
            q.val.app (op U) (Additive.ofMul a))
          (regularToRationalUnitsAdd_comp_quotient X))

/-- Multiplying a local rational equation by an actual regular unit
does not change its section of the Cartier divisor sheaf. -/
theorem cartierEquationClassHom_mul_regular_unit
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ) (a : Γ(X, U)ˣ) :
    cartierEquationClassHom X U
        (Additive.ofMul (f * Units.map (X.germToFunctionField U).hom.toMonoidHom a)) =
      cartierEquationClassHom X U (Additive.ofMul f) := by
  change cartierEquationClassHom X U
      (Additive.ofMul f + Additive.ofMul (Units.map (X.germToFunctionField U).hom.toMonoidHom a)) = _
  rw [map_add, cartierEquationClassHom_map_regular_unit, add_zero]

/-- Every Cartier section has an actual rational equation on some
neighborhood of each point. The neighborhood, its inclusion, and the
restriction equality are all produced from the sheaf cokernel. -/
theorem exists_local_cartier_equation (U : X.Opens)
    (D : (cartierDivisorSheaf X).val.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (i : V ⟶ U) (hxV : x ∈ V) (f : X.functionFieldˣ),
      letI : Nonempty V := ⟨⟨x, hxV⟩⟩
      cartierEquationClassHom X V (Additive.ofMul f) =
        (cartierDivisorSheaf X).val.map i.op D := by
  obtain ⟨V, i, r, hxV, hr⟩ := KltDP.Sheaf.exists_local_quotient_representative
    (regularToRationalUnitsAdd X) U D x hx
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  refine ⟨V, i, hxV, ((rationalUnitsAddSectionsIso X V).hom r).toMul, ?_⟩
  change (rationalUnitsToCartier X).val.app (op V)
      ((rationalUnitsAddSectionsIso X V).inv ((rationalUnitsAddSectionsIso X V).hom r)) = _
  rw [Iso.hom_inv_id_apply]
  exact hr

/-- Global Cartier divisors are the actual global sections of the
constructed quotient sheaf, with its inherited additive commutative group. -/
abbrev CartierDivisor : Type u := (cartierDivisorSheaf X).val.obj (op ⊤)

/-- The actual principal Cartier divisor map from nonzero rational
functions to global sections of the Cartier divisor sheaf. -/
def principalCartierDivisorHom : Additive X.functionFieldˣ →+ CartierDivisor X :=
  cartierEquationClassHom X ⊤

/-- Actual global regular units have zero principal Cartier divisor. -/
@[simp]
theorem principalCartierDivisorHom_map_global_unit (a : Γ(X, ⊤)ˣ) :
    principalCartierDivisorHom X
      (Additive.ofMul (Units.map (algebraMap Γ(X, ⊤) X.functionField).toMonoidHom a)) = 0 :=
  cartierEquationClassHom_map_regular_unit X ⊤ a

end KltDP.Geometry
