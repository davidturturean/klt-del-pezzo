import KltDP.Geometry.EffectiveCartierSection
import KltDP.Geometry.WeilCartierEquiv

/-!
# Regular equations from the original effective Weil divisor

Nonnegative coefficients make the existing fraction-field product of
height-one prime generators the image of an actual regular product with
natural exponents. Applied to the original surface stalk coordinates,
this produces a regular stalk representative of the original rational
equation. Germ representability supplies an actual neighborhood section.

The original Cartier equation and this regular equation have the same
orders along every original curve through the point. The existing stalk
unit and neighborhood-unit theorems then identify their actual Cartier
classes on a smaller original open. Thus the regular-equation cover is
derived from the original effective Weil image and factorial stalks.

No regular-equation cover, local-lifting conclusion, branch ideal equality
or desired Cartier-class equality is an assumption. Factoriality remains
an explicit hypothesis on the actual stalks. The identity of the resulting
zero subscheme with the prescribed reduced node sum remains separate.

Reuse: pinned finite products, integer/natural powers, Finsupp embeddings
and original germ representability; the project's actual stalk-divisor,
curve-order, regular-unit and Cartier--Weil constructions. Newer Mathlib
retains these basic mechanisms (germ_exist is renamed exists_germ_eq),
but does not replace this original-object adapter. No source port is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace KltDP.RingTheory

variable (R : Type u) [CommRing R] [IsDomain R]
  [IsNoetherianRing R] [UniqueFactorizationMonoid R]

/-- The actual regular product of the original prime generators. -/
def regularDivisorProduct (D : AffineHeightOnePrime R →₀ ℤ) : R :=
  ∏ p ∈ D.support, heightOnePrimeGenerator R p ^ (D p).toNat

/-- For nonnegative original coefficients, the existing fraction-field
equation is the image of the actual regular prime-generator product. -/
theorem map_regularDivisorProduct
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (D : AffineHeightOnePrime R →₀ ℤ) (hD : ∀ p, 0 ≤ D p) :
    algebraMap R K (regularDivisorProduct R D) =
      (fractionOfDivisorCoordinates R K D : K) := by
  classical
  unfold regularDivisorProduct fractionOfDivisorCoordinates
  rw [map_prod, Units.coe_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have he : (heightOnePrimeGeneratorUnit R K p) ^ D p =
      (heightOnePrimeGeneratorUnit R K p) ^ (D p).toNat := by
    calc
      _ = (heightOnePrimeGeneratorUnit R K p) ^ ((D p).toNat : ℤ) :=
        congrArg (fun n : ℤ => (heightOnePrimeGeneratorUnit R K p) ^ n)
          (Int.toNat_of_nonneg (hD p)).symm
      _ = _ := zpow_natCast _ _
  rw [map_pow, he, Units.val_pow_eq_pow_val, heightOnePrimeGeneratorUnit_val]

end KltDP.RingTheory

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- Extension of the original effective divisor to the actual stalk's
height-one-prime coordinates retains coefficient nonnegativity. -/
theorem stalkDivisorCoordinates_nonneg {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    (x : U) (D : X.WeilDivisor) (hD : EffectiveDivisor D)
    (p : RingTheory.AffineHeightOnePrime (X.stalk x)) :
    0 ≤ X.stalkDivisorCoordinates hU x D p := by
  classical
  let f : {C : X.PrimeCurve // (x : X.toScheme) ∈ C} ↪
      RingTheory.AffineHeightOnePrime (X.stalk x) :=
    ⟨fun C => C.1.stalkHeightOnePrime hU x C.2,
      PrimeCurve.stalkHeightOnePrime_injective hU x⟩
  change 0 ≤ Finsupp.embDomain f
    (D.subtypeDomain (fun C => (x : X.toScheme) ∈ C)) p
  by_cases hp : p ∈ Set.range f
  · obtain ⟨C, rfl⟩ := hp
    rw [Finsupp.embDomain_apply]
    exact hD C.1
  · simpa only [Finsupp.embDomain_notin_range f _ p hp] using (le_refl (0 : ℤ))

/-- An original effective Weil image gives a cover by genuine regular
equations of the original Cartier divisor, using actual factorial stalks. -/
theorem hasRegularCartierEquations_of_effective_weil
    [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]
    (E : CartierDivisor X.toScheme) (hE : EffectiveDivisor (X.cartierToWeilHom E)) :
    HasRegularCartierEquations X.toScheme E := by
  classical
  intro x
  let A : X.toScheme.Opens := (X.toScheme.affineCover.map x).opensRange
  have hA : IsAffineOpen A := isAffineOpen_opensRange (X.toScheme.affineCover.map x)
  let xa : A := ⟨x, X.toScheme.affineCover.covers x⟩
  let B := X.cartierToWeilHom E
  let f := X.stalkRationalEquation hA xa B
  let a : X.stalk x := RingTheory.regularDivisorProduct (X.stalk x)
    (X.stalkDivisorCoordinates hA xa B)
  have ha : algebraMap (X.stalk x) X.toScheme.functionField a =
      (f : X.toScheme.functionField) :=
    RingTheory.map_regularDivisorProduct (X.stalk x) X.toScheme.functionField
      (X.stalkDivisorCoordinates hA xa B)
      (X.stalkDivisorCoordinates_nonneg hA xa B hE)
  obtain ⟨W, hxW, s, hs⟩ := X.toScheme.presheaf.germ_exist x a
  letI : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hsfield : X.toScheme.germToFunctionField W s =
      (f : X.toScheme.functionField) := by
    calc
      _ = algebraMap (X.stalk x) X.toScheme.functionField
          (X.toScheme.presheaf.germ W x hxW s) :=
        (ConcreteCategory.congr_hom (X.toScheme.presheaf.germ_stalkSpecializes hxW
          ((genericPoint_spec X.toScheme).specializes trivial)) s).symm
      _ = algebraMap (X.stalk x) X.toScheme.functionField a := congrArg _ hs
      _ = _ := ha
  obtain ⟨g, U, hxU, hg⟩ := exists_cartierOrderEquation X.toScheme E x
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have horders (C : X.PrimeCurve) (hxC : x ∈ C) : C.order f = C.order g := by
    exact (X.stalkRationalEquation_order hA xa B C hxC).trans
      (X.cartierToWeilHom_apply_of_equation E C U
        (C.genericPoint_mem_of_mem ⟨x, hxU⟩ hxC) g hg)
  obtain ⟨V, hVU, hxV, b, hb⟩ :=
    X.exists_regular_unit_near_of_equal_curve_orders x (U ⊓ W) ⟨hxU, hxW⟩ f g horders
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hVW : V ≤ W := hVU.trans inf_le_right
  have hVUg : V ≤ U := hVU.trans inf_le_left
  have hfg : cartierEquationClassHom X.toScheme V (Additive.ofMul f) =
      cartierEquationClassHom X.toScheme V (Additive.ofMul g) :=
    (cartierEquationClassHom_eq_iff X.toScheme V f g).mpr
      ⟨b, by simpa only [div_eq_mul_inv] using hb⟩
  let c : RegularCartierEquationChart X.toScheme E :=
    { chart :=
        { openSet := V
          nonempty := inferInstance
          equation := f
          represents := hfg.trans
            (cartierGlobalEquation_restrict X.toScheme E (homOfLE hVUg) g hg) }
      coefficient := X.toScheme.presheaf.map (homOfLE hVW).op s
      germ_eq :=
        (X.toScheme.presheaf.germ_res_apply (homOfLE hVW) (genericPoint X.toScheme)
          (genericPoint_mem_nonempty_open X.toScheme V) s).trans hsfield }
  exact ⟨c, hxV⟩

/-- The actual Cartier representative of an original effective Weil
divisor has regular equation charts; no such cover is supplied. -/
theorem hasRegularCartierEquations_cartierWeilEquiv_symm
    [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]
    (B : X.WeilDivisor) (hB : EffectiveDivisor B) :
    HasRegularCartierEquations X.toScheme (X.cartierWeilEquiv.symm B) := by
  apply X.hasRegularCartierEquations_of_effective_weil
  have hmap : X.cartierToWeilHom (X.cartierWeilEquiv.symm B) = B :=
    X.cartierWeilEquiv.apply_symm_apply B
  rw [hmap]
  exact hB

end KltDP.Geometry.NormalProjectiveSurface
