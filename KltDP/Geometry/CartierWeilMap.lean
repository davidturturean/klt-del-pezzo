import KltDP.Geometry.CartierCommonEquations
import KltDP.Geometry.CartierLocalClass
import KltDP.Geometry.PrincipalDivisor
import Mathlib.Topology.Compactness.Compact

/-!
# Orders of actual Cartier divisors and the Cartier-to-Weil homomorphism

An actual section of the Cartier divisor sheaf has local rational equations.
At a point with a DVR stalk, their orders agree: the quotient of two equations
is a regular unit on their common neighborhood, whose germ is a stalk unit.
This defines an additive integer order on the actual global Cartier group.

For the project's normal projective surfaces, the DVR hypothesis at a prime
curve is already proved. Compactness supplies finitely many equation charts.
On each chart the Cartier order is the order of its rational equation, whose
global principal support is already finite. Thus the resulting coefficients
have finite support on the original prime curves. The constructed map takes
principal Cartier divisors to the existing actual principal Weil divisors.

The pointwise construction works on every integral scheme at every DVR stalk.
The finite-support target below is for normal projective surfaces, not for
arbitrary non-quasi-compact normal schemes. No assertion of injectivity,
surjectivity, factoriality, or comparison of divisor classes is included.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u}) [IsIntegral X]

local instance (x : X) : IsDomain (X.presheaf.stalk x) :=
  integralSchemeStalk_isDomain X x

/-- An actual regular unit on a neighborhood has order zero at a DVR
stalk in that neighborhood. The original germ maps give the comparison. -/
theorem stalkDivisorOrder_map_section_unit (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (U : X.Opens) [Nonempty U] (hx : x ∈ U) (a : Γ(X, U)ˣ) :
    stalkDivisorOrder X x
      (Units.map (X.germToFunctionField U).hom.toMonoidHom a) = 0 := by
  let b : (X.presheaf.stalk x)ˣ :=
    Units.map (X.presheaf.germ U x hx).hom.toMonoidHom a
  have hmap :
      Units.map (algebraMap (X.presheaf.stalk x) X.functionField) b =
        Units.map (X.germToFunctionField U).hom.toMonoidHom a := by
    apply Units.ext
    change (X.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes trivial))
        ((X.presheaf.germ U x hx) (a : Γ(X, U))) =
      (X.germToFunctionField U) (a : Γ(X, U))
    exact ConcreteCategory.congr_hom
      (X.presheaf.germ_stalkSpecializes hx
        ((genericPoint_spec X).specializes trivial)) (a : Γ(X, U))
  rw [← hmap]
  exact stalkDivisorOrder_map_unit X x b

/-- Equal actual equation classes have equal DVR orders at every point
of their common open. Equality is proved using the actual transition unit. -/
theorem stalkDivisorOrder_eq_of_cartierEquation_eq (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (U : X.Opens) [Nonempty U] (hx : x ∈ U) (f g : X.functionFieldˣ)
    (hfg : cartierEquationClassHom X U (Additive.ofMul f) =
      cartierEquationClassHom X U (Additive.ofMul g)) :
    stalkDivisorOrder X x f = stalkDivisorOrder X x g := by
  obtain ⟨a, ha⟩ := (cartierEquationClassHom_eq_iff X U f g).mp hfg
  have hzero : stalkDivisorOrder X x (f / g) = 0 := by
    rw [← ha]
    exact stalkDivisorOrder_map_section_unit X x U hx a
  change stalkDivisorOrderHom X x (Additive.ofMul f - Additive.ofMul g) = 0 at hzero
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- Every global Cartier divisor has an actual equation near every point.
The equation is selected only after existence has been proved for the sheaf
quotient; no global principal representation is assumed. -/
theorem exists_cartierOrderEquation (D : CartierDivisor X) (x : X) :
    ∃ f : X.functionFieldˣ, ∃ (U : X.Opens) (hx : x ∈ U),
      letI : Nonempty U := ⟨⟨x, hx⟩⟩
      cartierEquationClassHom X U (Additive.ofMul f) =
        (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D := by
  obtain ⟨U, i, hx, f, hf⟩ := exists_local_cartier_equation X ⊤ D x trivial
  have hi : i = homOfLE (show U ≤ ⊤ from le_top) := Subsingleton.elim _ _
  exact ⟨f, U, hx, by simpa only [hi] using hf⟩

/-- One actual rational equation near the given point. All subsequent
orders are proved independent of this choice. -/
def cartierOrderEquation (D : CartierDivisor X) (x : X) : X.functionFieldˣ :=
  (exists_cartierOrderEquation X D x).choose

theorem cartierOrderEquation_spec (D : CartierDivisor X) (x : X) :
    ∃ (U : X.Opens) (hx : x ∈ U),
      letI : Nonempty U := ⟨⟨x, hx⟩⟩
      cartierEquationClassHom X U (Additive.ofMul (cartierOrderEquation X D x)) =
        (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D :=
  (exists_cartierOrderEquation X D x).choose_spec

/-- The integer order of an actual global Cartier divisor at a DVR stalk. -/
def cartierOrderAt (D : CartierDivisor X) (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] : ℤ :=
  stalkDivisorOrder X x (cartierOrderEquation X D x)

/-- Any actual local equation computes the chosen order. Intersecting
its chart with the chosen one proves independence of both the equation
and the neighborhood. -/
theorem cartierOrderAt_eq_of_equation (D : CartierDivisor X) (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (U : X.Opens) [Nonempty U] (hx : x ∈ U) (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D) :
    cartierOrderAt X D x = stalkDivisorOrder X x f := by
  obtain ⟨V, hxV, hV⟩ := cartierOrderEquation_spec X D x
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let W : X.Opens := V ⊓ U
  have hxW : x ∈ W := ⟨hxV, hx⟩
  letI : Nonempty W := ⟨⟨x, hxW⟩⟩
  apply stalkDivisorOrder_eq_of_cartierEquation_eq X x W hxW
  exact (cartierGlobalEquation_restrict X D (homOfLE (show W ≤ V from inf_le_left))
    (cartierOrderEquation X D x) hV).trans
      (cartierGlobalEquation_restrict X D (homOfLE (show W ≤ U from inf_le_right))
        f hf).symm

@[simp]
theorem cartierOrderAt_zero (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    cartierOrderAt X 0 x = 0 := by
  have h := cartierOrderAt_eq_of_equation X 0 x ⊤ trivial 1 (by simp)
  exact h.trans (stalkDivisorOrder_one X x)

/-- Products of simultaneous local equations prove additivity on actual
global sections, with no homomorphism law supplied as an assumption. -/
theorem cartierOrderAt_add (D E : CartierDivisor X) (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    cartierOrderAt X (D + E) x = cartierOrderAt X D x + cartierOrderAt X E x := by
  obtain ⟨U, i, hx, f, g, hf, hg⟩ :=
    exists_common_cartier_equations X D E ⊤ x trivial
  letI : Nonempty U := ⟨⟨x, hx⟩⟩
  have hfg : cartierEquationClassHom X U (Additive.ofMul (f * g)) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op (D + E) := by
    change cartierEquationClassHom X U (Additive.ofMul f + Additive.ofMul g) = _
    rw [map_add, hf, hg, map_add]
  rw [cartierOrderAt_eq_of_equation X (D + E) x U hx (f * g) hfg,
    cartierOrderAt_eq_of_equation X D x U hx f hf,
    cartierOrderAt_eq_of_equation X E x U hx g hg,
    stalkDivisorOrder_mul]

/-- The actual Cartier-to-integer order homomorphism at a DVR stalk. -/
def cartierOrderAtHom (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] : CartierDivisor X →+ ℤ where
  toFun D := cartierOrderAt X D x
  map_zero' := cartierOrderAt_zero X x
  map_add' D E := cartierOrderAt_add X D E x

/-- A principal Cartier divisor has exactly the original DVR order of
its rational function. In particular the sign is the existing +1
uniformizer convention. -/
@[simp]
theorem cartierOrderAt_principal (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (f : X.functionFieldˣ) :
    cartierOrderAt X (principalCartierDivisorHom X (Additive.ofMul f)) x =
      stalkDivisorOrder X x f := by
  apply cartierOrderAt_eq_of_equation X _ x ⊤ trivial f
  have hi : (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op =
      𝟙 (op (⊤ : X.Opens)) := Subsingleton.elim _ _
  rw [hi]
  exact (ConcreteCategory.congr_hom
    ((cartierDivisorSheaf X).val.map_id (op (⊤ : X.Opens)))
    (principalCartierDivisorHom X (Additive.ofMul f))).symm

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)

local instance (C : S.PrimeCurve) :
    IsDiscreteValuationRing (S.toScheme.presheaf.stalk C.genericPoint) :=
  C.genericPoint_isDiscreteValuationRing

/-- Order along an actual prime curve, for the actual Cartier divisor
sheaf on the original surface. The DVR property is a proved geometric
fact about the curve's generic point. -/
def cartierCoefficientHom (C : S.PrimeCurve) : CartierDivisor S.toScheme →+ ℤ :=
  cartierOrderAtHom S.toScheme C.genericPoint

/-- Compactness and the existing finite support of actual principal
orders prove finite support for every global Cartier divisor. -/
theorem cartierCoefficient_finite_support (D : CartierDivisor S.toScheme) :
    (Function.support (fun C : S.PrimeCurve => S.cartierCoefficientHom C D)).Finite := by
  classical
  choose U hx hrep using fun x : S.toScheme => cartierOrderEquation_spec S.toScheme D x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : S.toScheme => (U x : Set S.toScheme)) (fun x => (U x).isOpen)
      (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  have hfinite : (⋃ x ∈ t, Function.support
      (fun C : S.PrimeCurve => C.order (cartierOrderEquation S.toScheme D x))).Finite :=
    t.finite_toSet.biUnion (fun x _ => S.order_finite_support _)
  refine hfinite.subset ?_
  intro C hC
  obtain ⟨x, hxT, hxC⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ C.genericPoint))
  refine Set.mem_iUnion₂.mpr ⟨x, hxT, ?_⟩
  letI : Nonempty (U x) := ⟨⟨x, hx x⟩⟩
  have horder : S.cartierCoefficientHom C D =
      C.order (cartierOrderEquation S.toScheme D x) :=
    cartierOrderAt_eq_of_equation S.toScheme D C.genericPoint (U x) hxC
      (cartierOrderEquation S.toScheme D x) (hrep x)
  change C.order (cartierOrderEquation S.toScheme D x) ≠ 0
  rw [← horder]
  exact hC

/-- The actual Cartier-to-Weil homomorphism. Its coefficients are orders
of local equations at the original curve stalks; finite support is proved. -/
def cartierToWeilHom : CartierDivisor S.toScheme →+ S.WeilDivisor where
  toFun D := Finsupp.ofSupportFinite (fun C => S.cartierCoefficientHom C D)
    (S.cartierCoefficient_finite_support D)
  map_zero' := by
    apply Finsupp.ext
    intro C
    exact (S.cartierCoefficientHom C).map_zero
  map_add' D E := by
    apply Finsupp.ext
    intro C
    exact (S.cartierCoefficientHom C).map_add D E

@[simp]
theorem cartierToWeilHom_apply (D : CartierDivisor S.toScheme) (C : S.PrimeCurve) :
    S.cartierToWeilHom D C = S.cartierCoefficientHom C D := rfl

/-- Every actual equation chart computes every coefficient whose generic
point lies on that chart. This is the usual Cartier-to-Weil formula. -/
theorem cartierToWeilHom_apply_of_equation (D : CartierDivisor S.toScheme)
    (C : S.PrimeCurve) (U : S.toScheme.Opens) [Nonempty U] (hC : C.genericPoint ∈ U)
    (f : S.toScheme.functionFieldˣ)
    (hf : cartierEquationClassHom S.toScheme U (Additive.ofMul f) =
      (cartierDivisorSheaf S.toScheme).val.map
        (homOfLE (show U ≤ ⊤ from le_top)).op D) :
    S.cartierToWeilHom D C = C.order f :=
  cartierOrderAt_eq_of_equation S.toScheme D C.genericPoint U hC f hf

/-- The constructed Cartier-to-Weil map sends every actual principal
Cartier divisor to the previously constructed principal Weil divisor. -/
@[simp]
theorem cartierToWeilHom_principal (f : S.toScheme.functionFieldˣ) :
    S.cartierToWeilHom (principalCartierDivisorHom S.toScheme (Additive.ofMul f)) =
      S.principalDivisor f := by
  apply Finsupp.ext
  intro C
  exact cartierOrderAt_principal S.toScheme C.genericPoint f

/-- Compatibility with principal divisors as an equality of actual
additive homomorphisms, rather than just a coefficient identity. -/
theorem cartierToWeilHom_comp_principal :
    S.cartierToWeilHom.comp (principalCartierDivisorHom S.toScheme) =
      S.principalDivisorHom := by
  apply AddMonoidHom.ext
  intro f
  exact S.cartierToWeilHom_principal f.toMul

end NormalProjectiveSurface

end KltDP.Geometry
