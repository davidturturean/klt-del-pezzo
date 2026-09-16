import KltDP.Geometry.WeilLocalEquation
import KltDP.Geometry.StalkUnitNeighborhood
import KltDP.Geometry.CartierWeilMap
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Cartier divisors from Weil divisors on a locally factorial surface

An actual factorial stalk supplies a rational equation for a finite Weil
divisor near its point. On overlaps, the two equations have the same
orders on every curve. The actual curve–stalk-prime correspondence and
the UFD unit criterion imply that their ratio is a regular unit locally.
The sheaf condition then identifies their actual Cartier equation classes.
These classes glue in the actual Cartier divisor sheaf. The existing
Cartier-to-Weil order formula proves that the glued divisor maps to the
original Weil divisor.

Factoriality is an explicit hypothesis on every actual stalk. Neither a
factorial affine neighborhood nor the existence of a Cartier representative
is supplied as input. The gluing pattern reuses the pinned
`TopCat.Presheaf.section_ext` and `existsUnique_gluing'` APIs, as in the
project's independently constructed `CartierPicardAssembly`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
variable [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]

/-- On a nonempty open, rational functions with equal orders on all
curves meeting that open define the same actual Cartier section. -/
theorem cartierEquationClass_eq_of_equal_curve_orders
    (U : X.toScheme.Opens) [Nonempty U] (f g : X.toScheme.functionFieldˣ)
    (horders : ∀ C : X.PrimeCurve, C.genericPoint ∈ U → C.order f = C.order g) :
    cartierEquationClassHom X.toScheme U (Additive.ofMul f) =
      cartierEquationClassHom X.toScheme U (Additive.ofMul g) := by
  apply TopCat.Presheaf.section_ext (cartierDivisorSheaf X.toScheme) U
  intro x hxU
  have hxorders (C : X.PrimeCurve) (hxC : x ∈ C) : C.order f = C.order g :=
    horders C (C.genericPoint_mem_of_mem ⟨x, hxU⟩ hxC)
  obtain ⟨V, hVU, hxV, b, hb⟩ :=
    X.exists_regular_unit_near_of_equal_curve_orders x U hxU f g hxorders
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hlocal : cartierEquationClassHom X.toScheme V (Additive.ofMul f) =
      cartierEquationClassHom X.toScheme V (Additive.ofMul g) :=
    (cartierEquationClassHom_eq_iff X.toScheme V f g).mpr
      ⟨b, by simpa only [div_eq_mul_inv] using hb⟩
  have hres : (cartierDivisorSheaf X.toScheme).val.map (homOfLE hVU).op
      (cartierEquationClassHom X.toScheme U (Additive.ofMul f)) =
    (cartierDivisorSheaf X.toScheme).val.map (homOfLE hVU).op
      (cartierEquationClassHom X.toScheme U (Additive.ofMul g)) := by
    simpa only [cartierEquationClassHom_restrict] using hlocal
  calc
    TopCat.Presheaf.germ (cartierDivisorSheaf X.toScheme).val U x hxU
        (cartierEquationClassHom X.toScheme U (Additive.ofMul f)) =
      TopCat.Presheaf.germ (cartierDivisorSheaf X.toScheme).val V x hxV
        ((cartierDivisorSheaf X.toScheme).val.map (homOfLE hVU).op
          (cartierEquationClassHom X.toScheme U (Additive.ofMul f))) :=
      (TopCat.Presheaf.germ_res_apply (cartierDivisorSheaf X.toScheme).val
        (homOfLE hVU) x hxV _).symm
    _ = TopCat.Presheaf.germ (cartierDivisorSheaf X.toScheme).val V x hxV
        ((cartierDivisorSheaf X.toScheme).val.map (homOfLE hVU).op
          (cartierEquationClassHom X.toScheme U (Additive.ofMul g))) :=
      congrArg (TopCat.Presheaf.germ (cartierDivisorSheaf X.toScheme).val V x hxV) hres
    _ = TopCat.Presheaf.germ (cartierDivisorSheaf X.toScheme).val U x hxU
        (cartierEquationClassHom X.toScheme U (Additive.ofMul g)) :=
      TopCat.Presheaf.germ_res_apply (cartierDivisorSheaf X.toScheme).val (homOfLE hVU) x hxV _

/-- Every actual finite Weil divisor on the locally factorial surface
is the image of an actual global Cartier divisor. The representative is
constructed by gluing proved local rational equations. -/
theorem exists_cartierDivisor_of_weilDivisor (D : X.WeilDivisor) :
    ∃ E : CartierDivisor X.toScheme, X.cartierToWeilHom E = D := by
  choose U hx f hf using fun x : X.toScheme =>
    X.exists_rationalEquation_near_of_stalk_ufd x D
  letI (x : X.toScheme) : Nonempty (U x) := ⟨⟨x, hx x⟩⟩
  let sf := fun x : X.toScheme =>
    cartierEquationClassHom X.toScheme (U x) (Additive.ofMul (f x))
  have hcover : (⊤ : X.toScheme.Opens) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hcompatible : TopCat.Presheaf.IsCompatible
      (cartierDivisorSheaf X.toScheme).val U sf := by
    intro x y
    letI : Nonempty (U x ⊓ U y : X.toScheme.Opens) :=
      ⟨⟨genericPoint X.toScheme,
        genericPoint_mem_nonempty_open X.toScheme (U x),
        genericPoint_mem_nonempty_open X.toScheme (U y)⟩⟩
    change (cartierDivisorSheaf X.toScheme).val.map
        (homOfLE (show U x ⊓ U y ≤ U x from inf_le_left)).op
        (cartierEquationClassHom X.toScheme (U x) (Additive.ofMul (f x))) =
      (cartierDivisorSheaf X.toScheme).val.map
        (homOfLE (show U x ⊓ U y ≤ U y from inf_le_right)).op
        (cartierEquationClassHom X.toScheme (U y) (Additive.ofMul (f y)))
    rw [cartierEquationClassHom_restrict, cartierEquationClassHom_restrict]
    apply X.cartierEquationClass_eq_of_equal_curve_orders (U x ⊓ U y) (f x) (f y)
    intro C hC
    exact (hf x C hC.1).trans (hf y C hC.2).symm
  obtain ⟨E, hE, -⟩ := (cartierDivisorSheaf X.toScheme).existsUnique_gluing' U ⊤
    (fun x => homOfLE (show U x ≤ ⊤ from le_top)) hcover sf hcompatible
  refine ⟨E, ?_⟩
  ext C
  exact (X.cartierToWeilHom_apply_of_equation E C (U C.genericPoint)
    (hx C.genericPoint) (f C.genericPoint) (hE C.genericPoint).symm).trans
      (hf C.genericPoint C (hx C.genericPoint))

/-- The actual Cartier-to-Weil homomorphism is surjective when every
actual stalk is factorial. -/
theorem cartierToWeilHom_surjective_of_stalks_ufd :
    Function.Surjective X.cartierToWeilHom :=
  X.exists_cartierDivisor_of_weilDivisor

end KltDP.Geometry.NormalProjectiveSurface
