import KltDP.Geometry.WeilCartierEquiv
import KltDP.Geometry.CartierOpenRestrictionEquations
import KltDP.Geometry.PrimeCurveStalkCoordinates

/-!
# The Weil divisor on a surface of a Cartier divisor given on an open subscheme

BRIEF31, task 2 (F09 step (i), surjectivity half; route S of `laneA1/F09_PICARD_PLAN.md` §4). `X` is a
normal projective surface over an algebraically closed field and `V` a nonempty open subscheme. A Cartier
divisor `D` of the *open* subscheme `V` has no accepted order theory of its own (prime curves, their DVR
stalks, principal divisors and the Cartier–Weil comparison are accepted only on
`NormalProjectiveSurface`s, and `V` is not projective). This module produces from `D` an honest Weil
divisor of `X`, by transporting the local rational equations of `D` along the accepted function-field
isomorphism `functionFieldIso V.ι` and taking their accepted orders `PrimeCurve.order` at the generic
points of the prime curves of `X`.

* `transportUnit V : V.functionFieldˣ → X.functionFieldˣ` (the inverse of the accepted
  `functionFieldIso V.ι`), with `transportUnit_germ`: a regular unit on `W ⊆ V` transports to the germ of
  its image under `V.ι.appIso` on `V.ι ''ᵁ W`;
* `cartierEquationClassHom_image_eq_of_eq`: two rational functions with the same Cartier equation class on
  `W` have the same equation class, after transport, on `V.ι ''ᵁ W`;
* `restrictedCoefficient V D C`: the order of `D` along a prime curve `C` of `X` — the accepted
  `C.order` of a transported local equation of `D` at `C.genericPoint` if that generic point lies in `V`,
  and `0` otherwise (a curve avoiding `V` cannot be seen by `D`). Generic points of prime curves are not
  closed points, so for `V` the complement of a closed point no curve is lost.
  `restrictedCoefficient_eq_of_equation` computes it from *any* local equation whose chart contains
  `C.genericPoint`, so the value does not depend on the chosen equation;
* `restrictedCoefficient_zero`, `restrictedCoefficient_add`, `restrictedCoefficient_finite_support`
  (the finiteness uses quasi-compactness of `V` inside the Noetherian surface and the accepted
  `order_finite_support` on each of the finitely many charts), giving
  **`restrictedWeilHom V : CartierDivisor V.toScheme →+ X.WeilDivisor`**.

Nothing here inverts the construction: that `(cartierWeilEquiv X).symm (restrictedWeilHom V D)` really
restricts to `D` is proved in `Geometry/CartierExtensionAcrossPoint`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenCartierWeil

open KltDP.Geometry.OpenImmersionRational

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}
variable (V : X.toScheme.Opens) [Nonempty V.toScheme]

local instance openNonempty : Nonempty V := ⟨Classical.choice inferInstance⟩

local instance openIntegral : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι

local instance primeCurveStalkDVR (C : X.PrimeCurve) :
    IsDiscreteValuationRing (X.toScheme.presheaf.stalk C.genericPoint) :=
  C.genericPoint_isDiscreteValuationRing

/-! ## Transport of rational functions from the open subscheme -/

/-- Transport of a nonzero rational function of the open subscheme `V` to the surface, along the
accepted function-field isomorphism of the open immersion `V.ι`. -/
def transportUnit (f : V.toScheme.functionFieldˣ) : X.toScheme.functionFieldˣ :=
  Units.map (functionFieldIso V.ι).inv.hom.toMonoidHom f

theorem transportUnit_hom (f : V.toScheme.functionFieldˣ) :
    Units.map (functionFieldIso V.ι).hom.hom.toMonoidHom (transportUnit V f) = f := by
  apply Units.ext
  exact Iso.inv_hom_id_apply (functionFieldIso V.ι) (f : V.toScheme.functionField)

theorem transportUnit_one : transportUnit V 1 = 1 := map_one _

theorem transportUnit_mul (f g : V.toScheme.functionFieldˣ) :
    transportUnit V (f * g) = transportUnit V f * transportUnit V g := map_mul _ _ _

theorem transportUnit_div (f g : V.toScheme.functionFieldˣ) :
    transportUnit V (f / g) = transportUnit V f / transportUnit V g := map_div _ _ _

/-- A regular unit on an open `W` of `V` transports to the germ on `V.ι ''ᵁ W` of its image under the
accepted section isomorphism of the open immersion. -/
theorem transportUnit_germ (W : V.toScheme.Opens) [Nonempty W] (a : Γ(V.toScheme, W)ˣ) :
    letI := nonempty_image V.ι W
    Units.map (X.toScheme.germToFunctionField (V.ι ''ᵁ W)).hom.toMonoidHom
        (Units.map (V.ι.appIso W).inv.hom.toMonoidHom a) =
      transportUnit V (Units.map (V.toScheme.germToFunctionField W).hom.toMonoidHom a) := by
  letI := nonempty_image V.ι W
  apply Units.ext
  apply (functionFieldIso V.ι).hom.hom.injective
  have h1 : (functionFieldIso V.ι).hom (X.toScheme.germToFunctionField (V.ι ''ᵁ W)
        ((V.ι.appIso W).inv (a : Γ(V.toScheme, W)))) =
      V.toScheme.germToFunctionField W
        ((V.ι.appIso W).hom ((V.ι.appIso W).inv (a : Γ(V.toScheme, W)))) :=
    functionFieldIso_image_germ V.ι W _
  rw [Iso.inv_hom_id_apply] at h1
  change (functionFieldIso V.ι).hom (X.toScheme.germToFunctionField (V.ι ''ᵁ W)
      ((V.ι.appIso W).inv (a : Γ(V.toScheme, W)))) =
    (functionFieldIso V.ι).hom ((functionFieldIso V.ι).inv
      (V.toScheme.germToFunctionField W (a : Γ(V.toScheme, W))))
  rw [h1, Iso.inv_hom_id_apply]

/-- Equal Cartier equation classes on an open of `V` transport to equal equation classes on its image
open of the surface. -/
theorem cartierEquationClassHom_image_eq_of_eq (W : V.toScheme.Opens) [Nonempty W]
    (f g : V.toScheme.functionFieldˣ)
    (h : cartierEquationClassHom V.toScheme W (Additive.ofMul f) =
      cartierEquationClassHom V.toScheme W (Additive.ofMul g)) :
    letI := nonempty_image V.ι W
    cartierEquationClassHom X.toScheme (V.ι ''ᵁ W) (Additive.ofMul (transportUnit V f)) =
      cartierEquationClassHom X.toScheme (V.ι ''ᵁ W) (Additive.ofMul (transportUnit V g)) := by
  letI := nonempty_image V.ι W
  obtain ⟨a, ha⟩ := (cartierEquationClassHom_eq_iff V.toScheme W f g).mp h
  refine (cartierEquationClassHom_eq_iff X.toScheme (V.ι ''ᵁ W) _ _).mpr
    ⟨Units.map (V.ι.appIso W).inv.hom.toMonoidHom a, ?_⟩
  rw [transportUnit_germ V W a, ha, transportUnit_div]

/-! ## The order of a Cartier divisor of the open subscheme along a prime curve -/

/-- A chosen local rational equation of `D` near a point of `V`, transported to the surface. -/
def restrictedEquation (D : CartierDivisor V.toScheme) (y : V.toScheme) :
    X.toScheme.functionFieldˣ :=
  transportUnit V (cartierOrderEquation V.toScheme D y)

open scoped Classical in
/-- The order of a Cartier divisor of the open subscheme `V` along a prime curve of the surface:
the accepted order of a transported local equation at the curve's generic point when that point lies
in `V`, and `0` for the curves that avoid `V`. -/
def restrictedCoefficient (D : CartierDivisor V.toScheme) (C : X.PrimeCurve) : ℤ :=
  if h : C.genericPoint ∈ V then C.order (restrictedEquation V D ⟨C.genericPoint, h⟩) else 0

theorem restrictedCoefficient_of_mem (D : CartierDivisor V.toScheme) (C : X.PrimeCurve)
    (h : C.genericPoint ∈ V) :
    restrictedCoefficient V D C = C.order (restrictedEquation V D ⟨C.genericPoint, h⟩) := by
  classical
  exact dif_pos h

theorem restrictedCoefficient_of_not_mem (D : CartierDivisor V.toScheme) (C : X.PrimeCurve)
    (h : C.genericPoint ∉ V) : restrictedCoefficient V D C = 0 := by
  classical
  exact dif_neg h

/-- **Every local equation computes the coefficient**: if `f` is a rational equation of `D` on an open
`W` of `V` whose image contains the generic point of `C`, then the coefficient of `C` is the accepted
order of the transported `f`. In particular the coefficient does not depend on the chosen equation. -/
theorem restrictedCoefficient_eq_of_equation (D : CartierDivisor V.toScheme) (C : X.PrimeCurve)
    (W : V.toScheme.Opens) [Nonempty W] (hCW : C.genericPoint ∈ V.ι ''ᵁ W)
    (f : V.toScheme.functionFieldˣ)
    (hf : cartierEquationClassHom V.toScheme W (Additive.ofMul f) =
      (cartierDivisorSheaf V.toScheme).val.map (homOfLE (show W ≤ ⊤ from le_top)).op D) :
    restrictedCoefficient V D C = C.order (transportUnit V f) := by
  have hCV : C.genericPoint ∈ V := V.ι_image_le W hCW
  have hy : (⟨C.genericPoint, hCV⟩ : V.toScheme) ∈ W :=
    (Scheme.Hom.map_mem_image_iff V.ι).mp hCW
  obtain ⟨W₀, hyW₀, hW₀⟩ :=
    cartierOrderEquation_spec V.toScheme D (⟨C.genericPoint, hCV⟩ : V.toScheme)
  letI : Nonempty W₀ := ⟨⟨⟨C.genericPoint, hCV⟩, hyW₀⟩⟩
  have hyW' : (⟨C.genericPoint, hCV⟩ : V.toScheme) ∈ W₀ ⊓ W := ⟨hyW₀, hy⟩
  letI : Nonempty (W₀ ⊓ W : V.toScheme.Opens) := ⟨⟨⟨C.genericPoint, hCV⟩, hyW'⟩⟩
  have h0 : cartierEquationClassHom V.toScheme (W₀ ⊓ W)
        (Additive.ofMul (cartierOrderEquation V.toScheme D ⟨C.genericPoint, hCV⟩)) =
      (cartierDivisorSheaf V.toScheme).val.map
        (homOfLE (show W₀ ⊓ W ≤ ⊤ from le_top)).op D :=
    cartierGlobalEquation_restrict V.toScheme D
      (homOfLE (show W₀ ⊓ W ≤ W₀ from inf_le_left)) _ hW₀
  have h1 : cartierEquationClassHom V.toScheme (W₀ ⊓ W) (Additive.ofMul f) =
      (cartierDivisorSheaf V.toScheme).val.map
        (homOfLE (show W₀ ⊓ W ≤ ⊤ from le_top)).op D :=
    cartierGlobalEquation_restrict V.toScheme D
      (homOfLE (show W₀ ⊓ W ≤ W from inf_le_right)) f hf
  letI := nonempty_image V.ι (W₀ ⊓ W : V.toScheme.Opens)
  have hmem : C.genericPoint ∈ V.ι ''ᵁ (W₀ ⊓ W : V.toScheme.Opens) :=
    (Scheme.Hom.map_mem_image_iff V.ι).mpr hyW'
  have himg := cartierEquationClassHom_image_eq_of_eq V (W₀ ⊓ W)
    (cartierOrderEquation V.toScheme D ⟨C.genericPoint, hCV⟩) f (h0.trans h1.symm)
  rw [restrictedCoefficient_of_mem V D C hCV]
  exact stalkDivisorOrder_eq_of_cartierEquation_eq X.toScheme C.genericPoint
    (V.ι ''ᵁ (W₀ ⊓ W : V.toScheme.Opens)) hmem _ _ himg

theorem restrictedCoefficient_zero (C : X.PrimeCurve) :
    restrictedCoefficient V (0 : CartierDivisor V.toScheme) C = 0 := by
  by_cases hCV : C.genericPoint ∈ V
  · have hmem : C.genericPoint ∈ V.ι ''ᵁ (⊤ : V.toScheme.Opens) :=
      (Scheme.Hom.map_mem_image_iff V.ι (U := ⊤)
        (x := (⟨C.genericPoint, hCV⟩ : V.toScheme))).mpr trivial
    rw [restrictedCoefficient_eq_of_equation V 0 C ⊤ hmem 1 (by simp), transportUnit_one,
      C.order_one]
  · exact restrictedCoefficient_of_not_mem V _ C hCV

theorem restrictedCoefficient_add (D E : CartierDivisor V.toScheme) (C : X.PrimeCurve) :
    restrictedCoefficient V (D + E) C =
      restrictedCoefficient V D C + restrictedCoefficient V E C := by
  by_cases hCV : C.genericPoint ∈ V
  · obtain ⟨W, i, hyW, f, g, hf, hg⟩ := exists_common_cartier_equations V.toScheme D E ⊤
      (⟨C.genericPoint, hCV⟩ : V.toScheme) trivial
    letI : Nonempty W := ⟨⟨⟨C.genericPoint, hCV⟩, hyW⟩⟩
    have hmem : C.genericPoint ∈ V.ι ''ᵁ W := (Scheme.Hom.map_mem_image_iff V.ι).mpr hyW
    have hfg : cartierEquationClassHom V.toScheme W (Additive.ofMul (f * g)) =
        (cartierDivisorSheaf V.toScheme).val.map
          (homOfLE (show W ≤ ⊤ from le_top)).op (D + E) := by
      change cartierEquationClassHom V.toScheme W (Additive.ofMul f + Additive.ofMul g) = _
      rw [map_add, hf, hg, map_add]
    rw [restrictedCoefficient_eq_of_equation V (D + E) C W hmem (f * g) hfg,
      restrictedCoefficient_eq_of_equation V D C W hmem f hf,
      restrictedCoefficient_eq_of_equation V E C W hmem g hg, transportUnit_mul,
      C.order_mul]
  · rw [restrictedCoefficient_of_not_mem V (D + E) C hCV,
      restrictedCoefficient_of_not_mem V D C hCV,
      restrictedCoefficient_of_not_mem V E C hCV, add_zero]

/-- **Finite support**: the open `V` is quasi-compact inside the Noetherian surface, so finitely many
equation charts cover it, and the accepted `order_finite_support` bounds the curves with nonzero order
on each chart. -/
theorem restrictedCoefficient_finite_support (D : CartierDivisor V.toScheme) :
    (Function.support (fun C : X.PrimeCurve => restrictedCoefficient V D C)).Finite := by
  classical
  choose W hy hrep using fun y : V.toScheme => cartierOrderEquation_spec V.toScheme D y
  have hcover : (V : Set X.toScheme) ⊆
      ⋃ y : V.toScheme, (V.ι ''ᵁ W y : Set X.toScheme) := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨(⟨z, hz⟩ : V.toScheme),
      (Scheme.Hom.map_mem_image_iff V.ι).mpr (hy (⟨z, hz⟩ : V.toScheme))⟩
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (V : Set X.toScheme)).elim_finite_subcover
    (fun y : V.toScheme => (V.ι ''ᵁ W y : Set X.toScheme))
    (fun y => (V.ι ''ᵁ W y).isOpen) hcover
  have hfinite : (⋃ y ∈ t, Function.support (fun C : X.PrimeCurve =>
      C.order (transportUnit V (cartierOrderEquation V.toScheme D y)))).Finite :=
    t.finite_toSet.biUnion (fun y _ => X.order_finite_support _)
  refine hfinite.subset ?_
  intro C hC
  have hCV : C.genericPoint ∈ V := by
    by_contra hno
    exact hC (restrictedCoefficient_of_not_mem V D C hno)
  obtain ⟨y, hyt, hyC⟩ := Set.mem_iUnion₂.mp (ht hCV)
  refine Set.mem_iUnion₂.mpr ⟨y, hyt, ?_⟩
  letI : Nonempty (W y) := ⟨⟨y, hy y⟩⟩
  have hval := restrictedCoefficient_eq_of_equation V D C (W y) hyC
    (cartierOrderEquation V.toScheme D y) (hrep y)
  change C.order (transportUnit V (cartierOrderEquation V.toScheme D y)) ≠ 0
  rw [← hval]
  exact hC

/-! ## The Weil divisor of a Cartier divisor of the open subscheme -/

/-- The Weil divisor of the surface attached to a Cartier divisor of the open subscheme `V`. -/
def restrictedWeil (D : CartierDivisor V.toScheme) : X.WeilDivisor :=
  Finsupp.ofSupportFinite (fun C => restrictedCoefficient V D C)
    (restrictedCoefficient_finite_support V D)

@[simp]
theorem restrictedWeil_apply (D : CartierDivisor V.toScheme) (C : X.PrimeCurve) :
    restrictedWeil V D C = restrictedCoefficient V D C := rfl

/-- **`CartierDivisor V → WeilDivisor X`**, additively. -/
def restrictedWeilHom : CartierDivisor V.toScheme →+ X.WeilDivisor where
  toFun := restrictedWeil V
  map_zero' := by
    apply Finsupp.ext
    intro C
    exact restrictedCoefficient_zero V C
  map_add' D E := by
    apply Finsupp.ext
    intro C
    exact restrictedCoefficient_add V D E C

@[simp]
theorem restrictedWeilHom_apply (D : CartierDivisor V.toScheme) (C : X.PrimeCurve) :
    restrictedWeilHom V D C = restrictedCoefficient V D C := rfl

end KltDP.Geometry.OpenCartierWeil
