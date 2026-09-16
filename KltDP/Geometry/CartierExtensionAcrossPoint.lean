import KltDP.Geometry.OpenCartierWeil
import KltDP.Geometry.CartierDivisorSupportedAtPoint
import KltDP.Geometry.PointBlowupPicardDecomposition
import KltDP.Geometry.ClosedPointDimension

/-!
# Extension of Cartier divisors and Picard classes across a closed point, and `picardDecomposition'`

BRIEF31, task 2 (F09 step (i)). `X` is a normal projective surface over an algebraically closed field
whose stalks are all factorial (for instance a regular surface, by the accepted
`stalks_uniqueFactorizationMonoid_of_regular`), and `V` a nonempty open subscheme.

* `extension V D := (cartierWeilEquiv X).symm (restrictedWeilHom V D)`: the Cartier divisor of the
  surface whose Weil divisor is the one built in `Geometry/OpenCartierWeil` from a Cartier divisor `D`
  of the open subscheme;
* **`cartierRestrictionHom_extension : cartierRestrictionHom V.ι (extension V D) = D`** — at every
  point of `V` a local equation of `extension V D` and a transported local equation of `D` have the
  same order along every prime curve through that point, so the accepted
  `cartierEquationClass_eq_of_equal_curve_orders` identifies their Cartier equation classes on a
  neighbourhood in `X`; the accepted `cartierPullback_equation` transports that identity to `V`;
* **`cartierRestrictionHom_surjective`, `schemePicardPullbackHom_surjective`**: restriction
  `CartierDivisor X → CartierDivisor V` and `Pic X → Pic V` are surjective for *every* nonempty open
  `V` (no hypothesis on the complement: the closure of a Weil divisor of `V` is a Weil divisor of `X`,
  and on a locally factorial surface it is Cartier);
* with the injectivity of `Geometry/CartierDivisorSupportedAtPoint` (which needs the complement to be a
  single closed point, and the two-dimensionality of its stalk, supplied here by the accepted
  `closed_stalk_dimension_two`): **`compl_schemePicardPullbackHom_bijective`**, `Pic X ≃ Pic (X ∖ {x})`
  for a closed point `x`, and `restrictPuncture_bijective` for the accepted point-blowup puncture;
* **`picardDecomposition' : Pic T ≃* Pic X × ker (Pic T → Pic (T ∖ E))`** — BRIEF29's
  `PointBlowupPicard.picardDecomposition` with its hypothesis `hres` discharged, and the kernel
  rewritten by the accepted-in-lane `ker_retraction`.

Still open for the F09 Picard formula: the identification of `ker (Pic T → Pic (T ∖ E))` with `ℤ · [E]`
(steps (iii) and (iv) of `laneA1/F09_PICARD_PLAN.md`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierExtension

open KltDP.Geometry.OpenImmersionRational KltDP.Geometry.OpenCartierWeil

variable {k : Type u} [Field k] [IsAlgClosed k] {X : NormalProjectiveSurface k}
  [∀ y : X.toScheme, UniqueFactorizationMonoid (X.stalk y)]

section Extension

variable (V : X.toScheme.Opens) [Nonempty V.toScheme]

local instance extensionOpenNonempty : Nonempty V := ⟨Classical.choice inferInstance⟩

local instance extensionOpenIntegral : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι

/-- The Cartier divisor of the surface attached to a Cartier divisor of the open subscheme `V`: the
accepted Cartier representative of the Weil divisor `restrictedWeilHom V D`. -/
def extension (D : CartierDivisor V.toScheme) : CartierDivisor X.toScheme :=
  X.cartierWeilEquiv.symm (restrictedWeilHom V D)

theorem cartierToWeilHom_extension (D : CartierDivisor V.toScheme) :
    X.cartierToWeilHom (extension V D) = restrictedWeilHom V D := by
  have h := X.cartierWeilEquiv.apply_symm_apply (restrictedWeilHom V D)
  rwa [X.cartierWeilEquiv_apply] at h

/-- **Every Cartier divisor of an open subscheme of a locally factorial normal projective surface
extends**: the restriction of `extension V D` to `V` is `D`. -/
theorem cartierRestrictionHom_extension (D : CartierDivisor V.toScheme) :
    cartierRestrictionHom V.ι (extension V D) = D := by
  apply TopCat.Presheaf.section_ext (cartierDivisorSheaf V.toScheme) ⊤
  intro z _
  obtain ⟨W, hzW, hW⟩ := cartierOrderEquation_spec V.toScheme D z
  letI : Nonempty W := ⟨⟨z, hzW⟩⟩
  letI := nonempty_image V.ι W
  obtain ⟨e, U₀, hzU₀, hU₀⟩ := exists_cartierOrderEquation X.toScheme (extension V D) (V.ι.base z)
  letI : Nonempty U₀ := ⟨⟨V.ι.base z, hzU₀⟩⟩
  have hzU : V.ι.base z ∈ U₀ ⊓ (V.ι ''ᵁ W) :=
    ⟨hzU₀, (Scheme.Hom.map_mem_image_iff V.ι).mpr hzW⟩
  letI : Nonempty (U₀ ⊓ (V.ι ''ᵁ W) : X.toScheme.Opens) := ⟨⟨V.ι.base z, hzU⟩⟩
  have hUe : cartierEquationClassHom X.toScheme (U₀ ⊓ (V.ι ''ᵁ W)) (Additive.ofMul e) =
      (cartierDivisorSheaf X.toScheme).val.map
        (homOfLE (show U₀ ⊓ (V.ι ''ᵁ W) ≤ ⊤ from le_top)).op (extension V D) :=
    cartierGlobalEquation_restrict X.toScheme (extension V D)
      (homOfLE (show U₀ ⊓ (V.ι ''ᵁ W) ≤ U₀ from inf_le_left)) e hU₀
  have horders : ∀ C : X.PrimeCurve, C.genericPoint ∈ U₀ ⊓ (V.ι ''ᵁ W) →
      C.order e = C.order (transportUnit V (cartierOrderEquation V.toScheme D z)) := by
    intro C hC
    have h1 : X.cartierToWeilHom (extension V D) C = C.order e :=
      X.cartierToWeilHom_apply_of_equation (extension V D) C (U₀ ⊓ (V.ι ''ᵁ W)) hC e hUe
    have h2 : X.cartierToWeilHom (extension V D) C = restrictedCoefficient V D C :=
      congrArg (fun E : X.WeilDivisor => E C) (cartierToWeilHom_extension V D)
    have h3 : restrictedCoefficient V D C =
        C.order (transportUnit V (cartierOrderEquation V.toScheme D z)) :=
      restrictedCoefficient_eq_of_equation V D C W hC.2 _ hW
    exact h1.symm.trans (h2.trans h3)
  have hclass := X.cartierEquationClass_eq_of_equal_curve_orders (U₀ ⊓ (V.ι ''ᵁ W)) e
    (transportUnit V (cartierOrderEquation V.toScheme D z)) horders
  letI : Nonempty (V.ι ⁻¹ᵁ (U₀ ⊓ (V.ι ''ᵁ W) : X.toScheme.Opens)) := ⟨⟨z, hzU⟩⟩
  have hpull : cartierEquationClassHom V.toScheme
        (V.ι ⁻¹ᵁ (U₀ ⊓ (V.ι ''ᵁ W) : X.toScheme.Opens))
        (Additive.ofMul (Units.map (functionFieldIso V.ι).hom.hom.toMonoidHom e)) =
      cartierEquationClassHom V.toScheme (V.ι ⁻¹ᵁ (U₀ ⊓ (V.ι ''ᵁ W) : X.toScheme.Opens))
        (Additive.ofMul (cartierOrderEquation V.toScheme D z)) := by
    have hc := congrArg (fun s => (cartierPullback V.ι).val.app
      (op (U₀ ⊓ (V.ι ''ᵁ W) : X.toScheme.Opens)) s) hclass
    simp only [cartierPullback_equation] at hc
    rwa [transportUnit_hom] at hc
  have hres : cartierEquationClassHom V.toScheme
        (V.ι ⁻¹ᵁ (U₀ ⊓ (V.ι ''ᵁ W) : X.toScheme.Opens))
        (Additive.ofMul (Units.map (functionFieldIso V.ι).hom.hom.toMonoidHom e)) =
      (cartierDivisorSheaf V.toScheme).val.map
        (homOfLE (show V.ι ⁻¹ᵁ (U₀ ⊓ (V.ι ''ᵁ W) : X.toScheme.Opens) ≤ ⊤ from le_top)).op
        (cartierRestrictionHom V.ι (extension V D)) :=
    cartierRestriction_globalEquation_preimage V.ι (extension V D)
      (U₀ ⊓ (V.ι ''ᵁ W) : X.toScheme.Opens) e hUe
  have hle : V.ι ⁻¹ᵁ (U₀ ⊓ (V.ι ''ᵁ W) : X.toScheme.Opens) ≤ W := by
    intro y hy
    have hy' : y ∈ V.ι ⁻¹ᵁ (V.ι ''ᵁ W) := hy.2
    rwa [Scheme.Hom.preimage_image_eq] at hy'
  have hDeq : cartierEquationClassHom V.toScheme
        (V.ι ⁻¹ᵁ (U₀ ⊓ (V.ι ''ᵁ W) : X.toScheme.Opens))
        (Additive.ofMul (cartierOrderEquation V.toScheme D z)) =
      (cartierDivisorSheaf V.toScheme).val.map
        (homOfLE (show V.ι ⁻¹ᵁ (U₀ ⊓ (V.ι ''ᵁ W) : X.toScheme.Opens) ≤ ⊤ from le_top)).op D :=
    cartierGlobalEquation_restrict V.toScheme D (homOfLE hle) _ hW
  have hsections := hres.symm.trans (hpull.trans hDeq)
  exact (TopCat.Presheaf.germ_res_apply (cartierDivisorSheaf V.toScheme).val
      (homOfLE (show V.ι ⁻¹ᵁ (U₀ ⊓ (V.ι ''ᵁ W) : X.toScheme.Opens) ≤ ⊤ from le_top)) z hzU
      (cartierRestrictionHom V.ι (extension V D))).symm.trans
    ((congrArg (TopCat.Presheaf.germ (cartierDivisorSheaf V.toScheme).val
        (V.ι ⁻¹ᵁ (U₀ ⊓ (V.ι ''ᵁ W) : X.toScheme.Opens)) z hzU) hsections).trans
      (TopCat.Presheaf.germ_res_apply (cartierDivisorSheaf V.toScheme).val
        (homOfLE (show V.ι ⁻¹ᵁ (U₀ ⊓ (V.ι ''ᵁ W) : X.toScheme.Opens) ≤ ⊤ from le_top)) z hzU D))

/-- **Restriction of Cartier divisors to a nonempty open subscheme is surjective.** -/
theorem cartierRestrictionHom_surjective :
    Function.Surjective (cartierRestrictionHom V.ι) :=
  fun D => ⟨extension V D, cartierRestrictionHom_extension V D⟩

/-- **Restriction of Picard classes to a nonempty open subscheme is surjective**, `Pic X → Pic V`. -/
theorem schemePicardPullbackHom_surjective :
    Function.Surjective (schemePicardPullbackHom V.ι) := by
  intro c
  obtain ⟨D, hD⟩ := cartierPicardClass_surjective V.toScheme c
  refine ⟨cartierPicardClass X.toScheme (extension V D), ?_⟩
  rw [schemePicardPullbackHom_cartierPicardClass, cartierRestrictionHom_extension, hD]

end Extension

/-! ## Bijectivity off a closed point, and the Picard decomposition of a point blowup -/

section Puncture

/-- **`Pic X → Pic (X ∖ {x})` is bijective** for a closed point of a locally factorial normal
projective surface: surjectivity above, injectivity from `Geometry/CartierDivisorSupportedAtPoint`
with the two-dimensionality of the stalk supplied by the accepted `closed_stalk_dimension_two`. -/
theorem schemePicardPullbackHom_bijective_of_forall_ne (x : X.toScheme)
    (hdim : ringKrullDim (X.toScheme.presheaf.stalk x) = 2) (V : X.toScheme.Opens)
    [Nonempty V.toScheme] (hV : ∀ y, y ≠ x → y ∈ V) :
    Function.Bijective (schemePicardPullbackHom V.ι) :=
  ⟨CartierSupportedAtPoint.schemePicardPullbackHom_injective hdim hV,
    schemePicardPullbackHom_surjective V⟩

set_option maxHeartbeats 1000000 in
theorem compl_schemePicardPullbackHom_bijective (x : X.toScheme)
    (hx : IsClosed ({x} : Set X.toScheme)) :
    Function.Bijective (schemePicardPullbackHom
      (Scheme.Opens.ι (⟨({x} : Set X.toScheme)ᶜ, hx.isOpen_compl⟩ : X.toScheme.Opens))) := by
  have hdim : ringKrullDim (X.toScheme.presheaf.stalk x) = 2 :=
    X.closed_stalk_dimension_two x hx
  haveI hne : Nonempty (⟨({x} : Set X.toScheme)ᶜ, hx.isOpen_compl⟩ : X.toScheme.Opens) :=
    CartierSupportedAtPoint.nonempty_of_forall_ne hdim (fun _ hy => hy)
  haveI : Nonempty (Scheme.Opens.toScheme
      (⟨({x} : Set X.toScheme)ᶜ, hx.isOpen_compl⟩ : X.toScheme.Opens)) := ⟨Classical.choice hne⟩
  exact schemePicardPullbackHom_bijective_of_forall_ne x hdim
    (⟨({x} : Set X.toScheme)ᶜ, hx.isOpen_compl⟩ : X.toScheme.Opens) (fun _ hy => hy)

open KltDP.Geometry.PointBlowupGluing KltDP.Geometry.PointBlowupPicard

variable {R : Type u} [CommRing R] (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
  (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
  (hclosed : IsClosed ({j.base q} : Set X.toScheme))

/-- The hypothesis `hres` of BRIEF29's `picardDecomposition`, discharged for a closed point of a
locally factorial normal projective surface. -/
theorem restrictPuncture_bijective : Function.Bijective (restrictPuncture j q hclosed) := by
  have hdim : ringKrullDim (X.toScheme.presheaf.stalk (j.base q)) = 2 :=
    X.closed_stalk_dimension_two (j.base q) hclosed
  haveI hne : Nonempty (puncture j q hclosed) :=
    CartierSupportedAtPoint.nonempty_of_forall_ne hdim (fun _ hy => hy)
  haveI : Nonempty (puncture j q hclosed).toScheme := ⟨Classical.choice hne⟩
  exact ⟨CartierSupportedAtPoint.puncture_schemePicardPullbackHom_injective j q hclosed hdim,
    schemePicardPullbackHom_surjective (puncture j q hclosed)⟩

/-- **The Picard group of the blowup of a closed point of a locally factorial normal projective
surface**: `Pic T ≃* Pic X × ker (Pic T → Pic (T ∖ E))`, BRIEF29's `picardDecomposition` with `hres`
discharged and the kernel rewritten by `ker_retraction`. -/
def picardDecomposition' :
    (scheme j q hclosed).Pic ≃* X.toScheme.Pic × ↥(restrictComplement j q hclosed).ker :=
  (picardDecomposition j q hclosed (restrictPuncture_bijective j q hclosed)).trans
    (MulEquiv.prodCongr (MulEquiv.refl X.toScheme.Pic)
      (MulEquiv.subgroupCongr
        (ker_retraction j q hclosed (restrictPuncture_bijective j q hclosed))))

end Puncture

/-- Universe check at `Type`/`Scheme.{0}`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (X₀ : NormalProjectiveSurface k₀)
    [∀ y : X₀.toScheme, UniqueFactorizationMonoid (X₀.stalk y)] (V₀ : X₀.toScheme.Opens)
    [Nonempty V₀.toScheme] : Function.Surjective (schemePicardPullbackHom V₀.ι) :=
  schemePicardPullbackHom_surjective V₀

end KltDP.Geometry.CartierExtension
