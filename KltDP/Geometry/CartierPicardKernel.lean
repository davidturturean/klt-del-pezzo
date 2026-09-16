import KltDP.Geometry.CartierPicardHom

/-!
# The kernel of the actual Cartier-to-Picard homomorphism

An actual trivialization of O(D) supplies a global rational section. On
every equation chart its coordinate is a unit: it is the image of one
under a linear automorphism of the actual section ring. The inverse of
this global rational generator is consequently an equation for D on all
charts. Sheaf separatedness identifies D with that principal divisor.

The argument uses pinned module-sheaf evaluation, the corresponding
actual component linear equivalences, and the ordinary sheaf section
extensionality theorem. It does not assume a Cartier/Picard equivalence.
The already defined Cartier-to-Picard homomorphism therefore has precisely
the actual principal Cartier divisors as its kernel. Surjectivity onto
the Picard group remains a separate assertion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem linearEquiv_self_apply_one_isUnit
    {R : Type*} [CommRing R] (e : R ≃ₗ[R] R) : IsUnit (e 1) := by
  obtain ⟨a, ha⟩ := e.surjective 1
  have hmul : e a = a * e 1 := by
    simpa only [smul_eq_mul, mul_one] using e.map_smul a (1 : R)
  exact isUnit_of_mul_eq_one_right a (e 1) (hmul.symm.trans ha)

variable (X : Scheme.{u}) [IsIntegral X]

/-- An actual sheaf trivialization gives the actual linear equivalence
on the sections of every open. -/
def cartierTrivializationSectionEquiv (D : CartierDivisor X)
    (e : _root_.SheafOfModules.unit X.ringCatSheaf ≅ cartierDivisorModule X D)
    (U : X.Opens) :
    Γ(X, U) ≃ₗ[Γ(X, U)] (cartierDivisorModule X D).val.obj (op U) :=
  ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso e).toLinearEquiv

@[simp]
theorem cartierTrivializationSectionEquiv_apply (D : CartierDivisor X)
    (e : _root_.SheafOfModules.unit X.ringCatSheaf ≅ cartierDivisorModule X D)
    (U : X.Opens) (a : Γ(X, U)) :
    cartierTrivializationSectionEquiv X D e U a = e.hom.val.app (op U) a := rfl

/-- The generator furnished by an actual trivialization restricts to
the generator furnished by that same trivialization on every smaller open. -/
theorem cartierTrivialization_generator_restrict (D : CartierDivisor X)
    (e : _root_.SheafOfModules.unit X.ringCatSheaf ≅ cartierDivisorModule X D)
    {U V : X.Opens} (i : V ⟶ U) :
    (cartierDivisorModule X D).val.map i.op (e.hom.val.app (op U) (1 : Γ(X, U))) =
      e.hom.val.app (op V) (1 : Γ(X, V)) := by
  have h := (PresheafOfModules.naturality_apply e.hom.val i.op (1 : Γ(X, U))).symm
  have hone : (_root_.SheafOfModules.unit X.ringCatSheaf).val.map i.op
      (1 : Γ(X, U)) = (1 : Γ(X, V)) :=
    PresheafOfModules.unit_map_one X.ringCatSheaf.val i.op
  exact h.trans (congrArg (fun a : Γ(X, V) => e.hom.val.app (op V) a) hone)

/-- The original function-field value of the global trivializing section. -/
def cartierTrivializationRationalGenerator (D : CartierDivisor X)
    (e : _root_.SheafOfModules.unit X.ringCatSheaf ≅ cartierDivisorModule X D) :
    X.functionField :=
  rationalFunctionModuleSectionsEquiv X ⊤ (e.hom.val.app (op ⊤) (1 : Γ(X, ⊤))).val

/-- On every nonempty open the same generator represents the same
element of the original function field. -/
theorem cartierTrivializationRationalGenerator_restrict (D : CartierDivisor X)
    (e : _root_.SheafOfModules.unit X.ringCatSheaf ≅ cartierDivisorModule X D)
    (U : X.Opens) [Nonempty U] :
    rationalFunctionModuleSectionsEquiv X U (e.hom.val.app (op U) (1 : Γ(X, U))).val =
      cartierTrivializationRationalGenerator X D e := by
  have h := congrArg Subtype.val
    (cartierTrivialization_generator_restrict X D e
      (homOfLE (show U ≤ ⊤ from le_top)))
  calc
    rationalFunctionModuleSectionsEquiv X U (e.hom.val.app (op U) (1 : Γ(X, U))).val =
        rationalFunctionModuleSectionsEquiv X U
          ((rationalFunctionModule X).val.map
            (homOfLE (show U ≤ ⊤ from le_top)).op
            (e.hom.val.app (op ⊤) (1 : Γ(X, ⊤))).val) := congrArg _ h.symm
    _ = cartierTrivializationRationalGenerator X D e :=
      rationalFunctionModuleSectionsEquiv_naturality X _ _

/-- On an actual equation chart the global generator is `a/f` for an
actual regular unit a. The unit condition is proved from the linear
automorphism obtained by comparing the two actual trivializations. -/
theorem exists_unit_cartierTrivializationRationalGenerator (D : CartierDivisor X)
    (e : _root_.SheafOfModules.unit X.ringCatSheaf ≅ cartierDivisorModule X D)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D) :
    ∃ a : Γ(X, U)ˣ,
      cartierTrivializationRationalGenerator X D e =
        (X.germToFunctionField U).hom (a : Γ(X, U)) * (↑(f⁻¹) : X.functionField) := by
  let θ := cartierEquationSectionEquiv X D U f hf
  let α := cartierTrivializationSectionEquiv X D e U ≪≫ₗ θ.symm
  obtain ⟨a, ha⟩ := linearEquiv_self_apply_one_isUnit α
  have hcoord : θ (a : Γ(X, U)) = e.hom.val.app (op U) (1 : Γ(X, U)) := by
    rw [ha]
    exact θ.apply_symm_apply (cartierTrivializationSectionEquiv X D e U 1)
  refine ⟨a, ?_⟩
  calc
    cartierTrivializationRationalGenerator X D e =
        rationalFunctionModuleSectionsEquiv X U (e.hom.val.app (op U) (1 : Γ(X, U))).val :=
      (cartierTrivializationRationalGenerator_restrict X D e U).symm
    _ = rationalFunctionModuleSectionsEquiv X U (θ (a : Γ(X, U))).val :=
      congrArg (fun s : (cartierDivisorModule X D).val.obj (op U) =>
        rationalFunctionModuleSectionsEquiv X U s.val) hcoord.symm
    _ = (X.germToFunctionField U).hom (a : Γ(X, U)) * (↑(f⁻¹) : X.functionField) :=
      cartierEquationSectionEquiv_apply_field X D U f hf a

/-- A trivial actual divisor module forces an actual global principal
equation, with the sign fixed by O(D) = f⁻¹ O. -/
theorem exists_principalCartierDivisor_of_trivialization (D : CartierDivisor X)
    (e : _root_.SheafOfModules.unit X.ringCatSheaf ≅ cartierDivisorModule X D) :
    ∃ f : X.functionFieldˣ, D = principalCartierDivisorHom X (Additive.ofMul f) := by
  obtain ⟨U, i, hxU, f, hf⟩ :=
    exists_local_cartier_equation X ⊤ D (genericPoint X) trivial
  letI : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  have hi : i = homOfLE (show U ≤ ⊤ from le_top) := Subsingleton.elim _ _
  have hf' : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D := by
    simpa only [hi] using hf
  obtain ⟨a, ha⟩ := exists_unit_cartierTrivializationRationalGenerator X D e U f hf'
  let r : X.functionFieldˣ := Units.map (X.germToFunctionField U).hom.toMonoidHom a * f⁻¹
  have hr : (r : X.functionField) = cartierTrivializationRationalGenerator X D e := ha.symm
  refine ⟨r⁻¹, ?_⟩
  apply TopCat.Presheaf.IsSheaf.section_ext (cartierDivisorSheaf X).cond
  intro x hx
  obtain ⟨V, j, hxV, g, hg⟩ := exists_local_cartier_equation X ⊤ D x trivial
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hj : j = homOfLE (show V ≤ ⊤ from le_top) := Subsingleton.elim _ _
  have hg' : cartierEquationClassHom X V (Additive.ofMul g) =
      (cartierDivisorSheaf X).val.map (homOfLE (show V ≤ ⊤ from le_top)).op D := by
    simpa only [hj] using hg
  obtain ⟨b, hb⟩ := exists_unit_cartierTrivializationRationalGenerator X D e V g hg'
  have hrg : r = Units.map (X.germToFunctionField V).hom.toMonoidHom b * g⁻¹ := by
    apply Units.ext
    exact hr.trans hb
  have hinv : r⁻¹ = g * Units.map (X.germToFunctionField V).hom.toMonoidHom (b⁻¹) := by
    rw [hrg, mul_inv_rev, inv_inv, map_inv]
  refine ⟨V, le_top, hxV, ?_⟩
  change (cartierDivisorSheaf X).val.map (homOfLE (show V ≤ ⊤ from le_top)).op D =
    (cartierDivisorSheaf X).val.map (homOfLE (show V ≤ ⊤ from le_top)).op
      (cartierEquationClassHom X ⊤ (Additive.ofMul (r⁻¹)))
  rw [cartierEquationClassHom_restrict, hinv,
    cartierEquationClassHom_mul_regular_unit]
  exact hg'.symm

/-- In the actual Picard group, the kernel condition is precisely an
actual principal Cartier divisor witness. -/
theorem cartierPicardClass_eq_one_iff (D : CartierDivisor X) :
    cartierPicardClass X D = 1 ↔
      ∃ f : X.functionFieldˣ, D = principalCartierDivisorHom X (Additive.ofMul f) := by
  constructor
  · intro h
    letI := Scheme.Modules.monoidalCategory X
    have hval : toSkeleton (cartierDivisorModule X D) = (1 : Skeleton X.Modules) :=
      (cartierPicardClass_val X D).symm.trans
        (congrArg (fun c : X.Pic => (c : Skeleton X.Modules)) h)
    rw [Skeleton.one_eq] at hval
    obtain ⟨e⟩ : Nonempty (cartierDivisorModule X D ≅ 𝟙_ X.Modules) := Quotient.exact hval
    exact exists_principalCartierDivisor_of_trivialization X D
      (e ≪≫ PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).symm
  · rintro ⟨f, rfl⟩
    exact cartierPicardClass_principal X f

/-- The kernel of the actual homomorphism is the actual principal-divisor image. -/
theorem cartierPicardHom_ker :
    (cartierPicardHom X).ker = principalCartierDivisors X := by
  apply le_antisymm
  · intro D hD
    apply (mem_principalCartierDivisors_iff X D).mpr
    apply (cartierPicardClass_eq_one_iff X D).mp
    exact congrArg Additive.toMul hD
  · exact principalCartierDivisors_le_cartierPicardHom_ker X

end KltDP.Geometry
