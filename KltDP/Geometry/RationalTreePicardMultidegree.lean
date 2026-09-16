import KltDP.Geometry.RationalTreePicardRationalComponentFrame
import KltDP.Geometry.ProjectiveLinePicardExponent

/-!
# The multidegree homomorphism of a curve with rational components

The manuscript lemma (Picard group of a rational tree) concerns the
multidegree map `Pic(Z) → ℤ^{components}`. This module states that map on
the actual Picard group `X.Pic` of the project: for each original irreducible
component `C` with a given identification `e C` of its reduced closed union
`Z_C` with the projective line, the component degree is the composite of the
existing Picard pullbacks along `Z_C → X` and along `(e C)⁻¹` with the
existing projective-line exponent homomorphism. The multidegree homomorphism
is the product of these over all components.

On the class of an actual line bundle `L`, the component degree is the
component exponent defined in `RationalTreePicardRationalComponentFrame`.
Consequently the kernel statement of the lemma reduces to actual line bundles:
the multidegree homomorphism is injective if and only if every original line
bundle with zero component exponent on all components is trivial. The
identity Picard class is proved to consist exactly of the actually trivial
line bundles, and every Picard class is represented by an actual line bundle.

Nothing here proves injectivity or surjectivity of the multidegree map; both
remain open. The degree notion is the existing transition exponent, whose
comparison with an independently defined divisor degree is a separate
obligation, and the identifications with the projective line are inputs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section PicardClasses

variable {X : Scheme.{u}}

/-- The identity Picard class consists exactly of the actually trivial
invertible sheaves. -/
theorem toPic_eq_one_iff_iso_unit (L : InvertibleSheaf X) :
    L.toPic = 1 ↔ Nonempty (L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) := by
  letI := Scheme.Modules.monoidalCategory X
  constructor
  · intro h
    have h1 : (L.toPic : Skeleton X.Modules) = ((1 : X.Pic) : Skeleton X.Modules) :=
      congrArg (fun p : X.Pic => (p : Skeleton X.Modules)) h
    change (L.toPic : Skeleton X.Modules) = (1 : Skeleton X.Modules) at h1
    rw [InvertibleSheaf.toPic_val L, Skeleton.one_eq] at h1
    obtain ⟨e⟩ := (show Nonempty (L.obj ≅ 𝟙_ X.Modules) from Quotient.exact h1)
    exact ⟨e ≪≫ PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond⟩
  · rintro ⟨e⟩
    apply Units.ext
    change (L.toPic : Skeleton X.Modules) = (1 : Skeleton X.Modules)
    rw [InvertibleSheaf.toPic_val L, Skeleton.one_eq]
    exact Quotient.sound ⟨e ≪≫
      (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).symm⟩

/-- An actual invertible sheaf representing a given Picard class, with local
invertibility derived from the class being a tensor unit. -/
def picardRepresentative (p : X.Pic) : InvertibleSheaf X := by
  letI := Scheme.Modules.monoidalCategory X
  let a : (Skeleton X.Modules)ˣ := p
  let M : X.Modules := (fromSkeleton X.Modules).obj a.val
  have hM : toSkeleton M = a.val := Quotient.out_eq a.val
  exact ⟨M, SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton M (hM.symm ▸ a.isUnit)⟩

/-- The representative has the original class. -/
theorem picardRepresentative_toPic (p : X.Pic) : (picardRepresentative p).toPic = p := by
  letI := Scheme.Modules.monoidalCategory X
  apply Units.ext
  change ((picardRepresentative p).toPic : Skeleton X.Modules) = (p : Skeleton X.Modules)
  rw [InvertibleSheaf.toPic_val]
  exact Quotient.out_eq _

/-- Every actual Picard class is the class of an actual invertible sheaf. -/
theorem toPic_surjective : Function.Surjective (InvertibleSheaf.toPic (X := X)) :=
  fun p => ⟨picardRepresentative p, picardRepresentative_toPic p⟩

end PicardClasses

variable (k : Type u) [Field k] (X : Scheme.{u}) [NoetherianSpace X]

section OneComponent

variable (S : Set ↥(irreducibleComponents X))
  (e : componentUnionScheme X S ≅ projectiveSpace k 1)

/-- The degree of a Picard class on the selected component union, read through
its identification with the projective line: the existing Picard pullbacks
along the closed inclusion and along the inverse identification, followed by
the existing projective-line exponent homomorphism. -/
def componentDegreeHom : X.Pic →* Multiplicative ℤ :=
  (ProjectiveLinePicardExponent.hom k).comp
    ((schemePicardPullbackHom e.inv).comp
      (schemePicardPullbackHom (componentUnionInclusion X S)))

/-- The existing exponent homomorphism evaluates by the existing value. -/
theorem projectiveLineExponentHom_apply (p : (projectiveSpace k 1).Pic) :
    ProjectiveLinePicardExponent.hom k p =
      Multiplicative.ofAdd (ProjectiveLinePicardExponent.value k p) := rfl

/-- On the class of an actual line bundle, the component degree is the
component exponent. -/
theorem componentDegreeHom_toPic (L : InvertibleSheaf X) :
    componentDegreeHom k X S e L.toPic =
      Multiplicative.ofAdd (componentExponent k X S e L) := by
  rw [componentDegreeHom, MonoidHom.comp_apply, MonoidHom.comp_apply,
    schemePicardPullbackHom_toPic (componentUnionInclusion X S) L,
    schemePicardPullbackHom_toPic e.inv, projectiveLineExponentHom_apply,
    ProjectiveLinePicardExponent.value_toPic]
  rfl

/-- Trivial component degree of a line bundle class is exactly an actual
frame on the selected component union. -/
theorem componentDegreeHom_toPic_eq_one_iff (L : InvertibleSheaf X) :
    componentDegreeHom k X S e L.toPic = 1 ↔
      Nonempty ((schemeModulePullback (componentUnionInclusion X S)).obj L.obj ≅
        _root_.SheafOfModules.unit (componentUnionScheme X S).ringCatSheaf) := by
  rw [componentDegreeHom_toPic, ofAdd_eq_one, componentExponent_eq_zero_iff]

end OneComponent

section AllComponents

variable (e : ∀ C : ↥(irreducibleComponents X),
  componentUnionScheme X {C} ≅ projectiveSpace k 1)

/-- The multidegree homomorphism of the manuscript lemma, on the actual
Picard group, for the given identifications of the components with the
projective line. -/
def multidegreeHom : X.Pic →* (↥(irreducibleComponents X) → Multiplicative ℤ) :=
  Pi.monoidHom fun C => componentDegreeHom k X {C} (e C)

@[simp]
theorem multidegreeHom_apply (p : X.Pic) (C : ↥(irreducibleComponents X)) :
    multidegreeHom k X e p C = componentDegreeHom k X {C} (e C) p := rfl

/-- On the class of an actual line bundle, the multidegree is the family of
component exponents. -/
theorem multidegreeHom_toPic (L : InvertibleSheaf X) :
    multidegreeHom k X e L.toPic =
      fun C => Multiplicative.ofAdd (componentExponent k X {C} (e C) L) := by
  funext C
  exact componentDegreeHom_toPic k X {C} (e C) L

/-- Trivial multidegree of a line bundle class means zero component exponent
on every original component. -/
theorem multidegreeHom_toPic_eq_one_iff (L : InvertibleSheaf X) :
    multidegreeHom k X e L.toPic = 1 ↔
      ∀ C : ↥(irreducibleComponents X), componentExponent k X {C} (e C) L = 0 := by
  rw [multidegreeHom_toPic, funext_iff]
  refine forall_congr' fun C => ?_
  show Multiplicative.ofAdd (componentExponent k X {C} (e C) L) = 1 ↔ _
  exact ofAdd_eq_one

/-- The kernel statement of the manuscript lemma, reduced to actual line
bundles: the multidegree homomorphism is injective exactly when every original
line bundle with zero component exponent on all components is trivial. -/
theorem multidegreeHom_injective_iff :
    Function.Injective (multidegreeHom k X e) ↔
      ∀ L : InvertibleSheaf X,
        (∀ C : ↥(irreducibleComponents X), componentExponent k X {C} (e C) L = 0) →
          Nonempty (L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) := by
  rw [injective_iff_map_eq_one]
  constructor
  · intro h L hL
    exact (toPic_eq_one_iff_iso_unit L).mp
      (h L.toPic ((multidegreeHom_toPic_eq_one_iff k X e L).mpr hL))
  · intro h p hp
    obtain ⟨L, rfl⟩ := toPic_surjective p
    exact (toPic_eq_one_iff_iso_unit L).mpr
      (h L ((multidegreeHom_toPic_eq_one_iff k X e L).mp hp))

/-- Surjectivity of the multidegree homomorphism, reduced to actual line
bundles: every prescribed family of component exponents is realized. -/
theorem multidegreeHom_surjective_iff :
    Function.Surjective (multidegreeHom k X e) ↔
      ∀ d : ↥(irreducibleComponents X) → ℤ, ∃ L : InvertibleSheaf X,
        ∀ C : ↥(irreducibleComponents X), componentExponent k X {C} (e C) L = d C := by
  constructor
  · intro h d
    obtain ⟨p, hp⟩ := h (fun C => Multiplicative.ofAdd (d C))
    obtain ⟨L, rfl⟩ := toPic_surjective p
    refine ⟨L, fun C => ?_⟩
    have hC : Multiplicative.ofAdd (componentExponent k X {C} (e C) L) =
        Multiplicative.ofAdd (d C) := by
      simpa only [multidegreeHom_toPic] using congrFun hp C
    exact Multiplicative.ofAdd.injective hC
  · intro h m
    obtain ⟨L, hL⟩ := h (fun C => Multiplicative.toAdd (m C))
    refine ⟨L.toPic, ?_⟩
    rw [multidegreeHom_toPic]
    funext C
    show Multiplicative.ofAdd (componentExponent k X {C} (e C) L) = m C
    rw [hL C]
    rfl

end AllComponents

end KltDP.Geometry.RationalTreePicard
