import KltDP.Geometry.PrimeCurveIntersectionFinite
import KltDP.Geometry.PrimeCurvePairingSupport

/-!
# Pairing at most one gives at most one actual intersection point

Every point of the finite intersection scheme has a nontrivial ring of
sections on its open singleton: its germ maps to the nontrivial local ring.
The existing decomposition of global sections gives finite dimensionality
of each singleton summand. Thus each original point contributes at least
one to the actual intersection degree. A degree bound by one gives a
subsingleton intersection scheme, and hence a subsingleton intersection of
the original prime-curve carriers. No regularity of the curves is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}
  (C : X.PrimeCurve) (D : CartierDivisor X.toScheme)
  (hD : HasRegularCartierEquations X.toScheme D) (hC : C.NotInSupport D hD)

/-- The number of actual points of the intersection scheme is bounded by
the intersection degree. Its finiteness is supplied by the actual curve. -/
theorem intersectionScheme_card_le_intersectionDegree :
    Nat.card (C.intersectionScheme D hD hC) ≤ C.intersectionDegree D hD hC := by
  classical
  let Z := C.intersectionScheme D hD hC
  let f := C.intersectionToSpec D hD hC
  letI : Finite Z := C.intersectionScheme_finite' D hD hC
  letI : Fintype Z := Fintype.ofFinite Z
  letI : DiscreteTopology Z := DiscreteTopology.of_finite_of_isClosed_singleton
    (C.intersectionScheme_isClosed_singleton' D hD hC)
  let φ : k →+* Γ(Z, ⊤) := baseFieldToGlobalSections f
  letI := Module.compHom Γ(Z, ⊤) φ
  letI : ∀ z : Z, Module k Γ(Z, singletonOpen Z z) := fun z =>
    sectionsBaseModule Z φ (singletonOpen Z z)
  haveI : Module.Finite k Γ(Z, ⊤) :=
    finite_sections_of_hZero f (C.intersectionDegree_finiteDimensional D hD hC)
  let e := sectionsPiLinearEquiv Z (singletonOpen Z) φ
    (singletonOpen_iSup Z) (singletonOpen_disjoint Z)
  letI : ∀ z : Z, Nonempty Γ(Z, singletonOpen Z z) := fun z =>
    ⟨(0 : Γ(Z, singletonOpen Z z))⟩
  haveI : ∀ z : Z, Module.Finite k Γ(Z, singletonOpen Z z) := fun z =>
    Module.Finite.of_surjective ((LinearMap.proj z).comp e.toLinearMap)
      ((Function.surjective_eval z).comp e.surjective)
  have hpos (z : Z) : 0 < Module.finrank k Γ(Z, singletonOpen Z z) := by
    haveI : Nontrivial Γ(Z, singletonOpen Z z) :=
      (Z.presheaf.germ (singletonOpen Z z) z (Set.mem_singleton z)).hom.domain_nontrivial
    exact Module.finrank_pos
  have hsum : C.intersectionDegree D hD hC =
      ∑ z : Z, Module.finrank k Γ(Z, singletonOpen Z z) :=
    C.intersectionDegree_eq_sum_points D hD hC
      (C.intersectionScheme_isClosed_singleton' D hD hC)
  rw [hsum]
  calc
    Nat.card Z = ∑ _z : Z, (1 : ℕ) := by simp [Nat.card_eq_fintype_card]
    _ ≤ _ := Finset.sum_le_sum (fun z _ => hpos z)

/-- A degree bound by one makes the actual intersection scheme a
subsingleton. Finiteness is proved before applying the cardinality bound. -/
theorem intersectionScheme_subsingleton_of_degree_le_one
    (hle : C.intersectionDegree D hD hC ≤ 1) :
    Subsingleton (C.intersectionScheme D hD hC) := by
  letI : Finite (C.intersectionScheme D hD hC) := C.intersectionScheme_finite' D hD hC
  letI : Fintype (C.intersectionScheme D hD hC) := Fintype.ofFinite _
  apply Fintype.card_le_one_iff_subsingleton.mp
  rw [← Nat.card_eq_fintype_card]
  exact (C.intersectionScheme_card_le_intersectionDegree D hD hC).trans hle

/-- The original curve and effective Cartier support meet in at most one
point whenever their actual intersection degree is at most one. -/
theorem inter_support_subsingleton_of_degree_le_one
    (hle : C.intersectionDegree D hD hC ≤ 1) :
    ((C : Set X.toScheme) ∩
      ((effectiveCartierIdealDataOfRegularEquations X.toScheme D hD).support :
        Set X.toScheme)).Subsingleton := by
  letI := C.intersectionScheme_subsingleton_of_degree_le_one D hD hC hle
  rw [← C.range_intersectionToSurface D hD hC]
  rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
  exact congrArg (C.intersectionToSurface D hD hC).base (Subsingleton.elim a b)

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

namespace KltDP.Geometry.PrimeCurvePairingSupport

open KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) (C D : X.PrimeCurve)

/-- Two distinct prime curves whose actual Cartier pairing is at most one
meet in at most one original surface point. No smoothness of the curves is
required. -/
theorem intersectionPairing_primeCurves_le_one_inter_subsingleton
    (hCD : C ≠ D)
    (hle : intersectionPairing X hregular (X.primeCurveCartier hregular C)
      (X.primeCurveCartier hregular D) ≤ 1) :
    ((C : Set X.toScheme) ∩ (D : Set X.toScheme)).Subsingleton := by
  have hdegree : C.intersectionDegree (X.primeCurveCartier hregular D)
      (X.primeCurveCartier_hasRegularEquations hregular D)
      (X.notInSupport_of_ne hregular hCD) ≤ 1 := by
    rw [intersectionPairing_primeCurves_eq_intersectionNumber X hregular C D,
      C.intersectionNumber_eq_intersectionDegree (X.primeCurveCartier hregular D)
        (X.primeCurveCartier_hasRegularEquations hregular D)
        (X.notInSupport_of_ne hregular hCD)] at hle
    exact_mod_cast hle
  simpa only [X.primeCurveCartier_support hregular D] using
    C.inter_support_subsingleton_of_degree_le_one (X.primeCurveCartier hregular D)
      (X.primeCurveCartier_hasRegularEquations hregular D)
      (X.notInSupport_of_ne hregular hCD) hdegree

end KltDP.Geometry.PrimeCurvePairingSupport

#print axioms KltDP.Geometry.NormalProjectiveSurface.PrimeCurve.intersectionScheme_card_le_intersectionDegree
#print axioms KltDP.Geometry.NormalProjectiveSurface.PrimeCurve.intersectionScheme_subsingleton_of_degree_le_one
#print axioms KltDP.Geometry.NormalProjectiveSurface.PrimeCurve.inter_support_subsingleton_of_degree_le_one
#print axioms KltDP.Geometry.PrimeCurvePairingSupport.intersectionPairing_primeCurves_le_one_inter_subsingleton
