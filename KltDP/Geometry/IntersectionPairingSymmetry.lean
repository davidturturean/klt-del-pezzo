import KltDP.Geometry.IntersectionPairing
import KltDP.Geometry.MinimalResolutionCount
import KltDP.Geometry.PositivitySurface
import KltDP.Geometry.BlowupExceptionalCurve

/-!
# The intersection matrix is symmetric, and the positivity results in pairing form (F03/F12)

The E6 module `KltDP.Geometry.IntersectionPairing` built a bilinear pairing on Cartier divisors and
on `Pic`, with symmetry (and everything depending on it) conditional on the named hypothesis
`PrimeCurveIntersectionSymmetric`. **That hypothesis is discharged here**, so the pairing is
unconditionally symmetric on a regular surface over an algebraically closed field:

* `notInSupport_of_ne`: for distinct prime curves `C ≠ C'`, `C ⊄ Supp D_{C'}`. The accepted
  `primeCurveCartier_support` identifies `Supp D_{C'}` with `C'`; if the generic point of `C` lay in
  `C'` then `C = closure {η_C} ⊆ C'`, hence `C = C'` by `coe_eq_of_subset_irreducibleCloseds`
  (heights in the order of irreducible closed subsets) together with the accepted
  `PrimeCurve.ne_univ`.
* `primeCurveIntersectionSymmetric`: the diagonal is trivial and the off-diagonal is the accepted
  `intersectionNumber_symm`, so the matrix `(C, C') ↦ C · D_{C'}` is symmetric.
* Unconditional restatements: `intersectionPairing_symm`, `intersectionPairing_primeCurve`,
  `picardPairing_class`, `picardPairing_symm`, `picardPairing_mul_left_of_regular`,
  `picardPairing_mul_right_of_regular`, `selfIntersection_primeCurveClass`.

Positivity in pairing form (the E5 definitions of `KltDP.Geometry.Positivity`):

* `isNef_iff_pairing`: `O_X(D)` is nef iff `0 ≤ D · D_C` for every prime curve `C` (the accepted F03
  degree already matches `subvarietyDegree`, which was `rfl`).
* `nullLocus_eq_of_quantity` generalises the E5 `nullLocus_eq` in the surface quantity: for any
  integer `q` playing the role of `L²` in the bigness criterion, `E(L)` is the closure of the union
  of the degree-zero prime curves together with the whole surface when `q = 0`. Its instance
  `nullLocus_eq_selfIntersection` is the statement with `q = selfIntersection L`, i.e. with `L²`
  given by the bilinear pairing of E6 rather than by the accepted Euler four-term expression.
* `BigOnSurfaceIffSelfIntersectionPos` is the surface half of Keel's Definition-Lemma 0.0 in pairing
  form; it stays a hypothesis (see `laneE/F03_PAIRING_PLAN.md`).

Finally `selfIntersection_exceptional_eq_neg_one` is the pairing form of the E4 result `E·E = −1`
for the accepted glued point blowup: the class `[O_X(E)]` of the exceptional curve has
`selfIntersection = −1`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open KltDP.Geometry KltDP.Geometry.Positivity

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-! ### Discharging the symmetry hypothesis -/

/-- **Distinct prime curves are not contained in one another**, in the form needed by the accepted
`intersectionNumber_symm`: the generic point of `C` is off the support of `D_{C'}`. -/
theorem notInSupport_of_ne {C C' : X.PrimeCurve} (h : C ≠ C') :
    C.NotInSupport (X.primeCurveCartier hregular C')
      (X.primeCurveCartier_hasRegularEquations hregular C') := by
  intro hmem
  apply h
  apply PrimeCurve.ext
  have hmem' : C.genericPoint ∈ (C' : Set X.toScheme) := by
    have hsupp := X.primeCurveCartier_support hregular C'
    have : C.genericPoint ∈
        ((effectiveCartierIdealDataOfRegularEquations X.toScheme
          (X.primeCurveCartier hregular C')
          (X.primeCurveCartier_hasRegularEquations hregular C')).support :
            Set X.toScheme) := hmem
    rwa [hsupp] at this
  have hsub : (C : Set X.toScheme) ⊆ (C' : Set X.toScheme) := by
    rw [← C.closure_genericPoint]
    exact closure_minimal (Set.singleton_subset_iff.mpr hmem') C'.isClosed
  exact C.coe_eq_of_subset_irreducibleCloseds C'.1 hsub C'.ne_univ

/-- **The prime-curve intersection matrix is symmetric** (the E6 named hypothesis, discharged). -/
theorem primeCurveIntersectionSymmetric :
    PrimeCurveIntersectionSymmetric X hregular := by
  intro C C'
  rcases eq_or_ne C C' with rfl | h
  · rfl
  · exact X.primeCurveIntersectionSymmetric_of_notInSupport hregular C C'
      (X.notInSupport_of_ne hregular h) (X.notInSupport_of_ne hregular h.symm)

/-! ### The pairing, unconditionally -/

/-- **Symmetry of the intersection pairing**, unconditionally. -/
theorem intersectionPairing_symm (D₁ D₂ : CartierDivisor X.toScheme) :
    intersectionPairing X hregular D₁ D₂ = intersectionPairing X hregular D₂ D₁ :=
  X.intersectionPairing_comm hregular (X.primeCurveIntersectionSymmetric hregular) D₁ D₂

/-- **`D · D_C = intersectionNumber C D`**, unconditionally. -/
theorem intersectionPairing_primeCurve (D : CartierDivisor X.toScheme) (C : X.PrimeCurve) :
    intersectionPairing X hregular D (X.primeCurveCartier hregular C) = C.intersectionNumber D :=
  X.intersectionPairing_primeCurveCartier hregular (X.primeCurveIntersectionSymmetric hregular) D C

/-- **The Picard pairing of two divisor classes**, unconditionally. -/
theorem picardPairing_class (D E : CartierDivisor X.toScheme) :
    picardPairing X hregular (cartierPicardClass X.toScheme D)
        (cartierPicardClass X.toScheme E) = intersectionPairing X hregular D E :=
  X.picardPairing_cartierPicardClass hregular (X.primeCurveIntersectionSymmetric hregular) D E

/-- **Symmetry of the Picard pairing**, unconditionally. -/
theorem picardPairing_symm (p q : X.toScheme.Pic) :
    picardPairing X hregular p q = picardPairing X hregular q p :=
  X.picardPairing_comm hregular (X.primeCurveIntersectionSymmetric hregular) p q

/-- **Bilinearity of the Picard pairing**, unconditionally. -/
theorem picardPairing_mul_left_of_regular (p p' q : X.toScheme.Pic) :
    picardPairing X hregular (p * p') q =
      picardPairing X hregular p q + picardPairing X hregular p' q :=
  X.picardPairing_mul_left hregular (X.primeCurveIntersectionSymmetric hregular) p p' q

theorem picardPairing_mul_right_of_regular (p q q' : X.toScheme.Pic) :
    picardPairing X hregular p (q * q') =
      picardPairing X hregular p q + picardPairing X hregular p q' :=
  X.picardPairing_mul_right hregular (X.primeCurveIntersectionSymmetric hregular) p q q'

/-- **`L² = C·C` for the class of a prime-curve divisor**, unconditionally: the accepted
`selfIntersectionNumber`. -/
theorem selfIntersection_primeCurveClass (C : X.PrimeCurve) :
    selfIntersection X hregular
        (cartierDivisorInvertibleSheaf X.toScheme (X.primeCurveCartier hregular C)) =
      C.selfIntersectionNumber hregular :=
  X.selfIntersection_cartierDivisorInvertibleSheaf_primeCurve hregular
    (X.primeCurveIntersectionSymmetric hregular) C

/-! ### Positivity in pairing form -/

/-- **Nef in pairing form**: `O_X(D)` is nef iff it pairs nonnegatively with every prime curve. -/
theorem isNef_iff_pairing (D : CartierDivisor X.toScheme) :
    IsNef X.structureMorphism (cartierDivisorInvertibleSheaf X.toScheme D) ↔
      ∀ C : X.PrimeCurve, 0 ≤ intersectionPairing X hregular D
        (X.primeCurveCartier hregular C) := by
  rw [isNef_iff_forall_primeCurve X (cartierDivisorInvertibleSheaf X.toScheme D)]
  refine forall_congr' fun C => ?_
  rw [X.intersectionPairing_primeCurve hregular D C,
    C.intersectionNumber_eq_restrictionDegree D]

/-- The surface half of Keel's Definition-Lemma 0.0 in pairing form: on the whole surface, `L` is
big exactly when `L² > 0`. A hypothesis (Riemann–Roch input), never assumed. -/
def BigOnSurfaceIffSelfIntersectionPos (L : InvertibleSheaf X.toScheme) : Prop :=
  ∀ Z : IrreducibleCloseds X.toScheme, (Z : Set X.toScheme) = Set.univ →
    (IsBig (Positivity.inclusion Z ≫ X.structureMorphism)
        (pullbackInvertibleSheaf (Positivity.inclusion Z) L) ↔
      0 < selfIntersection X hregular L)

section NullLocus

variable (L : InvertibleSheaf X.toScheme) (q : ℤ)

/-- **Keel's exceptional subvarieties on a surface**, with the surface quantity kept abstract. -/
theorem isExceptionalSubvariety_iff_of_quantity
    (hdim : ∀ Z : IrreducibleCloseds X.toScheme, 0 < topologicalKrullDim (Z : Set X.toScheme) →
      topologicalKrullDim (Z : Set X.toScheme) = 1 ∨ (Z : Set X.toScheme) = Set.univ)
    (hpos : ∀ Z : IrreducibleCloseds X.toScheme, topologicalKrullDim (Z : Set X.toScheme) = 1 ∨
      (Z : Set X.toScheme) = Set.univ → 0 < topologicalKrullDim (Z : Set X.toScheme))
    (hcurve : ∀ Z : IrreducibleCloseds X.toScheme, topologicalKrullDim (Z : Set X.toScheme) = 1 →
      (IsBig (Positivity.inclusion Z ≫ X.structureMorphism)
          (pullbackInvertibleSheaf (Positivity.inclusion Z) L) ↔
        0 < subvarietyDegree X.structureMorphism L Z))
    (hsurface : ∀ Z : IrreducibleCloseds X.toScheme, (Z : Set X.toScheme) = Set.univ →
      (IsBig (Positivity.inclusion Z ≫ X.structureMorphism)
          (pullbackInvertibleSheaf (Positivity.inclusion Z) L) ↔ 0 < q))
    (Z : IrreducibleCloseds X.toScheme) :
    IsExceptionalSubvariety X.structureMorphism L Z ↔
      ((topologicalKrullDim (Z : Set X.toScheme) = 1 ∧
          subvarietyDegree X.structureMorphism L Z ≤ 0) ∨
        ((Z : Set X.toScheme) = Set.univ ∧ q ≤ 0)) := by
  constructor
  · rintro ⟨hZpos, hZbig⟩
    rcases hdim Z hZpos with h1 | h2
    · exact Or.inl ⟨h1, not_lt.mp fun hlt => hZbig ((hcurve Z h1).mpr hlt)⟩
    · exact Or.inr ⟨h2, not_lt.mp fun hlt => hZbig ((hsurface Z h2).mpr hlt)⟩
  · rintro (⟨h1, hdeg⟩ | ⟨h2, hq⟩)
    · exact ⟨hpos Z (Or.inl h1), fun hbig => absurd ((hcurve Z h1).mp hbig) (not_lt.mpr hdeg)⟩
    · exact ⟨hpos Z (Or.inr h2), fun hbig => absurd ((hsurface Z h2).mp hbig) (not_lt.mpr hq)⟩

/-- **The exceptional locus of a nef bundle on a surface**, with the surface quantity kept abstract:
the closure of the union of the prime curves of degree zero, together with the whole surface when
`q = 0`. -/
theorem nullLocus_eq_of_quantity
    (hdim : ∀ Z : IrreducibleCloseds X.toScheme, 0 < topologicalKrullDim (Z : Set X.toScheme) →
      topologicalKrullDim (Z : Set X.toScheme) = 1 ∨ (Z : Set X.toScheme) = Set.univ)
    (hpos : ∀ Z : IrreducibleCloseds X.toScheme, topologicalKrullDim (Z : Set X.toScheme) = 1 ∨
      (Z : Set X.toScheme) = Set.univ → 0 < topologicalKrullDim (Z : Set X.toScheme))
    (hcurve : ∀ Z : IrreducibleCloseds X.toScheme, topologicalKrullDim (Z : Set X.toScheme) = 1 →
      (IsBig (Positivity.inclusion Z ≫ X.structureMorphism)
          (pullbackInvertibleSheaf (Positivity.inclusion Z) L) ↔
        0 < subvarietyDegree X.structureMorphism L Z))
    (hsurface : ∀ Z : IrreducibleCloseds X.toScheme, (Z : Set X.toScheme) = Set.univ →
      (IsBig (Positivity.inclusion Z ≫ X.structureMorphism)
          (pullbackInvertibleSheaf (Positivity.inclusion Z) L) ↔ 0 < q))
    (hnef : IsNef X.structureMorphism L) (hq : 0 ≤ q) :
    nullLocus X.structureMorphism L =
      closure ((⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme)) ∪
        ⋃ (_ : q = 0), (Set.univ : Set X.toScheme)) := by
  have hAB : (⋃ Z ∈ {Z : IrreducibleCloseds X.toScheme |
        IsExceptionalSubvariety X.structureMorphism L Z}, (Z : Set X.toScheme)) =
      ((⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme)) ∪
        ⋃ (_ : q = 0), (Set.univ : Set X.toScheme)) := by
    apply Set.Subset.antisymm
    · refine Set.iUnion₂_subset fun Z hZ => ?_
      rcases (X.isExceptionalSubvariety_iff_of_quantity L q hdim hpos hcurve hsurface
        Z).mp hZ with ⟨h1, hdeg⟩ | ⟨h2, hqle⟩
      · refine Set.subset_union_of_subset_left ?_ _
        refine Set.subset_biUnion_of_mem (u := fun C : X.PrimeCurve => (C : Set X.toScheme))
          (show (⟨Z, h1⟩ : X.PrimeCurve) ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0} from ?_)
        exact le_antisymm hdeg (hnef Z h1)
      · refine Set.subset_union_of_subset_right ?_ _
        rw [h2]
        exact Set.subset_iUnion (fun _ : q = 0 => (Set.univ : Set X.toScheme))
          (le_antisymm hqle hq)
    · refine Set.union_subset (Set.iUnion₂_subset fun C hC => ?_) (Set.iUnion_subset fun h0 => ?_)
      · refine Set.subset_biUnion_of_mem
          (u := fun Z : IrreducibleCloseds X.toScheme => (Z : Set X.toScheme))
          (show C.1 ∈ {Z : IrreducibleCloseds X.toScheme |
            IsExceptionalSubvariety X.structureMorphism L Z} from ?_)
        exact (X.isExceptionalSubvariety_iff_of_quantity L q hdim hpos hcurve hsurface
          C.1).mpr (Or.inl ⟨C.2, le_of_eq hC⟩)
      · refine Set.subset_biUnion_of_mem
          (u := fun Z : IrreducibleCloseds X.toScheme => (Z : Set X.toScheme))
          (show (⟨Set.univ, IrreducibleSpace.isIrreducible_univ X.toScheme, isClosed_univ⟩ :
              IrreducibleCloseds X.toScheme) ∈
            {Z : IrreducibleCloseds X.toScheme |
              IsExceptionalSubvariety X.structureMorphism L Z} from ?_)
        exact (X.isExceptionalSubvariety_iff_of_quantity L q hdim hpos hcurve hsurface
          _).mpr (Or.inr ⟨rfl, le_of_eq h0⟩)
  unfold nullLocus
  rw [hAB]

end NullLocus

/-- **The exceptional locus with `L²` given by the bilinear pairing**: the E5 statement with the
E6 `selfIntersection` in place of the accepted Euler four-term expression. -/
theorem nullLocus_eq_selfIntersection (L : InvertibleSheaf X.toScheme)
    (hdim : ∀ Z : IrreducibleCloseds X.toScheme, 0 < topologicalKrullDim (Z : Set X.toScheme) →
      topologicalKrullDim (Z : Set X.toScheme) = 1 ∨ (Z : Set X.toScheme) = Set.univ)
    (hpos : ∀ Z : IrreducibleCloseds X.toScheme, topologicalKrullDim (Z : Set X.toScheme) = 1 ∨
      (Z : Set X.toScheme) = Set.univ → 0 < topologicalKrullDim (Z : Set X.toScheme))
    (hcurve : ∀ Z : IrreducibleCloseds X.toScheme, topologicalKrullDim (Z : Set X.toScheme) = 1 →
      (IsBig (Positivity.inclusion Z ≫ X.structureMorphism)
          (pullbackInvertibleSheaf (Positivity.inclusion Z) L) ↔
        0 < subvarietyDegree X.structureMorphism L Z))
    (hsurface : BigOnSurfaceIffSelfIntersectionPos X hregular L)
    (hnef : IsNef X.structureMorphism L) (hq : 0 ≤ selfIntersection X hregular L) :
    nullLocus X.structureMorphism L =
      closure ((⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme)) ∪
        ⋃ (_ : selfIntersection X hregular L = 0), (Set.univ : Set X.toScheme)) :=
  X.nullLocus_eq_of_quantity L (selfIntersection X hregular L) hdim hpos hcurve
    hsurface hnef hq

end KltDP.Geometry.NormalProjectiveSurface

/-! ### The pairing form of `E·E = −1` for the accepted point blowup -/

namespace KltDP.Geometry.BlowupExceptional

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface KltDP.Literature.Stacks

universe v

variable {k : Type v} [Field k] [IsAlgClosed k]

/-- **The exceptional class of a point blowup has self-intersection `−1` in the bilinear pairing**
(the pairing form of the E4 result, for lanes A2 and F). -/
theorem selfIntersection_exceptional_eq_neg_one (hA : BlowupRegularPointLiteral k)
    {S S' : NormalProjectiveSurface k} (b : S.toScheme ⟶ S'.toScheme) (x' : S'.Point)
    (hb : IsPointBlowupAt S S' b x') (hreg' : ∀ y : S'.Point, RegularPoint S'.toScheme y)
    (hreg : ∀ y : S.Point, RegularPoint S.toScheme y) :
    ∃ E : S.PrimeCurve,
      selfIntersection S hreg
          (cartierDivisorInvertibleSheaf S.toScheme (S.primeCurveCartier hreg E)) = -1 ∧
        b.base '' (E : Set S.toScheme) = {x'} := by
  obtain ⟨E, hminus, himg⟩ := exists_minusOne_of_literal hA b x' hb hreg' hreg
  refine ⟨E, ?_, himg⟩
  rw [S.selfIntersection_primeCurveClass hreg E]
  exact hminus.selfIntersection

end KltDP.Geometry.BlowupExceptional
