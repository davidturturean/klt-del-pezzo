import KltDP.Geometry.Positivity

/-!
# The exceptional locus of a nef bundle on a surface (F12)

Keel's `E(L)` (Definition 0.1) is defined for arbitrary positive-dimensional subvarieties. On a
projective surface the positive-dimensional subvarieties are the prime curves and the surface
itself, so `E(L)` is the closure of the union of the prime curves of degree zero, together with the
whole surface when `L² = 0` (Keel's own remark after Definition 0.1: "Of course if `L` is not big
(and `X` is irreducible), `E(L) = X`").

The three inputs are named hypotheses, not literature literals:

* `hdim`: every positive-dimensional irreducible closed subset of the surface is a prime curve or
  the whole surface (dimension theory of a two-dimensional scheme; not in the accepted tree);
* `hcurve`: on a one-dimensional subvariety, `L` is big iff its degree is positive (Keel's
  Definition-Lemma 0.0 in dimension one, i.e. Riemann–Roch on a curve);
* `hsurface`: on the whole surface, `L` is big iff `L² > 0` (Keel's Definition-Lemma 0.0 in
  dimension two, with the accepted Euler-characteristic pairing `picardEulerPairing` as `L²`).

`isExceptionalSubvariety_iff` is the characterisation of the exceptional subvarieties; `nullLocus_eq`
rewrites `E(L)` as the closure of the union of the degree-zero prime curves together with the whole
surface in the `L² = 0` case. The comparison of `picardEulerPairing` with the accepted
`intersectionNumber` is an open F03 debt (recorded in the accepted `CartierEulerPairing` docstring),
so `L²` here is the Euler pairing, not the intersection number.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.Positivity

open KltDP.Geometry KltDP.Geometry.ModuleCohomology KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k) (L : InvertibleSheaf X.toScheme)

/-- **Keel's exceptional subvarieties on a surface.** -/
theorem isExceptionalSubvariety_iff
    (hdim : ∀ Z : IrreducibleCloseds X.toScheme, 0 < topologicalKrullDim (Z : Set X.toScheme) →
      topologicalKrullDim (Z : Set X.toScheme) = 1 ∨ (Z : Set X.toScheme) = Set.univ)
    (hpos : ∀ Z : IrreducibleCloseds X.toScheme, topologicalKrullDim (Z : Set X.toScheme) = 1 ∨
      (Z : Set X.toScheme) = Set.univ → 0 < topologicalKrullDim (Z : Set X.toScheme))
    (hcurve : ∀ Z : IrreducibleCloseds X.toScheme, topologicalKrullDim (Z : Set X.toScheme) = 1 →
      (IsBig (inclusion Z ≫ X.structureMorphism)
          (pullbackInvertibleSheaf (inclusion Z) L) ↔
        0 < subvarietyDegree X.structureMorphism L Z))
    (hsurface : ∀ Z : IrreducibleCloseds X.toScheme, (Z : Set X.toScheme) = Set.univ →
      (IsBig (inclusion Z ≫ X.structureMorphism)
          (pullbackInvertibleSheaf (inclusion Z) L) ↔
        0 < X.picardEulerPairing L.toPic L.toPic))
    (Z : IrreducibleCloseds X.toScheme) :
    IsExceptionalSubvariety X.structureMorphism L Z ↔
      ((topologicalKrullDim (Z : Set X.toScheme) = 1 ∧
          subvarietyDegree X.structureMorphism L Z ≤ 0) ∨
        ((Z : Set X.toScheme) = Set.univ ∧ X.picardEulerPairing L.toPic L.toPic ≤ 0)) := by
  constructor
  · rintro ⟨hZpos, hZbig⟩
    rcases hdim Z hZpos with h1 | h2
    · exact Or.inl ⟨h1, not_lt.mp fun hlt => hZbig ((hcurve Z h1).mpr hlt)⟩
    · exact Or.inr ⟨h2, not_lt.mp fun hlt => hZbig ((hsurface Z h2).mpr hlt)⟩
  · rintro (⟨h1, hdeg⟩ | ⟨h2, hsq⟩)
    · exact ⟨hpos Z (Or.inl h1), fun hbig => absurd ((hcurve Z h1).mp hbig) (not_lt.mpr hdeg)⟩
    · exact ⟨hpos Z (Or.inr h2), fun hbig => absurd ((hsurface Z h2).mp hbig) (not_lt.mpr hsq)⟩

/-- **The exceptional locus of a nef bundle on a surface**: the closure of the union of the prime
curves of degree zero, together with the whole surface when `L² = 0`. Nefness enters through
`hnef`, which turns "degree `≤ 0`" into "degree `= 0`" on curves, and `hsq` likewise on the
surface. -/
theorem nullLocus_eq
    (hdim : ∀ Z : IrreducibleCloseds X.toScheme, 0 < topologicalKrullDim (Z : Set X.toScheme) →
      topologicalKrullDim (Z : Set X.toScheme) = 1 ∨ (Z : Set X.toScheme) = Set.univ)
    (hpos : ∀ Z : IrreducibleCloseds X.toScheme, topologicalKrullDim (Z : Set X.toScheme) = 1 ∨
      (Z : Set X.toScheme) = Set.univ → 0 < topologicalKrullDim (Z : Set X.toScheme))
    (hcurve : ∀ Z : IrreducibleCloseds X.toScheme, topologicalKrullDim (Z : Set X.toScheme) = 1 →
      (IsBig (inclusion Z ≫ X.structureMorphism)
          (pullbackInvertibleSheaf (inclusion Z) L) ↔
        0 < subvarietyDegree X.structureMorphism L Z))
    (hsurface : ∀ Z : IrreducibleCloseds X.toScheme, (Z : Set X.toScheme) = Set.univ →
      (IsBig (inclusion Z ≫ X.structureMorphism)
          (pullbackInvertibleSheaf (inclusion Z) L) ↔
        0 < X.picardEulerPairing L.toPic L.toPic))
    (hnef : IsNef X.structureMorphism L)
    (hsq : 0 ≤ X.picardEulerPairing L.toPic L.toPic) :
    nullLocus X.structureMorphism L =
      closure ((⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme)) ∪
        ⋃ (_ : X.picardEulerPairing L.toPic L.toPic = 0), (Set.univ : Set X.toScheme)) := by
  have hAB : (⋃ Z ∈ {Z : IrreducibleCloseds X.toScheme |
        IsExceptionalSubvariety X.structureMorphism L Z}, (Z : Set X.toScheme)) =
      ((⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme)) ∪
        ⋃ (_ : X.picardEulerPairing L.toPic L.toPic = 0), (Set.univ : Set X.toScheme)) := by
    apply Set.Subset.antisymm
    · refine Set.iUnion₂_subset fun Z hZ => ?_
      rcases (isExceptionalSubvariety_iff X L hdim hpos hcurve hsurface Z).mp hZ with
        ⟨h1, hdeg⟩ | ⟨h2, hsqle⟩
      · refine Set.subset_union_of_subset_left ?_ _
        refine Set.subset_biUnion_of_mem (u := fun C : X.PrimeCurve => (C : Set X.toScheme))
          (show (⟨Z, h1⟩ : X.PrimeCurve) ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0} from ?_)
        exact le_antisymm hdeg (hnef Z h1)
      · refine Set.subset_union_of_subset_right ?_ _
        rw [h2]
        exact Set.subset_iUnion (fun _ : X.picardEulerPairing L.toPic L.toPic = 0 =>
          (Set.univ : Set X.toScheme)) (le_antisymm hsqle hsq)
    · refine Set.union_subset (Set.iUnion₂_subset fun C hC => ?_) (Set.iUnion_subset fun h0 => ?_)
      · refine Set.subset_biUnion_of_mem
          (u := fun Z : IrreducibleCloseds X.toScheme => (Z : Set X.toScheme))
          (show C.1 ∈ {Z : IrreducibleCloseds X.toScheme |
            IsExceptionalSubvariety X.structureMorphism L Z} from ?_)
        exact (isExceptionalSubvariety_iff X L hdim hpos hcurve hsurface C.1).mpr
          (Or.inl ⟨C.2, le_of_eq hC⟩)
      · refine Set.subset_biUnion_of_mem
          (u := fun Z : IrreducibleCloseds X.toScheme => (Z : Set X.toScheme))
          (show (⟨Set.univ, IrreducibleSpace.isIrreducible_univ X.toScheme, isClosed_univ⟩ :
              IrreducibleCloseds X.toScheme) ∈
            {Z : IrreducibleCloseds X.toScheme |
              IsExceptionalSubvariety X.structureMorphism L Z} from ?_)
        exact (isExceptionalSubvariety_iff X L hdim hpos hcurve hsurface _).mpr
          (Or.inr ⟨rfl, le_of_eq h0⟩)
  unfold nullLocus
  rw [hAB]

end KltDP.Geometry.Positivity
