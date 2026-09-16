import KltDP.Geometry.RationalTreePicardTwoBranches

/-!
# Transverse germs on the complement of a leaf: reduction to the stalk transfer off the leaf

BRIEF12, task (c) in reduced form. By `image_intersectionPoint_not_mem` (task (a)), every node of
`Z_{Cᶜ}` maps to a point of `Y` off the leaf component `C`, on the two original components
carrying the two components of `Z_{Cᶜ}` through it. Hence the transverse germs of `Y` at that
point (for the component `componentImage D'`) are available on every affine open, and the only
remaining step is their transfer along the closed immersion `ι_{Cᶜ}` at a point off `C`, where
`ι_{Cᶜ}` is a local isomorphism: `TransversePointTransfer Y C`. With it,
`hasTransverseComponentBranches_compl_of_transfer` gives the transverse germs on `Z_{Cᶜ}`,
`inheritsTransverseBranches_of_transfer` gives `InheritsTransverseBranches`, and the kernel
statement of `lem:tree-picard` is exported with this single stalk-level hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.RationalTreePicard

section Transfer

variable (Y : Scheme.{u}) [NoetherianSpace Y] (C : ↥(irreducibleComponents Y))

/-- The stalk-level transfer of the transverse data along `ι_{Cᶜ}` at a point of `Z_{Cᶜ}` mapping
off the leaf component: the four germ conditions of `Y` at the image point (for the original
component carrying `D'`, on every affine open) give the four germ conditions of `Z_{Cᶜ}` at the
point (for `D'`, on every affine open). -/
def TransversePointTransfer : Prop :=
  ∀ (D' : ↥(irreducibleComponents (componentUnionScheme Y ({C}ᶜ))))
    (z : componentUnionScheme Y ({C}ᶜ)),
    (componentUnionInclusion Y ({C}ᶜ)).base z ∉ C.1 →
    (∀ (U : Y.affineOpens) (hx : (componentUnionInclusion Y ({C}ᶜ)).base z ∈ U.1),
      ∃ w : Fin 2 → maximalIdeal (Y.presheaf.stalk ((componentUnionInclusion Y ({C}ᶜ)).base z)),
        (w 0 : Y.presheaf.stalk ((componentUnionInclusion Y ({C}ᶜ)).base z)) ∈
            (componentChartIdeal Y {componentImage Y ({C}ᶜ) D'} U).map
              (Y.presheaf.germ U.1 ((componentUnionInclusion Y ({C}ᶜ)).base z) hx).hom ∧
        (w 1 : Y.presheaf.stalk ((componentUnionInclusion Y ({C}ᶜ)).base z)) ∈
            (componentChartIdeal Y ({componentImage Y ({C}ᶜ) D'}ᶜ) U).map
              (Y.presheaf.germ U.1 ((componentUnionInclusion Y ({C}ᶜ)).base z) hx).hom ∧
        Module.finrank (ResidueField (Y.presheaf.stalk ((componentUnionInclusion Y ({C}ᶜ)).base z)))
            (CotangentSpace (Y.presheaf.stalk ((componentUnionInclusion Y ({C}ᶜ)).base z))) = 2 ∧
        LinearIndependent
            (ResidueField (Y.presheaf.stalk ((componentUnionInclusion Y ({C}ᶜ)).base z)))
            (fun i => (maximalIdeal
              (Y.presheaf.stalk ((componentUnionInclusion Y ({C}ᶜ)).base z))).toCotangent (w i))) →
    ∀ (V : (componentUnionScheme Y ({C}ᶜ)).affineOpens) (hz : z ∈ V.1),
      ∃ w : Fin 2 → maximalIdeal ((componentUnionScheme Y ({C}ᶜ)).presheaf.stalk z),
        (w 0 : (componentUnionScheme Y ({C}ᶜ)).presheaf.stalk z) ∈
            (componentChartIdeal (componentUnionScheme Y ({C}ᶜ)) {D'} V).map
              ((componentUnionScheme Y ({C}ᶜ)).presheaf.germ V.1 z hz).hom ∧
        (w 1 : (componentUnionScheme Y ({C}ᶜ)).presheaf.stalk z) ∈
            (componentChartIdeal (componentUnionScheme Y ({C}ᶜ)) ({D'}ᶜ) V).map
              ((componentUnionScheme Y ({C}ᶜ)).presheaf.germ V.1 z hz).hom ∧
        Module.finrank (ResidueField ((componentUnionScheme Y ({C}ᶜ)).presheaf.stalk z))
            (CotangentSpace ((componentUnionScheme Y ({C}ᶜ)).presheaf.stalk z)) = 2 ∧
        LinearIndependent (ResidueField ((componentUnionScheme Y ({C}ᶜ)).presheaf.stalk z))
            (fun i => (maximalIdeal ((componentUnionScheme Y ({C}ᶜ)).presheaf.stalk z)).toCotangent
              (w i))

variable {Y C}

/-- The transverse germs on the complement of a leaf, from those of `Y` and the stalk transfer off
the leaf. -/
theorem hasTransverseComponentBranches_compl_of_transfer [IsLocallyNoetherian Y]
    (htransY : HasTransverseComponentBranches Y) (htransfer : TransversePointTransfer Y C) :
    HasTransverseComponentBranches (componentUnionScheme Y ({C}ᶜ)) := by
  intro D' z hzD hzc V hz
  obtain ⟨D'', hD'', hzD''⟩ := (mem_componentClosedUnion (componentUnionScheme Y ({C}ᶜ)) _ z).mp hzc
  have hne : D'' ≠ D' := fun h => hD'' (by rw [h]; exact Set.mem_singleton D')
  have hzint : z ∈ componentIntersectionPoints (componentUnionScheme Y ({C}ᶜ)) :=
    ⟨D', D'', hne.symm, hzD, hzD''⟩
  have hxC : (componentUnionInclusion Y ({C}ᶜ)).base z ∉ C.1 :=
    image_intersectionPoint_not_mem htransY C ⟨z, hzint⟩
  refine htransfer D' z hxC (fun U hx => htransY (componentImage Y ({C}ᶜ) D') _ ?_ ?_ U hx) V hz
  · rw [← image_componentImage]
    exact ⟨z, hzD, rfl⟩
  · refine (mem_componentClosedUnion Y _ _).mpr ⟨componentImage Y ({C}ᶜ) D'',
      fun h => hne (componentImage_injective Y ({C}ᶜ) (Set.mem_singleton_iff.mp h)), ?_⟩
    rw [← image_componentImage]
    exact ⟨z, hzD'', rfl⟩

end Transfer

section Export

/-- The inheritance of the transverse germs, from the stalk transfer off the leaf for every
curve and leaf. -/
theorem inheritsTransverseBranches_of_transfer
    (h : ∀ (Y : Scheme.{u}) [NoetherianSpace Y] (C : ↥(irreducibleComponents Y)),
      TransversePointTransfer Y C) :
    InheritsTransverseBranches.{u} := by
  intro Y _ _ _ C q _ _ _ htransY
  exact hasTransverseComponentBranches_compl_of_transfer htransY (h Y C)

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The kernel statement of `lem:tree-picard` with the identification data, the tree inheritance
and the two-branches lemma discharged: only the stalk transfer off the leaf remains. -/
theorem rationalTreePicard_trivial_of_exponents_zero_of_transfer
    (h : ∀ (Y : Scheme.{u}) [NoetherianSpace Y] (C : ↥(irreducibleComponents Y)),
      TransversePointTransfer Y C) (n : ℕ) :
    ∀ (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
      [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f],
      Nat.card ↥(irreducibleComponents X) = n →
      topologicalKrullDim X ≤ 1 → (componentPointIncidenceGraph X).IsTree →
      HasTransverseComponentBranches X → ExponentsZeroTrivial k X :=
  rationalTreePicard_trivial_of_exponents_zero'' k (inheritsTransverseBranches_of_transfer h) n

/-- The kernel half of `lem:tree-picard`, with only the stalk transfer off the leaf as a
hypothesis. -/
theorem multidegreeHom_injective_of_transfer
    (h : ∀ (Y : Scheme.{u}) [NoetherianSpace Y] (C : ↥(irreducibleComponents Y)),
      TransversePointTransfer Y C)
    (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (htransX : HasTransverseComponentBranches X)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1) :
    Function.Injective (multidegreeHom k X e) :=
  multidegreeHom_injective_of_transverse k (inheritsTransverseBranches_of_transfer h) X f hdim
    hTree htransX e

end Export

end KltDP.Geometry.RationalTreePicard
