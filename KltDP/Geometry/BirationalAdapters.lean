import KltDP.Geometry.Resolution
import KltDP.Geometry.PointBlowupIntegral

/-!
# Birationality adapters: isomorphism over a nonempty open ⇒ Stacks-birational

`IsBirationalScheme f` is the scheme-level form of `KltDP.Geometry.IsBirational` (Stacks Definition 29.51.1,
tag 01RO, for integral schemes): the generic point maps to the generic point and the stalk map there is an
isomorphism.

Main adapter (`isBirationalScheme_of_isIso_restrict`): if `f : Y ⟶ Z` is an isomorphism over a nonempty open
`U ⊆ Z` (`IsIso (f ∣_ U)`), then `f` is birational. The generic point of `Y` lies in the nonempty open `f ⁻¹ᵁ U`;
the isomorphism `f ∣_ U` and the open immersions `U.ι`, `(f ⁻¹ᵁ U).ι` preserve generic points
(`genericPoint_eq_of_isOpenImmersion`), and `morphismRestrict_ι` compares the composites. The stalk map of `f` at a
point over `U` is identified with the stalk map of the isomorphism `f ∣_ U` (`morphismRestrictStalkMap`).

Applications: the surface-level `IsBirational.of_isIso_restrict`, and the accepted glued point blowup
`PointBlowupGluing.projection`, an isomorphism over the puncture (`projection_restrict_puncture_isIso`), is
birational (`PointBlowupGluing.projection_isBirationalScheme`, for a nonzero maximal centre on an integral base).
No literature statement is assumed. Not proved here: `IsPointBlowupAt` for the accepted projection (it needs a
`NormalProjectiveSurface` structure on the glued scheme).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- Stacks Definition 29.51.1 (tag 01RO) for integral schemes, at the level of schemes. -/
structure IsBirationalScheme {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z) : Prop where
  map_genericPoint : f.base (genericPoint Y) = genericPoint Z
  isIso_stalkMap_genericPoint : IsIso (f.stalkMap (genericPoint Y))

/-- The preimage of a nonempty open over which `f` is an isomorphism is nonempty. -/
theorem preimage_nonempty_of_isIso_restrict {Y Z : Scheme.{u}} (f : Y ⟶ Z) (U : Z.Opens)
    [Nonempty U.toScheme] [IsIso (f ∣_ U)] : ((f ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
  let y : U.toScheme := Classical.choice (inferInstance : Nonempty U.toScheme)
  let x' : (f ⁻¹ᵁ U).toScheme := (asIso (f ∣_ U)).inv.base y
  exact ⟨x'.val, x'.property⟩

/-- The generic point of `Y` lies over `U`. -/
theorem genericPoint_mem_preimage_of_isIso_restrict {Y Z : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Z)
    (U : Z.Opens) [Nonempty U.toScheme] [IsIso (f ∣_ U)] : f.base (genericPoint Y) ∈ U := by
  have hmem : genericPoint Y ∈ ((f ⁻¹ᵁ U : Y.Opens) : Set Y) :=
    ((genericPoint_spec Y).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).mpr
      (by simpa using preimage_nonempty_of_isIso_restrict f U)
  exact hmem

/-- Over a nonempty open on which `f` is an isomorphism, the generic point maps to the generic point. -/
theorem map_genericPoint_of_isIso_restrict {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (f : Y ⟶ Z) (U : Z.Opens) [Nonempty U.toScheme] [IsIso (f ∣_ U)] :
    f.base (genericPoint Y) = genericPoint Z := by
  let y : U.toScheme := Classical.choice (inferInstance : Nonempty U.toScheme)
  haveI : Nonempty (f ⁻¹ᵁ U).toScheme := ⟨(asIso (f ∣_ U)).inv.base y⟩
  haveI : IsIntegral (f ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have h1 : (f ⁻¹ᵁ U).ι.base (genericPoint (f ⁻¹ᵁ U).toScheme) = genericPoint Y :=
    genericPoint_eq_of_isOpenImmersion _
  have h2 : (f ∣_ U).base (genericPoint (f ⁻¹ᵁ U).toScheme) = genericPoint U.toScheme :=
    genericPoint_eq_of_isOpenImmersion _
  have h3 : U.ι.base (genericPoint U.toScheme) = genericPoint Z :=
    genericPoint_eq_of_isOpenImmersion _
  have hcomp : U.ι.base ((f ∣_ U).base (genericPoint (f ⁻¹ᵁ U).toScheme)) =
      f.base ((f ⁻¹ᵁ U).ι.base (genericPoint (f ⁻¹ᵁ U).toScheme)) := by
    rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply, morphismRestrict_ι]
  rw [h2, h3, h1] at hcomp
  exact hcomp.symm

/-- The stalk map of `f` at a point over `U` is an isomorphism. -/
theorem isIso_stalkMap_of_isIso_restrict {Y Z : Scheme.{u}} (f : Y ⟶ Z) (U : Z.Opens)
    [IsIso (f ∣_ U)] (y : Y) (hy : f.base y ∈ U) : IsIso (f.stalkMap y) := by
  have e := morphismRestrictStalkMap f U ⟨y, hy⟩
  exact (Arrow.isIso_iff_isIso_of_isIso e.hom).mp inferInstance

/-- **Adapter.** An isomorphism over a nonempty open is birational (Stacks 29.51.1). -/
theorem isBirationalScheme_of_isIso_restrict {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (f : Y ⟶ Z) (U : Z.Opens) [Nonempty U.toScheme] [IsIso (f ∣_ U)] : IsBirationalScheme f :=
  ⟨map_genericPoint_of_isIso_restrict f U,
    isIso_stalkMap_of_isIso_restrict f U _ (genericPoint_mem_preimage_of_isIso_restrict f U)⟩

/-- The surface-level birationality predicate agrees with the scheme-level one. -/
theorem isBirational_iff_isBirationalScheme {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) : IsBirational π ↔ IsBirationalScheme π :=
  ⟨fun h => ⟨h.map_genericPoint, h.isIso_stalkMap_genericPoint⟩,
    fun h => ⟨h.map_genericPoint, h.isIso_stalkMap_genericPoint⟩⟩

/-- A morphism of surfaces that is an isomorphism over a nonempty open of the target is birational. -/
theorem IsBirational.of_isIso_restrict {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (U : X.toScheme.Opens) [Nonempty U.toScheme] [IsIso (π ∣_ U)] :
    IsBirational π :=
  (isBirational_iff_isBirationalScheme π).mpr (isBirationalScheme_of_isIso_restrict π U)

namespace PointBlowupGluing

/-- **The accepted point blowdown is birational**: it is an isomorphism over the (nonempty) puncture. -/
theorem projection_isBirationalScheme {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X)) (hq : q.asIdeal ≠ ⊥) :
    letI : IsIntegral (scheme j q hclosed) := scheme_isIntegral j q hclosed hq
    IsBirationalScheme (projection j q hclosed) := by
  letI : IsIntegral (scheme j q hclosed) := scheme_isIntegral j q hclosed hq
  haveI : Nonempty (puncture j q hclosed).toScheme := puncture_nonempty j q hclosed hq
  haveI : IsIso ((projection j q hclosed) ∣_ puncture j q hclosed) :=
    projection_restrict_puncture_isIso j q hclosed
  exact isBirationalScheme_of_isIso_restrict (projection j q hclosed) (puncture j q hclosed)

end PointBlowupGluing

end KltDP.Geometry
