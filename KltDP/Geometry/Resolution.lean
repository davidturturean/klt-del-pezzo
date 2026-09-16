import KltDP.Geometry.PrimeCurveIntersectionNumber
import KltDP.Geometry.PointBlowupGluing
import KltDP.Geometry.ProjectiveProper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Resolutions of normal projective surfaces: the F10 interface

Definitions only, over the accepted `NormalProjectiveSurface k`. For a morphism `π : S.toScheme ⟶ X.toScheme`
compatible with the structure morphisms:

* `IsBirational π` is Stacks Definition 29.51.1 (tag 01RN) for integral schemes: the generic point maps to the
  generic point and the stalk map there is an isomorphism. It cancels on the right (`IsBirational.of_comp`).
* `IsResolution S X π` is Stacks Definition 54.14.1 (tag 0BGK, "a modification `f : X → Y` such that `X` is
  regular", modification = birational proper morphism of integral schemes, Definition 29.52.11, tag 0AAZ), with
  regularity the accepted `RegularPoint` predicate. Properness is a theorem here (`IsResolution.isProper`): every
  morphism over `k` between projective `k`-schemes is proper (`IsProper.of_comp_of_isSeparated`).
* `isoLocus π` / `exceptionalLocus π`: points of `S` with, respectively without, an open neighbourhood of the
  form `π ⁻¹ᵁ U` over which `π` is an isomorphism; the exceptional locus is closed.
* `IsExceptionalCurve π C`: a prime curve contracted to a point. Such a curve lies in the exceptional locus.
* `IsMinusOneCurve hreg C`: `C ≅ P¹_k` over `k` and `C·C = −1` in the accepted `selfIntersectionNumber`
  (Stacks' "exceptional curve of the first kind", Section 54.16, specialised to a regular projective surface over an
  algebraically closed field).
* `IsMinimalResolution S X π`: a resolution with no exceptional `(−1)`-curve.
* `PointBlowupChart`, `IsPointBlowupAt S S' b x'`: `b` is, up to isomorphism, the accepted glued point blowup of `S'`
  at the closed point `x'`; `IsPointBlowupSequence` is "a sequence of blowups in closed points" (Stacks 0C5R).
* `IsContraction S S' b E`: the Stacks Section 54.16 prose definition of a contraction of `E` (proper morphism
  mapping `E` to a closed point `x'` with `𝒪_{S',x'}` regular of dimension two and `S` the blowup of `S'` at `x'`),
  together with the consequences used downstream (regularity of `S'` everywhere, birationality of `b`).

No literature statement is assumed here. Finiteness of the exceptional curves and the adapters identifying the
accepted point blowup with `IsPointBlowupAt` / `IsBirational` are not part of this module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k]

section OverBase

/-- A morphism over `k` between projective `k`-schemes is proper: its composite with the (proper) structure
morphism of the target is the proper structure morphism of the source, and the target is separated over `k`. -/
theorem isProper_of_comp_structureMorphism {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (h : π ≫ X.structureMorphism = S.structureMorphism) :
    IsProper π := by
  haveI : IsProper X.structureMorphism := X.projective.isProper
  haveI : IsProper (π ≫ X.structureMorphism) := by
    rw [h]
    exact S.projective.isProper
  exact IsProper.of_comp_of_isSeparated π X.structureMorphism

end OverBase

section Birational

/-- Stacks Definition 29.51.1 for integral schemes: `π` maps the generic point to the generic point and induces
an isomorphism on the stalks there. -/
structure IsBirational {S X : NormalProjectiveSurface k} (π : S.toScheme ⟶ X.toScheme) : Prop where
  map_genericPoint : π.base (genericPoint S.toScheme) = genericPoint X.toScheme
  isIso_stalkMap_genericPoint : IsIso (π.stalkMap (genericPoint S.toScheme))

/-- Right cancellation: if `b` and `b ≫ π'` are birational, so is `π'`. -/
theorem IsBirational.of_comp {S S' X : NormalProjectiveSurface k}
    {b : S.toScheme ⟶ S'.toScheme} {π' : S'.toScheme ⟶ X.toScheme}
    (hb : IsBirational b) (h : IsBirational (b ≫ π')) : IsBirational π' := by
  have hgen : b.base (genericPoint S.toScheme) = genericPoint S'.toScheme := hb.map_genericPoint
  refine ⟨?_, ?_⟩
  · have hmap := h.map_genericPoint
    rw [Scheme.comp_base_apply, hgen] at hmap
    exact hmap
  · have hiso := h.isIso_stalkMap_genericPoint
    rw [Scheme.stalkMap_comp] at hiso
    haveI := hb.isIso_stalkMap_genericPoint
    have hres : IsIso (π'.stalkMap (b.base (genericPoint S.toScheme))) :=
      IsIso.of_isIso_comp_right (π'.stalkMap (b.base (genericPoint S.toScheme)))
        (b.stalkMap (genericPoint S.toScheme))
    rw [hgen] at hres
    exact hres

end Birational

section Resolution

/-- A resolution of the normal projective surface `X`: a birational morphism over `k` from a regular projective
surface `S` (Stacks 0BGK with 0AAZ). Properness is automatic, see `IsResolution.isProper`. -/
structure IsResolution (S X : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme) : Prop where
  over_base : π ≫ X.structureMorphism = S.structureMorphism
  regular : ∀ s : S.Point, RegularPoint S.toScheme s
  birational : IsBirational π

theorem IsResolution.isProper {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    (h : IsResolution S X π) : IsProper π :=
  isProper_of_comp_structureMorphism π h.over_base

variable {S X : NormalProjectiveSurface k} (π : S.toScheme ⟶ X.toScheme)

/-- Points of `S` having an open neighbourhood `π ⁻¹ᵁ U` over which `π` is an isomorphism. -/
def isoLocus : Set S.toScheme :=
  {s | ∃ U : X.toScheme.Opens, π.base s ∈ U ∧ IsIso (π ∣_ U)}

/-- The exceptional locus: points not mapped isomorphically. -/
def exceptionalLocus : Set S.toScheme := (isoLocus π)ᶜ

theorem isOpen_isoLocus : IsOpen (isoLocus π) := by
  rw [isOpen_iff_forall_mem_open]
  rintro s ⟨U, hsU, hiso⟩
  exact ⟨π.base ⁻¹' (U : Set X.toScheme), fun t ht => ⟨U, ht, hiso⟩,
    U.isOpen.preimage π.continuous, hsU⟩

theorem isClosed_exceptionalLocus : IsClosed (exceptionalLocus π) :=
  (isOpen_isoLocus π).isClosed_compl

theorem exceptionalLocus_eq_empty_of_isIso [IsIso π] : exceptionalLocus π = ∅ := by
  ext s
  simp only [exceptionalLocus, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
  exact ⟨⊤, Set.mem_univ _, inferInstance⟩

/-- Over an open `U` on which `π` is an isomorphism, `π` is injective on `π ⁻¹ᵁ U`. -/
theorem eq_of_isIso_restrict {U : X.toScheme.Opens} [IsIso (π ∣_ U)] {s t : S.toScheme}
    (hs : π.base s ∈ U) (ht : π.base t ∈ U) (h : π.base s = π.base t) : s = t := by
  have hst : (π ∣_ U).base ⟨s, hs⟩ = (π ∣_ U).base ⟨t, ht⟩ := by
    rw [morphismRestrict_base]
    exact Subtype.ext h
  have hinj := (π ∣_ U).homeomorph.injective
    (show (π ∣_ U).homeomorph ⟨s, hs⟩ = (π ∣_ U).homeomorph ⟨t, ht⟩ from hst)
  exact congrArg Subtype.val hinj

/-- A prime curve of `S` contracted by `π` to a single point. -/
def IsExceptionalCurve (C : S.PrimeCurve) : Prop :=
  ∃ x : X.Point, π.base '' (C : Set S.toScheme) = {x}

/-- An exceptional curve lies in the exceptional locus: over an iso-open the map is injective, so a contracted
curve would be a single point, contradicting dimension one. -/
theorem IsExceptionalCurve.subset_exceptionalLocus {C : S.PrimeCurve}
    (hC : IsExceptionalCurve π C) : (C : Set S.toScheme) ⊆ exceptionalLocus π := by
  obtain ⟨x, hx⟩ := hC
  have hmap : ∀ t ∈ (C : Set S.toScheme), π.base t = x := fun t ht => by
    have hmem : π.base t ∈ ({x} : Set X.toScheme) := hx ▸ Set.mem_image_of_mem _ ht
    exact hmem
  rintro s hs ⟨U, hsU, hiso⟩
  haveI := hiso
  have hsub : (C : Set S.toScheme) ⊆ {s} := fun t ht => by
    have htU : π.base t ∈ U := by
      rw [hmap t ht, ← hmap s hs]
      exact hsU
    exact eq_of_isIso_restrict π htU hsU ((hmap t ht).trans (hmap s hs).symm)
  haveI : Subsingleton (C : Set S.toScheme) := (Set.subsingleton_of_subset_singleton hsub).coe_sort
  have hle := topologicalKrullDim_nonpos_of_subsingleton (C : Set S.toScheme)
  rw [C.dimension_one] at hle
  exact (WithBot.coe_lt_coe.mpr (by simp : (0 : ℕ∞) < 1)).not_le hle

end Resolution

section MinusOne

/-- A `(−1)`-curve on a regular projective surface over an algebraically closed field: isomorphic to `P¹_k` over
`k`, with self-intersection `−1`. -/
structure IsMinusOneCurve [IsAlgClosed k] {S : NormalProjectiveSurface k}
    (hreg : ∀ s : S.Point, RegularPoint S.toScheme s) (C : S.PrimeCurve) : Prop where
  isoProjectiveLine : ∃ e : C.toScheme ≅ projectiveSpace k 1,
    e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec
  selfIntersection : C.selfIntersectionNumber hreg = -1

/-- A minimal resolution: a resolution none of whose exceptional curves is a `(−1)`-curve. -/
structure IsMinimalResolution [IsAlgClosed k] (S X : NormalProjectiveSurface k)
    (π : S.toScheme ⟶ X.toScheme) : Prop extends IsResolution S X π where
  no_minusOne_curve : ∀ C : S.PrimeCurve, IsExceptionalCurve π C → ¬ IsMinusOneCurve regular C

end MinusOne

section Blowup

/-- An accepted affine blowup chart around a closed point `y` of `Y`: an affine open immersion `j`, a maximal
point `q` of the chart over `y`, and closedness of `y`. -/
structure PointBlowupChart (Y : Scheme.{u}) (y : Y) where
  R : Type u
  [instCommRing : CommRing R]
  j : Spec (CommRingCat.of R) ⟶ Y
  [instOpenImmersion : IsOpenImmersion j]
  q : PrimeSpectrum R
  [instMaximal : q.asIdeal.IsMaximal]
  isClosed : IsClosed ({j.base q} : Set Y)
  base_eq : j.base q = y

namespace PointBlowupChart

variable {Y : Scheme.{u}} {y : Y} (c : PointBlowupChart Y y)

/-- The accepted glued point blowup of `Y` at `y` along the chart. -/
def scheme : Scheme.{u} :=
  letI := c.instCommRing
  letI := c.instOpenImmersion
  letI := c.instMaximal
  PointBlowupGluing.scheme c.j c.q c.isClosed

/-- The accepted blowdown morphism of the chart. -/
def projection : c.scheme ⟶ Y :=
  letI := c.instCommRing
  letI := c.instOpenImmersion
  letI := c.instMaximal
  PointBlowupGluing.projection c.j c.q c.isClosed

end PointBlowupChart

/-- `b : S ⟶ S'` is the blowup of `S'` at the closed point `x'`: a morphism over `k` identified, through an
isomorphism of `S` with the accepted glued point blowup, with the accepted blowdown. -/
structure IsPointBlowupAt (S S' : NormalProjectiveSurface k) (b : S.toScheme ⟶ S'.toScheme)
    (x' : S'.Point) : Prop where
  over_base : b ≫ S'.structureMorphism = S.structureMorphism
  blowup : ∃ (c : PointBlowupChart S'.toScheme x') (e : S.toScheme ≅ c.scheme),
    e.hom ≫ c.projection = b

/-- "A sequence of blowups in closed points" (Stacks 0C5R): an isomorphism over `k` (the empty sequence) or a
point blowup followed by a sequence. -/
inductive IsPointBlowupSequence :
    (S T : NormalProjectiveSurface k) → (S.toScheme ⟶ T.toScheme) → Prop
  | of_isIso {S T : NormalProjectiveSurface k} (f : S.toScheme ⟶ T.toScheme) (hf : IsIso f)
      (hover : f ≫ T.structureMorphism = S.structureMorphism) : IsPointBlowupSequence S T f
  | step {S S' T : NormalProjectiveSurface k} (b : S.toScheme ⟶ S'.toScheme)
      (g : S'.toScheme ⟶ T.toScheme) (x' : S'.Point) (hb : IsPointBlowupAt S S' b x')
      (hg : IsPointBlowupSequence S' T g) : IsPointBlowupSequence S T (b ≫ g)

/-- A contraction of the prime curve `E ⊂ S` (Stacks, Section 54.16 prose): `b` maps `E` to a closed point `x'`
of `S'` whose local ring is regular of dimension two, and `S` is the blowup of `S'` at `x'`. The fields
`regular` (regularity of `S'` at every point) and `birational` are the consequences used by the consumers. -/
structure IsContraction (S S' : NormalProjectiveSurface k) (b : S.toScheme ⟶ S'.toScheme)
    (E : S.PrimeCurve) : Prop where
  regular : ∀ s' : S'.Point, RegularPoint S'.toScheme s'
  birational : IsBirational b
  center : ∃ x' : S'.Point, IsClosed ({x'} : Set S'.toScheme) ∧
    b.base '' (E : Set S.toScheme) = {x'} ∧
    ringKrullDim (S'.toScheme.presheaf.stalk x') = 2 ∧ IsPointBlowupAt S S' b x'

theorem IsContraction.over_base {S S' : NormalProjectiveSurface k} {b : S.toScheme ⟶ S'.toScheme}
    {E : S.PrimeCurve} (h : IsContraction S S' b E) :
    b ≫ S'.structureMorphism = S.structureMorphism := by
  obtain ⟨x', -, -, -, hb⟩ := h.center
  exact hb.over_base

theorem IsContraction.isProper {S S' : NormalProjectiveSurface k} {b : S.toScheme ⟶ S'.toScheme}
    {E : S.PrimeCurve} (h : IsContraction S S' b E) : IsProper b :=
  isProper_of_comp_structureMorphism b h.over_base

end Blowup

end KltDP.Geometry
