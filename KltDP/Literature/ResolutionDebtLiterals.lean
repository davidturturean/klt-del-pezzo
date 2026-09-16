import KltDP.Literature.ResolutionLiterals
import KltDP.Geometry.BirationalAdapters
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Localization.AtPrime

/-!
# Stacks literals for the specialisation debts of Lipman's theorem, and for point blowups (F10, E2)

Prop-valued structures used only as hypotheses; nothing is assumed. Exact texts, tags, fetch date (2026-09-11,
https://stacks.math.columbia.edu/tag/<tag>) and every specialisation step are in `laneE/F10_LITERALS.md`.

Commutative algebra (no base field):
* `localCompletion A` is Mathlib's `𝔪`-adic completion `A^∧`; `formalFibre A 𝔮` is `(A^∧)_𝔮 / 𝔮 (A^∧)_𝔮`, the
  middle form of Stacks' definition of the formal fibre `A^∧ ⊗_A κ(𝔮)` (Section 15.51, tag 07GG);
  `IsNormalRingStacks` is Stacks Definition 10.37.11 (tag 00GV); `FormalFibresNormal A` says all formal fibres of
  `A` are normal rings.
* `CompletionNormalLiteral` — Stacks 0C23 (Lemma 15.53.6), exact, for all Noetherian local rings.

Over a field `k`:
* `FiniteTypeExcellentFormalFibresLiteral` — Stacks 07QW (Proposition 15.53.3: fields and finite type ring
  extensions are excellent) with 07QU (Lemma 15.53.2: localizations of finite type rings over excellent rings are
  excellent) and the parenthetical of 0C23 (excellent local rings have normal formal fibres): every localization
  at a prime of a finite type `k`-algebra has normal formal fibres.
* `LipmanModificationLiteral` — Stacks 0BGP (Theorem 54.14.5), (4) ⇒ (2), for `Y = X.toScheme` with
  `X : NormalProjectiveSurface k`. `Y` is normal, so its normalization is an isomorphism (Stacks 035Q, 0BXC, 0AB1)
  and finite. The conclusion is a resolution in Stacks' sense (0BGK, 0AAZ, 01RO): an integral regular scheme with a
  proper birational morphism to `Y`, birationality as `IsBirationalScheme`.
* `RegularProperProjectiveLiteral` — Stacks 0C5P (Lemma 54.16.11) over `S = Spec k`; "projective" over the affine
  base is H-projective (01W8 Definition 29.44.1, 087S Lemma 29.44.16), i.e. `IsProjectiveOverField`.
* `BirationalDimensionLiteral` — Stacks 02JX (Lemma 29.53.4) for a proper birational morphism onto a normal
  projective surface (closed, locally of finite type, dominant, transcendence degree `0`).
* `BlowupRegularLiteral` — Stacks 0AGR (Lemma 54.3.2), for `IsPointBlowupAt` over a regular surface.

Named hypotheses (not Stacks statements):
* `BlowupExceptionalMinusOne` — the exceptional curve of a point blowup of a regular surface is a `(−1)`-curve in
  the accepted sense (intended source 0AGQ, Lemma 54.3.1; the identification of `deg 𝒩_{E/X}` with the accepted
  `selfIntersectionNumber` is open in the library).
* `MinimalResolutionDominationHypothesis` — a minimal resolution is dominated by every resolution. Stacks Chapter 54
  contains no uniqueness or domination statement for minimal resolutions (Sections 54.16–54.17 list only 0C5J, 0C5K,
  0C2K, 0C2L, 0C5L, 0C5M, 0C2J, 0C2M, 0C2N, 0C5N, 0C5P, 0C5R, 0C5S).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Geometry

universe u

namespace KltDP.Literature.Stacks

section CommutativeAlgebra

/-- The `𝔪`-adic completion `A^∧` of a local ring `A`. -/
abbrev localCompletion (A : Type u) [CommRing A] [IsLocalRing A] : Type u :=
  AdicCompletion (IsLocalRing.maximalIdeal A) A

/-- The image in `A^∧` of the complement of the prime `𝔮 ⊆ A`. -/
abbrev formalFibreSubmonoid (A : Type u) [CommRing A] [IsLocalRing A] (q : Ideal A) [q.IsPrime] :
    Submonoid (localCompletion A) :=
  Algebra.algebraMapSubmonoid (localCompletion A) q.primeCompl

/-- The formal fibre of `A` at `𝔮` (Stacks, Section 15.51, tag 07GG: "For a prime `𝔮` of `A` the fibre ring
`A^∧ ⊗_A κ(𝔮) = (A^∧)_𝔮/𝔮(A^∧)_𝔮 = (A/𝔮)^∧ ⊗_{A/𝔮} κ(𝔮)` is called a formal fibre of `A`"), in the middle form:
the localization of `A^∧` at the image of `A \ 𝔮`, modulo the extension of `𝔮`. -/
abbrev formalFibre (A : Type u) [CommRing A] [IsLocalRing A] (q : Ideal A) [q.IsPrime] : Type u :=
  Localization (formalFibreSubmonoid A q) ⧸
    Ideal.map ((algebraMap (localCompletion A) (Localization (formalFibreSubmonoid A q))).comp
      (algebraMap A (localCompletion A))) q

/-- Stacks Definition 10.37.11 (tag 00GV): "A ring `R` is called normal if for every prime `𝔭 ⊂ R` the
localization `R_𝔭` is a normal domain", a normal domain being an integrally closed domain (10.37.1). -/
def IsNormalRingStacks (B : Type u) [CommRing B] : Prop :=
  ∀ (P : Ideal B) [P.IsPrime],
    IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)

/-- All formal fibres of the local ring `A` are normal rings. -/
def FormalFibresNormal (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (q : Ideal A) [q.IsPrime], IsNormalRingStacks (formalFibre A q)

/-- Stacks 0C23, Lemma 15.53.6: "Let `(A, 𝔪)` be a Noetherian local ring. If `A` is normal and the formal fibres of
`A` are normal (for example if `A` is excellent or quasi-excellent), then `A^∧` is normal." Normality of the local
rings `A` and `A^∧` is recorded as "integrally closed domain" (for a local ring `R`, `R_𝔪 = R`). -/
structure CompletionNormalLiteral : Prop where
  completion_normal : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
    IsDomain A → IsIntegrallyClosed A → FormalFibresNormal A →
      IsDomain (localCompletion A) ∧ IsIntegrallyClosed (localCompletion A)

end CommutativeAlgebra

variable (k : Type u) [Field k]

/-- Stacks 07QW, Proposition 15.53.3: "The following types of rings are excellent: (1) fields, (2) Noetherian
complete local rings, (3) `ℤ`, (4) Dedekind domains with fraction field of characteristic zero, (5) finite type ring
extensions of any of the above"; Stacks 07QU, Lemma 15.53.2: "Any localization of a finite type ring over a
(quasi-)excellent ring is (quasi-)excellent"; and Stacks 0C23 (Lemma 15.53.6): the formal fibres of `A` are normal
"for example if `A` is excellent or quasi-excellent". Encoded: for a finite type `k`-algebra `B` and a prime `𝔭`,
every localization `A` of `B` at `𝔭` has normal formal fibres. -/
structure FiniteTypeExcellentFormalFibresLiteral : Prop where
  formalFibres_normal : ∀ (B : Type u) [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (p : Ideal B) [p.IsPrime] (A : Type u) [CommRing A] [IsLocalRing A] [Algebra B A]
    [IsLocalization.AtPrime A p], FormalFibresNormal A

/-- Stacks 0BGP, Theorem 54.14.5 (Lipman): "Let `Y` be a two dimensional integral Noetherian scheme. The following
are equivalent (1) there exists an alteration `X → Y` with `X` regular, (2) there exists a resolution of
singularities of `Y`, (3) `Y` has a resolution of singularities by normalized blowups, (4) the normalization
`Y^ν → Y` is finite, `Y^ν` has finitely many singular points `y_1, …, y_m`, and for each `y_i` the completion of
`𝒪_{Y^ν, y_i}` is normal." Encoded: (4) ⇒ (2) for `Y = X.toScheme` (normal, so `Y^ν = Y`: Stacks 035Q, 0BXC,
0AB1), with the resolution as in 0BGK (Definition 54.14.1) and 0AAZ (Definition 29.52.11): an integral scheme `S`,
regular at every point, with a proper morphism to `Y` that is birational in the sense of 01RO (Definition 29.51.1). -/
structure LipmanModificationLiteral : Prop where
  exists_resolution : ∀ X : NormalProjectiveSurface k, (singularLocus X.toScheme).Finite →
    (∀ x ∈ singularLocus X.toScheme,
      IsDomain (localCompletion (X.toScheme.presheaf.stalk x)) ∧
        IsIntegrallyClosed (localCompletion (X.toScheme.presheaf.stalk x))) →
    ∃ (S : Scheme.{u}) (π : S ⟶ X.toScheme) (_ : IsIntegral S),
      (∀ s : S, RegularPoint S s) ∧ IsProper π ∧ IsBirationalScheme π

/-- Stacks 0C5P, Lemma 54.16.11: "Let `S` be a Noetherian scheme. Let `f : X → S` be a proper morphism with `X`
regular of dimension `2`. Then `X` is projective over `S`." Encoded with `S = Spec k`: since `Spec k` is affine it
has an ample invertible sheaf, so projective morphisms to it are H-projective (Stacks 087S, Lemma 29.44.16), i.e.
have a closed immersion into `P^n_k` over `k` (Stacks 01W8, Definition 29.44.1) — `IsProjectiveOverField`. -/
structure RegularProperProjectiveLiteral : Prop where
  projective : ∀ (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of k)), IsProper f →
    (∀ y : Y, RegularPoint Y y) → topologicalKrullDim Y = 2 → IsProjectiveOverField f

/-- Stacks 02JX, Lemma 29.53.4: "Let `f : X → Y` be a morphism of schemes. Assume that `Y` is locally Noetherian,
`X` and `Y` are integral schemes, `f` is dominant, and `f` is locally of finite type. Then we have
`dim(X) ≤ dim(Y) + trdeg_{R(Y)} R(X)`. If `f` is closed then equality holds." Encoded for a proper morphism `f`
(closed, locally of finite type) onto a normal projective surface (locally Noetherian) which is birational in the
sense of 01RO: the generic point maps to the generic point (dominant, 01RP) and `R(Y) → R(X)` is the isomorphism of
stalks at the generic points, so the transcendence degree is `0`. -/
structure BirationalDimensionLiteral : Prop where
  dim_eq : ∀ (X : NormalProjectiveSurface k) (Y : Scheme.{u}) [IsIntegral Y] (f : Y ⟶ X.toScheme),
    IsProper f → IsBirationalScheme f → topologicalKrullDim Y = topologicalKrullDim X.toScheme

/-- Stacks 0AGR, Lemma 54.3.2: "Let `(A, 𝔪, κ)` be a regular local ring of dimension `2`. Let
`f : X → S = Spec(A)` be the blowing up of `A` in `𝔪`. Then `X` is an irreducible regular scheme." Encoded for a
point blowup `IsPointBlowupAt S S' b x'` of a regular surface `S'`: off `x'` the blowup is an isomorphism, and over
`x'` blowing up commutes with the flat base change `Spec 𝒪_{S',x'} → S'` (Stacks 0805, Lemma 31.33.3). -/
structure BlowupRegularLiteral : Prop where
  regular : ∀ (S S' : NormalProjectiveSurface k) (b : S.toScheme ⟶ S'.toScheme) (x' : S'.Point),
    IsPointBlowupAt S S' b x' → (∀ s' : S'.Point, RegularPoint S'.toScheme s') →
      ∀ s : S.Point, RegularPoint S.toScheme s

/-- Named hypothesis (not a Stacks statement in this form): the exceptional curve of the point blowup of a regular
projective surface over an algebraically closed field is a `(−1)`-curve contracted to the centre. Intended source:
Stacks 0AGQ (Lemma 54.3.1: `E ≅ P¹_κ` and `𝒩_{E/X} = O_{P¹}(−1)`) plus the identification of the normal degree with
the accepted `selfIntersectionNumber`; the general form is open in the library. -/
structure BlowupExceptionalMinusOne [IsAlgClosed k] : Prop where
  exists_minusOne : ∀ (S S' : NormalProjectiveSurface k) (b : S.toScheme ⟶ S'.toScheme)
    (x' : S'.Point), IsPointBlowupAt S S' b x' → (∀ s' : S'.Point, RegularPoint S'.toScheme s') →
    ∀ hreg : ∀ s : S.Point, RegularPoint S.toScheme s,
      ∃ E : S.PrimeCurve, IsMinusOneCurve hreg E ∧ b.base '' (E : Set S.toScheme) = {x'}

/-- Named hypothesis (no Stacks statement exists; see the module docstring): every resolution of `X` factors
through a minimal resolution of `X` by a birational morphism over `X`. -/
structure MinimalResolutionDominationHypothesis [IsAlgClosed k] : Prop where
  dominates : ∀ (S X : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme),
    IsMinimalResolution S X π → ∀ (S' : NormalProjectiveSurface k) (π' : S'.toScheme ⟶ X.toScheme),
      IsResolution S' X π' → ∃ f : S'.toScheme ⟶ S.toScheme, f ≫ π = π' ∧ IsBirational f

end KltDP.Literature.Stacks
