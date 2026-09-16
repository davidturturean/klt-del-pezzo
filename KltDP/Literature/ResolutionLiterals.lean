import KltDP.Geometry.Resolution

/-!
# Stacks resolution-of-surfaces literals as explicit Prop hypotheses (F10)

Nothing is assumed here. Each `…Literal` is a `Prop`-valued structure whose single field is the Stacks statement
specialised to the accepted classes (`NormalProjectiveSurface k`, `RegularPoint`, `IsResolution`, `IsContraction`,
`IsMinusOneCurve`, `IsPointBlowupSequence`). Consumers take these structures as hypotheses, so a later acceptance
(root decision) makes them unconditional. The exact source texts, tags, fetch date and every specialisation step
are recorded in `laneE/F10_LITERALS.md`.

* `LipmanResolutionLiteral` — Stacks 0BGP (Theorem 54.14.5, Lipman), direction (4) ⇒ (2), for
  `X : NormalProjectiveSurface k` with finite singular locus; the resolution is delivered as a
  `NormalProjectiveSurface k` (projectivity of the normalized-blowup resolution is a specialisation debt).
* `CastelnuovoContractionLiteral` — Stacks 0C2N (Lemma 54.16.9 (1)) over `S = Spec k` for a `(−1)`-curve.
* `ContractionUniversalLiteral` — Stacks 0C5J (Lemma 54.16.1), universal property of a contraction.
* `BirationalFactorizationLiteral` — Stacks 0C5R (Lemma 54.17.1).
* `CommonResolutionLiteral` — Stacks 0C5S (Lemma 54.17.2).
* `ContractionMeasureHypothesis` — NOT a literature statement: a named termination hypothesis (a natural-number
  invariant of surfaces dropping along contractions; intended discharge: the Picard rank through Stacks 0C5L,
  `Pic(X) ≅ Pic(X') ⊕ ℤ`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Geometry

universe u

namespace KltDP.Literature.Stacks

variable (k : Type u) [Field k]

/-- Stacks 0BGP (Theorem 54.14.5, Lipman): "Let `Y` be a two dimensional integral Noetherian scheme. The following
are equivalent (1) there exists an alteration `X → Y` with `X` regular, (2) there exists a resolution of
singularities of `Y`, (3) `Y` has a resolution of singularities by normalized blowups, (4) the normalization
`Y^ν → Y` is finite, `Y^ν` has finitely many singular points `y_1, …, y_m`, and for each `y_i` the completion of
`𝒪_{Y^ν, y_i}` is normal." Encoded: direction (4) ⇒ (2) for `Y = X.toScheme`, `X : NormalProjectiveSurface k`
(normal, so `Y^ν = Y`), with the finiteness clause of (4) kept as a hypothesis; the completion clause (excellence of
finite-type `k`-schemes) and projectivity of the resolution over `k` are specialisation debts. -/
structure LipmanResolutionLiteral : Prop where
  exists_resolution : ∀ X : NormalProjectiveSurface k, (singularLocus X.toScheme).Finite →
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme), IsResolution S X π

/-- Stacks 0C2N (Lemma 54.16.9): "Let `S` be a Noetherian scheme. Let `f : X → S` be a morphism of finite type. Let
`E ⊂ X` be an exceptional curve of the first kind which is in a fibre of `f`. (1) If `X` is projective over `S`,
then there exists a contraction `X → X'` of `E` and `X'` is projective over `S`. (2) If `X` is quasi-projective over
`S`, then there exists a contraction `X → X'` of `E` and `X'` is quasi-projective over `S`." Encoded: part (1) with
`S = Spec k`, `X` a regular `NormalProjectiveSurface k`, `E` a `(−1)`-curve (`IsMinusOneCurve`), the contraction in
the sense of `IsContraction`, and `X'` again a `NormalProjectiveSurface k`. -/
structure CastelnuovoContractionLiteral [IsAlgClosed k] : Prop where
  exists_contraction : ∀ (S : NormalProjectiveSurface k)
    (hreg : ∀ s : S.Point, RegularPoint S.toScheme s) (E : S.PrimeCurve),
    IsMinusOneCurve hreg E →
      ∃ (S' : NormalProjectiveSurface k) (b : S.toScheme ⟶ S'.toScheme), IsContraction S S' b E

/-- Stacks 0C5J (Lemma 54.16.1): "Let `X` be a Noetherian scheme. Let `E ⊂ X` be an exceptional curve of the first
kind. If a contraction `X → X'` of `E` exists, then it has the following universal property: for every morphism
`φ : X → Y` such that `φ(E)` is a point, there is a unique factorization `X → X' → Y` of `φ`." Encoded for
contractions between `NormalProjectiveSurface k` and arbitrary target schemes `Y`. -/
structure ContractionUniversalLiteral : Prop where
  factor : ∀ (S S' : NormalProjectiveSurface k) (b : S.toScheme ⟶ S'.toScheme) (E : S.PrimeCurve),
    IsContraction S S' b E → ∀ (Y : Scheme.{u}) (φ : S.toScheme ⟶ Y),
      (∃ y : Y, φ.base '' (E : Set S.toScheme) = {y}) → ∃! φ' : S'.toScheme ⟶ Y, b ≫ φ' = φ

/-- Stacks 0C5R (Lemma 54.17.1): "Let `f : X → Y` be a proper birational morphism between integral Noetherian
schemes regular of dimension `2`. Then `f` is a sequence of blowups in closed points." Encoded for regular
`NormalProjectiveSurface k` and morphisms over `k` (proper automatically). -/
structure BirationalFactorizationLiteral : Prop where
  factor : ∀ (S T : NormalProjectiveSurface k) (f : S.toScheme ⟶ T.toScheme),
    (∀ s : S.Point, RegularPoint S.toScheme s) → (∀ t : T.Point, RegularPoint T.toScheme t) →
    f ≫ T.structureMorphism = S.structureMorphism → IsBirational f → IsPointBlowupSequence S T f

/-- `S` and `T` are `k`-birational: dense opens `U ⊆ S`, `V ⊆ T` with an isomorphism `U ≅ V` over `k`
(Stacks Lemma 29.51.7 characterisation of `S`-birational integral schemes). -/
def IsBirationalPair (S T : NormalProjectiveSurface k) : Prop :=
  ∃ (U : S.toScheme.Opens) (V : T.toScheme.Opens), Dense (U : Set S.toScheme) ∧
    Dense (V : Set T.toScheme) ∧ ∃ e : U.toScheme ≅ V.toScheme,
      e.hom ≫ V.ι ≫ T.structureMorphism = U.ι ≫ S.structureMorphism

/-- Stacks 0C5S (Lemma 54.17.2): "Let `S` be a Noetherian scheme. Let `X` and `Y` be proper integral schemes over
`S` which are regular of dimension `2`. Then `X` and `Y` are `S`-birational if and only if there exists a diagram of
`S`-morphisms `X = X_0 ← X_1 ← … ← X_n = Y_m → … → Y_1 → Y_0 = Y` where each morphism is a blowup in a closed
point." Encoded with `S = Spec k`, `X`, `Y` regular `NormalProjectiveSurface k`, and the diagram as a common source
`Z` with two point-blowup sequences. -/
structure CommonResolutionLiteral : Prop where
  iff : ∀ (S T : NormalProjectiveSurface k),
    (∀ s : S.Point, RegularPoint S.toScheme s) → (∀ t : T.Point, RegularPoint T.toScheme t) →
    (IsBirationalPair k S T ↔ ∃ (Z : NormalProjectiveSurface k) (f : Z.toScheme ⟶ S.toScheme)
      (g : Z.toScheme ⟶ T.toScheme), IsPointBlowupSequence Z S f ∧ IsPointBlowupSequence Z T g)

/-- Named termination hypothesis (not a literature statement): some natural-number invariant of surfaces over `k`
drops strictly along every contraction. Intended discharge: the Picard rank, `ρ(S) = ρ(S') + 1`, from Stacks 0C5L
(Lemma 54.16.5, `0 → Pic(X') → Pic(X) → ℤ → 0`) once a Picard rank exists in the accepted tree. -/
structure ContractionMeasureHypothesis : Prop where
  exists_measure : ∃ μ : NormalProjectiveSurface k → ℕ,
    ∀ (S S' : NormalProjectiveSurface k) (b : S.toScheme ⟶ S'.toScheme) (E : S.PrimeCurve),
      IsContraction S S' b E → μ S' < μ S

end KltDP.Literature.Stacks
