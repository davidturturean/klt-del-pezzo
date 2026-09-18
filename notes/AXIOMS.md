# Axioms used

The formalization contains no `sorry`. Besides `propext`, `Classical.choice` and `Quot.sound`, the final theorems (`KltDP.Manuscript.uniformSevenPointBound`, `KltDP.Manuscript.S01.sharpnessExampleCharThree`, `KltDP.Manuscript.S01.characteristicTwoFamily`) depend on the 28 published statements below. Each is declared as a single `axiom` in `KltDP/Literature/`, in the exact form in which it is used; the file records the source, the pinned edition or revision where one was recorded, and the specialisations made in translating the published statement into the Lean statement. Nothing stated in the paper is admitted. The recorded `#print axioms` output is `audit/axiom-report.txt`, and `python3 scripts/check_axioms.py` checks it against exactly this list.

## Summary

| Group | Count |
|---|---|
| Hartshorne, *Algebraic Geometry* (GTM 52) | 12 |
| Stacks Project | 12 |
| Lipman (as Stacks 0BGP, Theorem 54.14.5) | 1 |
| Keel, Ann. Math. 149 (1999) | 1 |
| Zariski, Ann. Inst. Fourier 2 (1950) | 1 |
| Tanaka, Ann. Inst. Fourier 68 (2018) | 1 |
| **Total** | **28** |

| # | Lean declaration (`KltDP.Literature.…`) | File (`KltDP/…`) | Published source | Statement | Where it enters the paper |
|---|---|---|---|---|---|
| H1 | `Hartshorne.castelnuovo_contraction_literal` | `Literature/HartshorneCastelnuovoLiteral.lean` | Hartshorne, *Algebraic Geometry*, V.5.7 (p. 414) | A (−1)-curve E ≅ P¹ on a regular projective surface is the exceptional curve of a point blowup: S is the blowup of a regular projective surface T at a point, with E the fibre. | Transitive only (`Geometry/GeneralMinimalResolutionExistence`, `Geometry/ActualFiniteDisjointContractions`) |
| H2 | `Hartshorne.hasContractionLifts_instance` | `Literature/Hartshorne/StrictTransformInstance.lean` | Hartshorne V.3.6, II.7.15, II.7.13(a)/II.7.14, V.5.3/V.5.7; multiplicity def. V.3 p. 388 | Strict transforms exist along any contraction of a (−1)-curve between regular projective surfaces: b\*Q = Q̃ + m·E, m = 0 iff Q misses the centre, Q̃ ≅ Q when m ≤ 1, every curve ≠ E is a strict transform. | §4, Thm 4.6 terminal case d = 1 (`Main/Final` → `S04.isolatedExchangeHyp_of_literal`) |
| H3 | `Hartshorne.hurwitz_degreeTwo_projectiveLine_instance` | `Literature/Hartshorne/HurwitzDegreeTwoInstance.lean` | Hartshorne IV Cor. 2.4 (Hurwitz) + Prop. IV.2.2(b); also Stacks 0C1B | A degree-two map B → P¹ from a curve B ≅ P¹ in char p > 2 has at most two totally ramified points (points of P¹ with a singleton fibre). | §7, Lemma 7.2 → Thm 7.5 (`S07/HurwitzInput`) |
| H4 | `Hartshorne.integral_numerical_group_free_finite_literal` | `Literature/Hartshorne/IntegralNumericalGroup.lean` | Hartshorne V Remark 1.9.1, p. 364 | Weil divisors modulo numerical equivalence on a regular integral projective surface form a free abelian group of finite rank. | §2, §3 (`Geometry/SurfaceNumericalFinitenessProved` imported by `S02/AnticanonicalContraction`, `S02/ExteriorNullCurves`, `S03/RulingFibers`, `S03/NefThresholdCore`, `S03/NefThreshold`) |
| H5 | `Hartshorne.minimal_surface_classification_literal` | `Literature/Hartshorne/MinimalSurfaceClassification.lean` | Hartshorne V.6.1 | For a minimal regular projective surface with canonical divisor K: all plurigenera vanish iff P₁₂ = 0, and P₁₂ = 0 iff X is birational to P² or X is ruled over a regular curve (P¹-bundle with a section). | Transitive only (`Geometry/HartshorneClassificationLiteralUse`) |
| H6 | `Hartshorne.nonsingular_complete_surface_projective_literal` | `Literature/Hartshorne/SurfaceProjectivity.lean` | Hartshorne II Remark 4.10.2(b), p. 105 (defs. pp. 105, 32/130, 103) | Every nonsingular complete surface over an algebraically closed field is projective (closed immersion into some Pⁿ). | Transitive only (`Examples/FrobeniusProjectivityProved`, `Geometry/RegularProperSurface`) |
| H7 | `Hartshorne.point_blowup_structure_cohomology_literal` | `Literature/Hartshorne/PointBlowupCohomology.lean` | Hartshorne V.3.4, pp. 387–388 (conventions pp. 357/386) | For the blowup π of a regular projective surface at a closed point: π\*O = O, Rⁱπ\*O = 0 for i > 0, and Hⁱ(X̃, O) ≅ Hⁱ(X, O) for all i. | Transitive only (`Geometry/PointBlowupSequenceCohomologyLiteralUse`, `Geometry/PointBlowupCohomologyLiteralUse`) |
| H8 | `Hartshorne.ruled_surface_genus_literal` | `Literature/Hartshorne/RuledSurfaceGenus.lean` | Hartshorne V.2.5 | For a surface ruled over a curve of genus g: χ(O_X) − 1 = −g, H⁰(ω_X) = 0, h¹(O_X) = g. | Transitive only (`Geometry/RuledSurfaceNumerics`, `Geometry/RuledProjectiveLineBaseCohomology`, `Geometry/RationalSurfaceStructureCohomology`) |
| H9 | `Hartshorne.ruled_surface_picard_literal` | `Literature/Hartshorne/RuledSurfacePicard.lean` | Hartshorne V.2.3 | For a surface ruled over C with section S₀ and fibre F: Pic X ≅ ℤ ⊕ Pic C, Num X ≅ ℤ² on the classes of S₀, F, with S₀·F = 1 and F² = 0. | Transitive only (`Geometry/RuledSurfaceNumerics`, `Geometry/RuledProjectiveLineBaseUnimodular`, `Geometry/RuledFiberOriginalPullback`) |
| H10 | `Hartshorne.surface_hodge_index_literal` | `Literature/Hartshorne/SurfaceHodgeIndex.lean` | Hartshorne V Theorem 1.9, p. 364 | Hodge index: H ample, D ≢ 0 numerically, D·H = 0 ⇒ D² < 0. | Transitive only (`Geometry/SurfaceHodgeIndexProved`) |
| H11 | `Hartshorne.surface_nakai_moishezon_literal` | `Literature/Hartshorne/SurfaceNakaiMoishezon.lean` | Hartshorne V Theorem 1.10, p. 365 | Nakai–Moishezon: D is ample iff D² > 0 and D·C > 0 for every irreducible curve C. | Transitive only (`Geometry/SurfaceNakaiMoishezonProved`) |
| H12 | `Hartshorne.surface_riemannRoch_literal` | `Literature/Hartshorne/SurfaceRiemannRoch.lean` | Hartshorne V Theorem 1.6, p. 362 | Riemann–Roch for surfaces: h⁰(D) − h¹(D) + h⁰(K − D) equals the Riemann–Roch number of D (½·D·(D − K) + 1 + p_a, as encoded by `rrNumber`). | §6, Lemma 6.1 and §7, Lemma 7.4 (`Geometry/SurfaceRiemannRochProved` imported by `S06/SquareOneAdjoint`, `S07/BisectionAdjoint`) |
| S1 | `Stacks.affine_morphism_cohomology_literal` | `Literature/Stacks/AffineMorphismCohomology.lean` | Stacks 089W, Lemma 30.2.4, rev. 540451b3 | For an affine morphism f and quasi-coherent M, Hⁿ(Y, f\*M) ≅ Hⁿ(X, M), naturally in M. | Transitive only (`Geometry/OriginalQuadraticCanonicalIntersections`, `Geometry/OriginalQuadraticCoverEuler`, `Geometry/AffineCohomologyLiteralUse`) |
| S2 | `Stacks.blowupRegularPoint_literal` | `Literature/Stacks/BlowupRegularPointAdmitted.lean` (statement: `Literature/BlowupExceptionalLiterals.lean`) | Stacks 0AGQ (Lemma 54.3.1, quoted) / 0AGR / 0C5P; Hartshorne V.3.1 | The exceptional fibre of the blowup of a regular projective surface at a closed point is P¹ over k and its conormal sheaf has degree 1 (E ≅ P¹, E² = −1). | §4, Thm 4.6 terminal case (`Main/Final` → `S04.hasPointBlowups_of_literal`) |
| S3 | `Stacks.closed_point_blowups_dominate_proper_literal` | `Literature/StacksPointBlowupDomination.lean` | Stacks 0AHI, resolve.tex 928–941, commit a04446e5 | A proper morphism to a Noetherian scheme that is an isomorphism away from finitely many regular 2-dimensional closed points is dominated by a finite sequence of point blowups over those points. | Transitive only (`Geometry/ProperBirationalSurfacePointBlowupDomination`) |
| S4 | `Stacks.field_isJ2` | `Literature/Stacks/FieldJ2.lean` (defs: `Literature/Definitions/J2.lean`) | Stacks 07PJ item (1), commit 540451b3; defs 07P7, 00KU | Every field is J-2: every finite-type algebra over a field has open regular locus. | Transitive only (`Geometry/FiniteTypeSurfaceFiniteness`, `Geometry/SurfaceFiniteness`, `Geometry/IntegralRegularClosedPoint`) |
| S6 | `Stacks.properCohomology_finite` | `Literature/Stacks/ProperCohomologyFinite.lean` | Stacks 02O6, rev. 540451b3 | Cohomology of a coherent sheaf on a scheme proper over a Noetherian ring A is a finitely generated A-module in every degree. | Transitive only (`AdmissionProbe/ProperCohomologyConsumers`, `Geometry/ProperAffineSectionsFinite`) |
| S7 | `Stacks.properFlat_fiberEuler_literal` | `Literature/Stacks/ProperFlatFiberEuler.lean` | Stacks Lemma 36.32.2, Tag 0B9T, rev. 540451b3, perfect.tex 7960–7983 | For a proper finitely presented morphism and a finitely presented module flat over the base, the fibrewise Euler characteristic is locally constant and commutes with base change. | Transitive only (`Geometry/SquareZeroFamilyEulerBaseChange`, `Geometry/SquareZeroFamilyEuler`) |
| S8 | `Stacks.proper_curve_pullback_degree_literal` | `Literature/ProperCurvePullbackDegreeLiteral.lean` | Stacks 0AYZ (with 0AYR, 02NY) | For a nonconstant map f : C → D of integral proper curves and locally free E of rank n on D, deg f\*E = [K(C):K(D)]·deg E (Euler-characteristic degrees). | Transitive only (`Geometry/BirationalProjectionDegree`, `Geometry/ProperBirationalCurvePullbackDegree`) |
| S9 | `Stacks.proper_curve_tensor_degree_literal` | `Literature/Stacks/CurveTensorDegreeLiteral.lean` | Stacks Lemma 33.44.7, tag 0AYX; Def. 33.44.1, tag 0AYR; varieties.tex rev. 540451b3, lines 9475–9488, 9717–9733 | On a proper scheme of dimension ≤ 1 over a field, deg(E ⊗ V) = n·deg V + m·deg E for locally free E, V of ranks n, m. | Datum and §1 (`Geometry/NumericalEquivalence` imported by `Datum/AnticanonicalDegrees`, `S01/Examples`) |
| S10 | `Stacks.regularLocal_isUFD` | `Literature/Stacks/RegularLocalUFD.lean` | Stacks 0AG0, rev. 540451b3; 034S (domain), 00KU (regular local) | A regular local ring is a domain and a unique factorisation domain. | Transitive only (`Geometry/RegularLocalUFD`) |
| S11 | `Stacks.regular_smooth_loci_perfect_literal` | `Literature/RegularSmoothLociLiteral.lean` | Stacks 0B8X, Lemma 33.25.8, rev. a04446e5 | For a reduced scheme locally of finite type over a perfect field, the smooth locus equals the regular locus and is open and dense. | §2, Lemma 2.5 and §3 (`Geometry/RegularSurfaceSmoothLiteralUse` imported by `S02/SquareDegree`, `S03/NefThresholdCore`) |
| S12 | `Stacks.smooth_standardSmooth_cover_literal` | `Literature/SmoothStandardCoverLiteral.lean` | Stacks 00TA, first cover assertion of Lemma 10.137.9, rev. a04446e5 | A smooth ring map R → S admits a cover by principal localisations S_g on which R → S_g is standard smooth. | §2, Lemma 2.5 and §3 (same consumer as S11) |
| S13 | `Stacks.steinFactorization_noetherian_literal` | `Literature/SteinFactorizationNoetherian.lean` (statement: `Literature/SteinFullStatement.lean`) | Stacks 03H0 with relative normalisation as in 035H, rev. 540451b3 | Stein factorisation: a proper morphism to a locally Noetherian scheme factors as a proper morphism with geometrically connected fibres and O_T = f'\*O_X followed by a finite morphism; T is the relative Spec of f\*O_X and the relative normalisation. | §3, Lemma 3.2 (`Geometry/KltSquareZeroPencilStein` imported by `S03/RulingFibers`); §2, Thm 2.6 (`S02/AnticanonicalContraction` → `Geometry/ProperSteinConnected` → `Geometry/SteinGeometricConnected`) |
| L1 | `Stacks.lipman_resolution_of_normal_completions_literal` | `Literature/LipmanResolutionLiteral.lean` | Stacks 0BGP, Theorem 54.14.5, (4) ⇒ (2) | An integral Noetherian surface whose normalisation is finite, has finitely many non-regular points, and has normal completed local rings there, admits a proper birational morphism from a regular integral locally Noetherian scheme (a resolution). | Transitive only (`Geometry/GeneralMinimalResolutionExistence`) |
| K1 | `Keel.semiampleness_completeSystem_literal` | `Literature/KeelCompleteSystem.lean` | Keel, Ann. Math. 149 (1999) 253–286, Theorem 0.2, p. 254; defs 0.0–0.1 pp. 253–254; conventions p. 259 | In characteristic p > 0, a nef line bundle on a projective scheme is semiample iff its restriction to the exceptional locus is semiample. | §2, Thm 2.6 (`S02/AnticanonicalContraction`, via `Geometry/NefPositiveSquareKeelRestriction`) |
| Z1 | `Zariski.closedPoint_normal_completion_literal` | `Literature/ZariskiNormalCompletion.lean` | Zariski, Ann. Inst. Fourier 2 (1950), Theorem 2, p. 162 | At a closed point of an integral affine variety over a field where the local ring is integrally closed, the maximal-ideal completion is a local integrally closed domain. | Transitive only (`Geometry/SingularStalkCompletionZariski`, `Geometry/GeneralMinimalResolutionExistence`) |
| T1 | `Tanaka.contraction_44_instance` | `Literature/Tanaka/ContractionTheorem.lean` | Tanaka, *Minimal model program for excellent surfaces*, AIF 68 (2018) no. 1, 345–376, Theorem 4.4, p. 365 | A K_S-negative extremal ray of the closed cone of curves of a regular projective surface over an algebraically closed field is contracted by a morphism to a projective scheme Y with f\*O_S = O_Y, contracting exactly the curves in the ray, and ρ(Y) = ρ(S) − 1. | §3 (`S03/NefThresholdCore`, one application at line 454) |

---

## Hartshorne, *Algebraic Geometry* (GTM 52, Springer 1977)

Eleven docstrings share the scan pin "softcover reprint, DOI 10.1007/978-1-4757-3849-0, SHA-256
55cee9c7…"; H1, H5, H8, H9 give only a theorem number.

### H1. `KltDP.Literature.Hartshorne.castelnuovo_contraction_literal`

* **File.** `Literature/HartshorneCastelnuovoLiteral.lean`.
* **Published source.** Docstring gives: "The complete Hartshorne Algebraic Geometry V.5.7 criterion,
  printed414." (no edition/DOI/SHA in this file; "printed414" sic).
* **Plain statement.** On a regular projective surface S over an algebraically closed field, a prime
  curve E isomorphic to P¹ over k with E² = −1 is the exceptional curve of the blowup of a regular
  projective surface T at a closed point z: there is b : S → T over k identifying S with the point
  blowup of T at z and E with its exceptional fibre (Castelnuovo's contractibility criterion).
* **Lean signature.**
  ```lean
  axiom castelnuovo_contraction_literal
      {k : Type u} [Field k] [IsAlgClosed k] :
        ∀ (S : NormalProjectiveSurface k)
          (hregular : ∀ s : S.Point, RegularPoint S.toScheme s) (E : S.PrimeCurve),
          (∃ eP : E.toScheme ≅ projectiveSpace k 1,
            eP.hom ≫ projectiveSpaceToSpec k 1 = E.toSpec) →
          E.selfIntersectionNumber hregular = -1 →
          ∃ (T : NormalProjectiveSurface k)
            (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
            (b : S.toScheme ⟶ T.toScheme) (z : T.Point)
            (c : PointBlowupChart T.toScheme z) (e : S.toScheme ≅ c.scheme),
            b ≫ T.structureMorphism = S.structureMorphism ∧
            e.hom ≫ c.projection = b ∧
            ∃ θ : E.toScheme ≅ PointBlowupGluing.globalCenterFiber c.j c.q c.isClosed,
              θ.hom ≫ PointBlowupGluing.globalCenterFiberι c.j c.q c.isClosed =
                E.inclusion ≫ e.hom
  ```
* **Instance/specialisation notes.** "The chapter's surface conventions are retained. The original
  exceptional curve is identified with the actual point-blowup fiber as a scheme. See the separate
  root admission decision and original-object dictionary." (The decision file is not in the lane tree.)
* **Consumers.** `Geometry/GeneralMinimalResolutionExistence` (1), `Geometry/ActualFiniteDisjointContractions` (1).
  No Manuscript module imports either directly: transitive only.

### H2. `KltDP.Literature.Hartshorne.hasContractionLifts_instance` —

* **File.** `Literature/Hartshorne/StrictTransformInstance.lean`; the referenced statement
  `KltDP.Manuscript.S04.HasContractionLifts` / `ContractionLifts` is in
  `Manuscript/S04/IsolatedNodeExchangeTerminal.lean`.
* **Published source.** Docstring gives: Hartshorne, *Algebraic Geometry*, GTM 52: Proposition V.3.6
  (quoted: "Let C be an effective divisor on X, P ∈ X a point of multiplicity r on C, π : X̃ → X the
  monoidal transformation of X at P, C̃ the strict transform. Then π\*C = C̃ + rE."); the definition of
  strict transform before V.3.6 / Corollary II.7.15; the multiplicity definition "V.3, p. 388";
  Proposition II.7.13(a)/II.7.14; Proposition V.5.3 / Castelnuovo V.5.7.
* **Plain statement.** For every contraction b : S → T of a (−1)-curve E between regular projective
  surfaces over an algebraically closed field, strict transforms exist: each prime curve Q of T has a
  strict transform Q̃ on S with b(Q̃) = Q; every prime curve of S other than E is such a strict
  transform; b\*Q = Q̃ + m·E as Cartier divisors, where m is the multiplicity of Q at the centre;
  m = 0 iff Q misses the centre (m > 0 if it meets it); and Q̃ ≅ Q over k whenever m ≤ 1.
* **Lean signature.**
  ```lean
  axiom hasContractionLifts_instance (k : Type u) [Field k] [IsAlgClosed k] :
      KltDP.Manuscript.S04.HasContractionLifts k
  ```
  Referenced statement (verbatim from `Manuscript/S04/IsolatedNodeExchangeTerminal.lean`):
  ```lean
  structure ContractionLifts {k : Type u} [Field k] [IsAlgClosed k]
      {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme} {E : S.PrimeCurve}
      (hb : IsContraction S T b E) (hS : ∀ s : S.Point, RegularPoint S.toScheme s) where
    lift : T.PrimeCurve → S.PrimeCurve
    mult : T.PrimeCurve → ℕ
    image_lift : ∀ Q : T.PrimeCurve, b.base '' (lift Q : Set S.toScheme) = (Q : Set T.toScheme)
    lift_surj : ∀ Q' : S.PrimeCurve, Q' ≠ E → ∃ Q : T.PrimeCurve, lift Q = Q'
    pullback_eq : ∀ Q : T.PrimeCurve,
      letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
      DominantCartierPullback.pullbackHom b (T.primeCurveCartier hb.regular Q) =
        S.primeCurveCartier hS (lift Q) + (mult Q : ℤ) • S.primeCurveCartier hS E
    mult_eq_zero : ∀ Q : T.PrimeCurve,
      Disjoint (Q : Set T.toScheme) (b.base '' (E : Set S.toScheme)) → mult Q = 0
    mult_pos : ∀ Q : T.PrimeCurve,
      ((Q : Set T.toScheme) ∩ b.base '' (E : Set S.toScheme)).Nonempty → 0 < mult Q
    lift_iso : ∀ Q : T.PrimeCurve, mult Q ≤ 1 →
      ∃ e : (lift Q).toScheme ≅ Q.toScheme, e.hom ≫ Q.toSpec = (lift Q).toSpec

  def HasContractionLifts (k : Type u) [Field k] [IsAlgClosed k] : Prop :=
    ∀ {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme} {E : S.PrimeCurve}
      (hb : IsContraction S T b E) (hS : ∀ s : S.Point, RegularPoint S.toScheme s),
      IsMinusOneCurve hS E → Nonempty (ContractionLifts hb hS)
  ```
* **Instance/specialisation notes.** "Each field is one of the published statements above, applied to
  b viewed as the monoidal transformation at b(E) (V.5.3); the specialisation of 'point of multiplicity
  r' to the actual intersection-number/disjointness vocabulary is documented on the fields of
  ContractionLifts." In this library a contraction b : S → T of a (−1)-curve E is literally the point blowup of T at the
  centre z = b(E) (`IsContraction` contains `IsPointBlowupAt`); the strict-transform multiplicity
  identification is not proved in `Geometry/PointBlowupPullbackWeil` and is supplied by this axiom.
* **Consumers.** `Manuscript/Main/Final.lean` (2; `isolatedExchangeHyp_all` passes it to
  `S04.isolatedExchangeHyp_of_literal`). Section: §4, Theorem 4.6 in the terminal case d = 1
  (`S04/IsolatedNodeExchangeTerminal`, "manuscript lines 1141–1145 and 1194–1219"), which supplies
  `IsolatedExchangeHyp` to Theorem 7.1.

### H3. `KltDP.Literature.Hartshorne.hurwitz_degreeTwo_projectiveLine_instance` —

* **File.** `Literature/Hartshorne/HurwitzDegreeTwoInstance.lean`.
* **Published source.** Docstring gives: Hartshorne GTM 52, Chapter IV, Corollary 2.4 (Hurwitz;
  quoted "Let f : X → Y be a finite separable morphism of curves. Let n = deg f. Then
  2g(X) − 2 = n·(2g(Y) − 2) + deg R") and Proposition 2.2(b) (quoted "If f is tamely ramified at P,
  then length(Ω_{X/Y})_P = e_P − 1"); "(Also Stacks Project, Tag 0C1B, Riemann–Hurwitz in the
  different form, as cited by the manuscript, source/manuscript.tex lines 2066–2099.)" No page numbers.
* **Plain statement.** Let S be a normal projective surface over an algebraically closed field of
  characteristic p > 2, B a prime curve of S isomorphic to P¹ over k, and g : S → P¹ a k-morphism whose
  restriction to B has degree two. Then at most two closed points of P¹ have a fibre in B consisting of
  a single point (a degree-two map P¹ → P¹ in tame characteristic has at most two ramification points).
* **Lean signature.**
  ```lean
  axiom hurwitz_degreeTwo_projectiveLine_instance {k : Type u} [Field k] [IsAlgClosed k]
      (p : ℕ) [CharP k p] (hp : 2 < p)
      (S : NormalProjectiveSurface k) (B : S.PrimeCurve)
      (e : B.toScheme ≅ projectiveSpace k 1) (he : e.hom ≫ projectiveSpaceToSpec k 1 = B.toSpec)
      (g : S.toScheme ⟶ projectiveSpace k 1) (hg : g ≫ projectiveSpaceToSpec k 1 = S.structureMorphism)
      (hdeg : B.lineDegree (pullbackInvertibleSheaf (B.inclusion ≫ g)
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)) = 2)
      (T : Finset (projectiveSpace k 1))
      (hT : ∀ t ∈ T, IsClosed ({t} : Set (projectiveSpace k 1)) ∧
        ∃ x : S.toScheme, (B : Set S.toScheme) ∩ g.base ⁻¹' {t} = {x}) :
      T.card ≤ 2
  ```
* **Instance/specialisation notes.** X = B, Y = P¹, f = g|_B "of degree two (hdeg: the degree of the
  pullback of O(1) to B is 2; a nonconstant morphism of curves is finite, of this degree)".
  Unformalized specialisation steps, listed "because the intermediate notions (separable degree,
  tameness, ramification index) are not formalized in this library":
  "f is separable: its inseparable degree is a power of p dividing deg f = 2, and p > 2";
  "f is tamely ramified everywhere: every e_P ≤ deg f = 2 < p";
  "g(X) = g(Y) = 0, so Hurwitz gives Σ_P (e_P − 1) = 2";
  "A closed point t ∈ Y whose fibre f^{-1}(t) is a single point x has e_x = deg f = 2
  (Σ_{x ↦ t} e_x = deg f, II.6.9), contributing 1 to the sum."
  "Hence there are at most two closed points t with a singleton fibre — the admitted conclusion, which
  is exactly the count Lemma 7.2 of the manuscript supplies to Theorem 7.5."
* **Consumers.** `Manuscript/S07/HurwitzInput` (2; `riemannHurwitzDegreeTwo_of_instance` discharges the
  `RiemannHurwitzDegreeTwo` hypothesis of `bisectionRamification_count`), `Manuscript/Main/Final` (1,
  docstring). Section: §7, Lemma 7.2 (`S07/BisectionRamification`) → Theorem 7.5 (`S07/TwoContactRuling`).

### H4. `KltDP.Literature.Hartshorne.integral_numerical_group_free_finite_literal`

* **File.** `Literature/Hartshorne/IntegralNumericalGroup.lean`.
* **Published source.** "Hartshorne V Remark 1.9.1"; "GTM52, Springer, first edition 1977 (softcover
  reprint), printed p.364; DOI 10.1007/978-1-4757-3849-0. Full source SHA256: 55cee9c7…".
* **Plain statement.** On an integral, regular, projective surface over an algebraically closed field,
  the group of Weil divisors modulo numerical equivalence is a free abelian group of finite rank.
* **Lean signature.**
  ```lean
  axiom integral_numerical_group_free_finite_literal :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of k))
      (hIntegral : IsIntegral Y) (hprojective : IsProjectiveOverField f)
      (hdimension : topologicalKrullDim Y = 2)
      (hregular : ∀ y : Y, RegularPoint Y y),
      let X := sourceSurface Y f hIntegral hprojective hdimension hregular
      Module.Free ℤ X.IntegralNumericalClassGroup ∧
        Module.Finite ℤ X.IntegralNumericalClassGroup
  ```
* **Instance/specialisation notes.** "This is the complete independent assertion that integral Num is
  free and finitely generated. Both conclusions are retained on the original quotient. It is not a
  substitute for the full algebraic-equivalence Neron-Severi theorem." Decision file cited:
  `hartshorne_numerical_finiteness_admission/ROOT_CANDIDATE_ADMISSION_DECISION.json`.
* **Consumers.** `Geometry/SurfaceNumericalFinitenessProved` (2). That module is imported directly by
  `Manuscript/S02/AnticanonicalContraction`, `S02/ExteriorNullCurves`, `S03/RulingFibers`,
  `S03/NefThresholdCore`, `S03/NefThreshold`: §2 and §3.

### H5. `KltDP.Literature.Hartshorne.minimal_surface_classification_literal`

* **File.** `Literature/Hartshorne/MinimalSurfaceClassification.lean`.
* **Published source.** Docstring gives: "Full published Hartshorne V.6.1 on the original objects." (no
  page, edition, DOI or SHA in this file).
* **Plain statement.** Let X be a regular projective surface over an algebraically closed field that is
  minimal (every birational morphism to a regular projective surface over k is an isomorphism) with
  canonical divisor K (a Cartier divisor whose sheaf is ω_X = ∧²Ω). Then: (a) H⁰(nK) = 0 for all n > 0
  iff H⁰(12K) = 0; (b) H⁰(12K) = 0 iff X is birational over k to P² or X is ruled: there is a regular
  integral curve C over k with a surjective morphism π : X → C all of whose closed fibres are P¹ over
  k, admitting a section.
* **Lean signature.**
  ```lean
  axiom minimal_surface_classification_literal :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (X : NormalProjectiveSurface k)
      (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
      (hminimal :
        ∀ (T : NormalProjectiveSurface k)
          (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
          (b : X.toScheme ⟶ T.toScheme),
          b ≫ T.structureMorphism = X.structureMorphism →
          IsBirational b → IsIso b)
      (K : CartierDivisor X.toScheme)
      (eK : cartierDivisorModule X.toScheme K ≅
        relativeDifferentialExterior X.structureMorphism 2),
      ((∀ n : ℕ, 0 < n →
          cohomologyDimension X.structureMorphism
            (cartierDivisorModule X.toScheme (n • K)) 0 = 0) ↔
        cohomologyDimension X.structureMorphism
          (cartierDivisorModule X.toScheme (12 • K)) 0 = 0) ∧
      (cohomologyDimension X.structureMorphism
          (cartierDivisorModule X.toScheme (12 • K)) 0 = 0 ↔
        (Scheme.BirationalOver X.structureMorphism (projectiveSpaceToSpec k 2) ∨
          ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)),
            IsIntegral C ∧ LocallyOfFiniteType c ∧ QuasiCompact c ∧ IsSeparated c ∧
            topologicalKrullDim C = 1 ∧
            (∀ y : C, RegularPoint C y) ∧
            ∃ π : X.toScheme ⟶ C,
              π ≫ c = X.structureMorphism ∧
              Function.Surjective π.base ∧
              (∀ y : C, IsClosed ({y} : Set C) →
                ∃ e : π.fiber y ≅ projectiveSpace k 1,
                  e.hom ≫ projectiveSpaceToSpec k 1 =
                    π.fiberι y ≫ X.structureMorphism) ∧
              ∃ σ : C ⟶ X.toScheme, σ ≫ π = 𝟙 C))
  ```
* **Instance/specialisation notes.** Only: "Isolated candidate bound by ROOT_SCOPE_DECISION and
  ROOT_CANDIDATE_SOURCE_DECISION. No production registry activation is performed by this file."
* **Consumers.** `Geometry/HartshorneClassificationLiteralUse` (1). Transitive only.

### H6. `KltDP.Literature.Hartshorne.nonsingular_complete_surface_projective_literal`

* **File.** `Literature/Hartshorne/SurfaceProjectivity.lean`.
* **Published source.** "Hartshorne, Algebraic Geometry, GTM 52, Springer, first edition 1977, II Remark
  4.10.2(b), printed p.105. The selected scan is the softcover reprint, DOI 10.1007/978-1-4757-3849-0,
  SHA-256 55cee9c7…"; "variety/completeness definitions on p.105, regular-stalk convention on
  pp.32/130, and projective embedding definition on p.103".
* **Plain statement.** Every nonsingular complete surface over an algebraically closed field (integral,
  separated, of finite type, proper, regular at every point, of dimension 2) is projective: it admits
  a closed immersion into some Pⁿ over k.
* **Lean signature.**
  ```lean
  axiom nonsingular_complete_surface_projective_literal :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
        (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)),
      IsIntegral X →
      IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
      IsProper f →
      (∀ x : X, RegularPoint X x) →
      topologicalKrullDim X = 2 →
      ∃ (n : ℕ) (i : X ⟶ projectiveSpace k n),
        IsClosedImmersion i ∧ i ≫ projectiveSpaceToSpec k n = f
  ```
* **Instance/specialisation notes.** "This is the entire standalone assertion ... No characteristic
  restriction is added. Specializations to the original constructed surfaces are proved separately."
  Decision file: `hartshorne_surface_admission/ROOT_CANDIDATE_ADMISSION_DECISION.json`.
* **Consumers.** `Examples/FrobeniusProjectivityProved` (3), `Geometry/RegularProperSurface` (1).
  Transitive only.

### H7. `KltDP.Literature.Hartshorne.point_blowup_structure_cohomology_literal`

* **File.** `Literature/Hartshorne/PointBlowupCohomology.lean`.
* **Published source.** "Hartshorne V.3.4 ... Published GTM52, pp387-388, with the surface and
  closed-point conventions on pp357/386."
* **Plain statement.** For the blowup π : X̃ → X of a regular projective surface X over an
  algebraically closed field at a closed point: π\*O_X̃ = O_X, the higher direct images Rⁱπ\*O_X̃
  vanish for i > 0, and Hⁱ(X̃, O_X̃) ≅ Hⁱ(X, O_X) for every i.
* **Lean signature.**
  ```lean
  axiom point_blowup_structure_cohomology_literal :
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k)
    (_hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
    (P : X.Point) (c : PointBlowupChart X.toScheme P),
    IsIso c.projection.c ∧
      (∀ i : ℕ, 0 < i →
        IsZero
          (((schemeAbelianSheafPushforward c.projection).rightDerived i).obj
            ((_root_.SheafOfModules.toSheaf c.scheme.ringCatSheaf).obj
              (_root_.SheafOfModules.unit c.scheme.ringCatSheaf)))) ∧
      (∀ i : ℕ,
        Nonempty
          (((baseFunctor X.structureMorphism i).obj
              (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf)) ≅
            ((baseFunctor (c.projection ≫ X.structureMorphism) i).obj
              (_root_.SheafOfModules.unit c.scheme.ringCatSheaf))))
  ```
* **Instance/specialisation notes.** "All three clauses and all original base-field actions are
  retained. Higher direct image zero is represented on the actual underlying abelian sheaf, using the
  full Stacks01F1 dictionary. No exactness on all sheaves, selected canonical-map normalization, or
  characteristic restriction is asserted." Review recorded in `point_blowup_cohomology_reuse_20260915`.
* **Consumers.** `Geometry/PointBlowupSequenceCohomologyLiteralUse` (4),
  `Geometry/PointBlowupCohomologyLiteralUse` (3). Transitive only.

### H8. `KltDP.Literature.Hartshorne.ruled_surface_genus_literal`

* **File.** `Literature/Hartshorne/RuledSurfaceGenus.lean`.
* **Published source.** Docstring gives: "Full published Hartshorne V.2.5 on the original objects."
* **Plain statement.** Let X be a regular projective surface over an algebraically closed field ruled
  over a regular integral curve C of genus g (a surjective π : X → C over k with every closed fibre
  P¹ over k and a section). Then χ(O_X) − 1 = −g (i.e. p_a(X) = −g), H⁰(X, ω_X) = 0 (p_g = 0), and
  h¹(X, O_X) = g.
* **Lean signature.**
  ```lean
  axiom ruled_surface_genus_literal :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (X : NormalProjectiveSurface k)
      (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
      (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
      [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
      (hCdim : topologicalKrullDim C = 1)
      (hCreg : ∀ y : C, RegularPoint C y)
      (π : X.toScheme ⟶ C)
      (hbase : π ≫ c = X.structureMorphism)
      (hsurj : Function.Surjective π.base)
      (hfib : ∀ y : C, IsClosed ({y} : Set C) →
        ∃ e : π.fiber y ≅ projectiveSpace k 1,
          e.hom ≫ projectiveSpaceToSpec k 1 =
            π.fiberι y ≫ X.structureMorphism)
      (σ : C ⟶ X.toScheme) (hσ : σ ≫ π = 𝟙 C),
      (eulerCharacteristic X.structureMorphism
          (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) - 1 =
        -(CurveCanonical.genus c : ℤ)) ∧
      (cohomologyDimension X.structureMorphism
          (relativeDifferentialExterior X.structureMorphism 2) 0 = 0) ∧
      (cohomologyDimension X.structureMorphism
          (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 1 =
        CurveCanonical.genus c)
  ```
* **Instance/specialisation notes.** Only: "Isolated candidate bound by ROOT_SCOPE_DECISION and
  ROOT_CANDIDATE_SOURCE_DECISION. No production registry activation is performed by this file."
* **Consumers.** `Geometry/RuledSurfaceNumerics` (2), `Geometry/RuledProjectiveLineBaseCohomology` (1),
  `Geometry/RationalSurfaceStructureCohomology` (1) (also `Geometry/HartshorneRuledLiteralUse`).
  Transitive only.

### H9. `KltDP.Literature.Hartshorne.ruled_surface_picard_literal`

* **File.** `Literature/Hartshorne/RuledSurfacePicard.lean`.
* **Published source.** Docstring gives: "Full published Hartshorne V.2.3 on the original objects."
* **Plain statement.** For X ruled over C as in H8, with a section curve S₀ ≅ C and a fibre curve F
  over a closed point: Pic X ≅ ℤ ⊕ Pic C (the ℤ generated by the class of S₀, Pic C entering by
  pullback along π), Num X ≅ ℤ ⊕ ℤ generated by the classes of S₀ and F, and S₀·F = 1, F² = 0.
* **Lean signature.**
  ```lean
  axiom ruled_surface_picard_literal :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (X : NormalProjectiveSurface k)
      (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
      (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
      [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
      (hCdim : topologicalKrullDim C = 1)
      (hCreg : ∀ y : C, RegularPoint C y)
      (π : X.toScheme ⟶ C)
      (hbase : π ≫ c = X.structureMorphism)
      (hsurj : Function.Surjective π.base)
      (hfib : ∀ y : C, IsClosed ({y} : Set C) →
        ∃ e : π.fiber y ≅ projectiveSpace k 1,
          e.hom ≫ projectiveSpaceToSpec k 1 =
            π.fiberι y ≫ X.structureMorphism)
      (σ : C ⟶ X.toScheme) (hσ : σ ≫ π = 𝟙 C)
      (S₀ : X.PrimeCurve) (e₀ : S₀.toScheme ≅ C)
      (he₀ : e₀.inv ≫ S₀.inclusion = σ)
      (y : C) (hy : IsClosed ({y} : Set C))
      (F : X.PrimeCurve) (eF : F.toScheme ≅ π.fiber y)
      (heF : eF.hom ≫ π.fiberι y = F.inclusion),
      let DS := X.primeCurveCartier hX S₀
      let DF := X.primeCurveCartier hX F
      let PS := cartierPicardHom X.toScheme DS
      let PF := cartierPicardHom X.toScheme DF
      ∃ ePic : (ℤ × Additive C.Pic) ≃+ Additive X.toScheme.Pic,
        ∃ eNum : (ℤ × ℤ) ≃+ X.IntegralNumericalClassGroup,
          (∀ (n : ℤ) (L : Additive C.Pic),
            ePic (n, L) = n • PS + (schemePicardPullbackHom π).toAdditive L) ∧
          (∀ n m : ℤ,
            eNum (n, m) =
              n • X.picardIntegralNumericalMap PS +
              m • X.picardIntegralNumericalMap PF) ∧
          X.intersectionPairing hX DS DF = 1 ∧
          X.intersectionPairing hX DF DF = 0
  ```
* **Instance/specialisation notes.** Only the same two-line registry note as H8.
* **Consumers.** `Geometry/RuledSurfaceNumerics` (1), `Geometry/RuledProjectiveLineBaseUnimodular` (1),
  `Geometry/RuledFiberOriginalPullback` (1) (also `RuledFiberConstancyOrthogonality`,
  `HartshorneRuledLiteralUse`). Transitive only.

### H10. `KltDP.Literature.Hartshorne.surface_hodge_index_literal`

* **File.** `Literature/Hartshorne/SurfaceHodgeIndex.lean`.
* **Published source.** "Hartshorne V Theorem 1.9 ... GTM52, Springer, first edition 1977 (softcover
  reprint), printed p.364; DOI 10.1007/978-1-4757-3849-0. Full source SHA256: 55cee9c7…".
* **Plain statement.** Hodge index theorem: on an integral regular projective surface over an
  algebraically closed field, if H is an ample divisor and D is a divisor not numerically equivalent
  to zero with D·H = 0, then D² < 0.
* **Lean signature.**
  ```lean
  axiom surface_hodge_index_literal :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of k))
      (hIntegral : IsIntegral Y) (hprojective : IsProjectiveOverField f)
      (hdimension : topologicalKrullDim Y = 2)
      (hregular : ∀ y : Y, RegularPoint Y y),
      let X := sourceSurface Y f hIntegral hprojective hdimension hregular
      ∀ H D : X.WeilDivisor,
        AmpleSerre.IsAmple (divisorLine X hregular H) →
        (¬ ∀ E : X.WeilDivisor, divisorPairing X hregular D E = 0) →
        divisorPairing X hregular D H = 0 →
        divisorPairing X hregular D D < 0
  ```
* **Instance/specialisation notes.** "The exact published theorem retains every original integral Weil
  divisor, actual ample H, the all-divisor numerical test, and strict negativity." Decision file:
  `hartshorne_hodge_admission/ROOT_CANDIDATE_ADMISSION_DECISION.json`.
* **Consumers.** `Geometry/SurfaceHodgeIndexProved` (1). Transitive only.

### H11. `KltDP.Literature.Hartshorne.surface_nakai_moishezon_literal`

* **File.** `Literature/Hartshorne/SurfaceNakaiMoishezon.lean`.
* **Published source.** "Hartshorne V Theorem 1.10 ... GTM52 (1977), printed page365. DOI:
  10.1007/978-1-4757-3849-0. Frozen primary PDF SHA256: 55cee9c7…".
* **Plain statement.** Nakai–Moishezon criterion: on an integral regular projective surface over an
  algebraically closed field, a divisor D is ample if and only if D² > 0 and D·C > 0 for every
  irreducible curve C.
* **Lean signature.**
  ```lean
  axiom surface_nakai_moishezon_literal :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of k))
      (hIntegral : IsIntegral Y) (hprojective : IsProjectiveOverField f)
      (hdimension : topologicalKrullDim Y = 2)
      (hregular : ∀ y : Y, RegularPoint Y y),
      let X := sourceSurface Y f hIntegral hprojective hdimension hregular
      ∀ D : X.WeilDivisor,
        AmpleSerre.IsAmple (divisorLine X hregular D) ↔
          0 < divisorPairing X hregular D D ∧
            ∀ C : X.PrimeCurve, 0 < divisorPairing X hregular D (Finsupp.single C 1)
  ```
* **Instance/specialisation notes.** "The entire iff is retained on every original Weil divisor and
  every actual prime curve. All regular integral projective dimension-two surfaces over algebraically
  closed fields are included, in arbitrary characteristic." Review: `hartshorne_nakai_admission`.
* **Consumers.** `Geometry/SurfaceNakaiMoishezonProved` (2). Transitive only.

### H12. `KltDP.Literature.Hartshorne.surface_riemannRoch_literal`

* **File.** `Literature/Hartshorne/SurfaceRiemannRoch.lean`.
* **Published source.** "Hartshorne V Theorem 1.6, the full surface Riemann–Roch formula ... GTM52,
  Springer, first edition1977 (softcover reprint), printed p.362; DOI10.1007/978-1-4757-3849-0.
  Complete source SHA256: 55cee9c7…".
* **Plain statement.** Riemann–Roch on a surface: for any divisor D and any canonical divisor K on an
  integral regular projective surface over an algebraically closed field,
  h⁰(D) − h¹(D) + h⁰(K − D) equals the Riemann–Roch number of D (Hartshorne's right-hand side
  ½·D·(D − K) + 1 + p_a(X), encoded as `rrNumber`, whose definition was not re-verified here).
* **Lean signature.**
  ```lean
  axiom surface_riemannRoch_literal :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of k))
      (hIntegral : IsIntegral Y) (hprojective : IsProjectiveOverField f)
      (hdimension : topologicalKrullDim Y = 2)
      (hregular : ∀ y : Y, RegularPoint Y y),
      let X := sourceSurface Y f hIntegral hprojective hdimension hregular
      ∀ D K : X.WeilDivisor, IsCanonical X hregular K →
        (hDimension X hregular D 0 : ℚ) - (hDimension X hregular D 1 : ℚ) +
          (hDimension X hregular (K - D) 0 : ℚ) = rrNumber X hregular D K
  ```
* **Instance/specialisation notes.** "All original source hypotheses and arbitrary divisors are
  retained. The preceding source definitions of l, s and arithmetic genus are unfolded via
  independently defined scalar cohomology and the actual Euler characteristic." Decision file:
  `hartshorne_rr_admission/ROOT_CANDIDATE_ADMISSION_DECISION.json`.
* **Consumers.** `Geometry/SurfaceRiemannRochProved` (6). That module is imported directly by
  `Manuscript/S06/SquareOneAdjoint` and `Manuscript/S07/BisectionAdjoint`: §6 (Lemma 6.1) and §7
  (Lemma 7.4).

---

## Stacks Project

### S1. `KltDP.Literature.Stacks.affine_morphism_cohomology_literal`

* **File.** `Literature/Stacks/AffineMorphismCohomology.lean`.
* **Published source.** "Stacks 089W ... Lemma 30.2.4 at Stacks revision 540451b3e79a131df8eca4c4187448e49dcb262d."
* **Plain statement.** For an affine morphism of schemes f : X → Y and a quasi-coherent O_X-module M,
  Hⁿ(Y, f\*M) ≅ Hⁿ(X, M) for every n, naturally in M.
* **Lean signature.**
  ```lean
  axiom affine_morphism_cohomology_literal :
    ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsAffineHom f] (n : ℕ),
      ∃ e : ∀ (M : X.Modules), M.IsQuasicoherent →
        H ((schemeModulePushforward f).obj M) n ≃+ H M n,
        ∀ (M N : X.Modules) (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
          (φ : M ⟶ N) (x : H ((schemeModulePushforward f).obj M) n),
          e N hN ((zariskiFunctor Y n).map ((schemeModulePushforward f).map φ) x) =
            (zariskiFunctor X n).map φ (e M hM x)
  ```
* **Instance/specialisation notes.** "All schemes, affine morphisms, quasicoherent coefficients, and
  degrees are retained. The natural family is witnessed by the published canonical Leray comparison.
  This existence statement does not identify a chosen native map as canonical, nor assert exactness on
  all abelian sheaves." Dossier: `affine_morphism_cohomology_source_20260915`.
* **Consumers.** `Geometry/OriginalQuadraticCanonicalIntersections` (4),
  `Geometry/OriginalQuadraticCoverEuler` (3), `Geometry/AffineCohomologyLiteralUse` (3). Transitive only.

### S2. `KltDP.Literature.Stacks.blowupRegularPoint_literal` —

* **File.** `Literature/Stacks/BlowupRegularPointAdmitted.lean`; the statement
  `BlowupRegularPointLiteral k` is the `Prop` structure in
  `Literature/BlowupExceptionalLiterals.lean`.
* **Published source.** Admission file: "Stacks Project Tag 0AGQ (blowing up a regular closed point of a
  regular surface: the exceptional fibre is a projective line over the residue field), Tag 0AGR / 0C5P
  (its conormal sheaf is O(1)); Hartshorne, Algebraic Geometry, Proposition V.3.1". The structure's
  docstring: "Stacks 0AGQ, Lemma 54.3.1" with the verbatim statement ("Let (A, 𝔪, κ) be a regular local
  ring of dimension 2. Let f : X → S = Spec(A) be the blowing up of A in 𝔪 wotj [sic, as served]
  exceptional divisor E. There is a closed immersion r : X → P¹_S over S such that r|_E : E → P¹_κ is
  an isomorphism, O_X(E) = O_X(−1) = r\*O_{P¹}(−1), and C_{E/X} = (r|_E)\*O_{P¹}(1) and
  N_{E/X} = (r|_E)\*O_{P¹}(−1)."); fetch date 2026-09-11 from `https://stacks.math.columbia.edu/tag/<tag>`;
  full record "in laneE/F10_LITERALS.md" (not in the lane tree). Note the two docstrings attribute the
  conormal clause differently (admission file: 0AGR/0C5P; structure docstring: part of 0AGQ =
  Lemma 54.3.1, with 0AGR = Lemma 54.3.2 being the regularity lemma encoded by the *other* structure,
  `BlowupChartRegularLiteral`, which is not an axiom).
* **Plain statement.** Blowing up a regular projective surface over an algebraically closed field at a
  closed point (of an affine chart) produces an exceptional fibre E isomorphic to P¹ over k, whose
  conormal sheaf has degree one on E; equivalently E ≅ P¹ and E² = −1.
* **Lean signature.**
  ```lean
  axiom blowupRegularPoint_literal (k : Type u) [Field k] [IsAlgClosed k] : BlowupRegularPointLiteral k
  ```
  Referenced statement (verbatim from `Literature/BlowupExceptionalLiterals.lean`, with
  `variable (k : Type u) [Field k]`):
  ```lean
  structure BlowupRegularPointLiteral : Prop where
    exceptional_projectiveLine : ∀ (S : NormalProjectiveSurface k) (R : Type u) [CommRing R]
      (j : Spec (CommRingCat.of R) ⟶ S.toScheme) [IsOpenImmersion j] (q : PrimeSpectrum R)
      [q.asIdeal.IsMaximal] (hclosed : IsClosed ({j.base q} : Set S.toScheme)),
      (∀ x : S.Point, RegularPoint S.toScheme x) →
        ∃ e : PointBlowupGluing.globalCenterFiber j q hclosed ≅ projectiveSpace k 1,
          e.hom ≫ projectiveSpaceToSpec k 1 =
              PointBlowupGluing.globalCenterFiberι j q hclosed ≫
                PointBlowupGluing.projection j q hclosed ≫ S.structureMorphism ∧
            eulerCharacteristic (projectiveSpaceToSpec k 1)
                ((schemeModulePullback e.inv).obj
                  (schemeConormalSheaf (PointBlowupGluing.globalCenterFiberι j q hclosed))) -
              eulerCharacteristic (projectiveSpaceToSpec k 1)
                (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) = 1
  ```
* **Instance/specialisation notes.** Admitted exactly in the form of the pre-existing `Prop` structure.
  From the structure docstring: "κ(j.base q) = k because k is algebraically closed and the point is
  closed on a finite-type k-scheme (accepted KltDP.Geometry.closedPointResidueFieldIso), so P¹_κ is
  P¹_k over k"; the conormal clause is "recorded as the Euler difference χ(C_{E/X}) − χ(O_{P¹}) = 1 of
  Stacks 0AYR, which is the degree of O_{P¹}(1). The normal-sheaf clause is the dual statement and is
  not encoded separately; the accepted O_X(E) clause is not used. Specialisation debt: the
  identification of the conormal sheaf I/I² of E with (r|_E)\*O_{P¹}(1) is used only through its
  degree, and the degree of O_{P¹}(1) on P¹ is 1 (accepted KltDP.Geometry.ProjectiveLineDegree.degree)."
* **Consumers.** `Manuscript/Main/Final` (2; `isolatedExchangeHyp_all` → `S04.isolatedExchangeHyp_of_literal`
  → `S04.hasPointBlowups_of_literal`). Section: §4, Theorem 4.6 terminal case ("consumed only through
  KltDP.Manuscript.S04.hasPointBlowups_of_literal ... for the terminal case of Theorem 4.6").

### S3. `KltDP.Literature.Stacks.closed_point_blowups_dominate_proper_literal`

* **File.** `Literature/StacksPointBlowupDomination.lean`.
* **Published source.** "Stacks 0AHI, resolve.tex 928–941, commit a04446e57ec1fbc252a871afcec7752fb2807b14;
  GFDL-1.2-or-later."
* **Plain statement.** Let X be a Noetherian scheme, T a finite set of closed points at which X is
  regular with 2-dimensional local rings, and f : Y → X a proper morphism that is an isomorphism over
  X ∖ T. Then there is a finite sequence of blowups of closed points lying over T, Z → X, which factors
  through f.
* **Lean signature.**
  ```lean
  axiom closed_point_blowups_dominate_proper_literal :
    ∀ (X Y : Scheme.{u}) (f : Y ⟶ X),
      IsNoetherian X →
      ∀ (T : Set X) (hfinite : T.Finite)
        (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X)),
        (∀ x ∈ T, RegularPoint X x) →
        (∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2) →
        IsProper f →
        IsIso (f ∣_ finiteClosedPointComplement X T hfinite hclosed) →
        ∃ (Z : Scheme.{u}) (b : Z ⟶ X),
          SchemePointBlowup.SequenceAway X Tᶜ Z b ∧
          ∃ (g : Z ⟶ Y), g ≫ f = b
  ```
* **Instance/specialisation notes.** "The original arbitrary Noetherian scheme, finite closed set,
  regular dimension-two stalks on that set, and proper morphism are retained. The existing actual Rees
  point blowups form a finite sequence above the original set. This literal supplies no independent
  over-base equation, smoothness, projectivity, discrepancy, or klt conclusion."
* **Consumers.** `Geometry/ProperBirationalSurfacePointBlowupDomination` (1). Transitive only.

### S4. `KltDP.Literature.Stacks.field_isJ2`

* **File.** `Literature/Stacks/FieldJ2.lean`; definitions in `Literature/Definitions/J2.lean`.
* **Published source.** "The Stacks Project Authors, tag 07PJ, item (1), at frozen commit
  540451b3e79a131df8eca4c4187448e49dcb262d: every field is J-2. The J-1/J-2 and regular-local
  definitions are recorded in tags 07P7 and 00KU."
* **Plain statement.** Every field k is a J-2 ring: k is Noetherian and every finite-type k-algebra A
  is J-1, i.e. A is Noetherian and the set of primes at which A is regular (maximal ideal generated by
  dim-many elements) is open in Spec A.
* **Lean signature.**
  ```lean
  axiom field_isJ2 (k : Type u) [instField : Field k] :
      KltDP.Literature.J2Ring.{u, v} k
  ```
  Referenced definitions (verbatim from `Literature/Definitions/J2.lean`):
  ```lean
  def generatorRegularLocus (R : Type u) [CommRing R] : Set (PrimeSpectrum R) :=
    {p | Geometry.RegularLocalByGenerators (Localization.AtPrime p.asIdeal)}
  def J1Ring (R : Type u) [CommRing R] : Prop :=
    IsNoetherianRing R ∧ IsOpen (generatorRegularLocus R)
  def J2Ring (R : Type u) [CommRing R] : Prop :=
    IsNoetherianRing R ∧
      ∀ (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A], J1Ring A
  ```
* **Instance/specialisation notes.** "The literal field case of Stacks 07PJ(1), with independent ring
  universes." The J2 file: "These predicates impose no domain, dimension, characteristic, or geometric
  assumptions beyond the published definitions."
* **Consumers.** `Geometry/FiniteTypeSurfaceFiniteness` (3), `Geometry/SurfaceFiniteness` (2),
  `Geometry/IntegralRegularClosedPoint` (1) (also `Geometry/IntegralFiniteTypeRegularLocus`).
  Transitive only.

### S6. `KltDP.Literature.Stacks.properCohomology_finite`

* **File.** `Literature/Stacks/ProperCohomologyFinite.lean`.
* **Published source.** "Literal statement candidate for Stacks Project Tag 02O6, revision
  540451b3e79a131df8eca4c4187448e49dcb262d." (No lemma number or file/line range given.)
* **Plain statement.** For a proper morphism X → Spec A with A a Noetherian ring and M a coherent
  O_X-module, every cohomology group Hⁿ(X, M) is a finitely generated A-module.
* **Lean signature.**
  ```lean
  axiom properCohomology_finite
      {A : Type u} [instCommRing : CommRing A] [instNoetherianRing : IsNoetherianRing A]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [instProper : IsProper f]
      (M : X.Modules) [instCoherent : KltDP.Geometry.IsCoherentModule M] (n : ℕ) :
      letI := KltDP.Geometry.ModuleCohomology.baseRingRightDerivedModule f M n
      Module.Finite A (KltDP.Geometry.ModuleCohomology.rightDerivedH M n)
  ```
* **Instance/specialisation notes.** "The cohomology model is original abelian-derived global sections
  with the independently defined action of the original base ring. Published Tag 01F1 and its
  common-resolution proof identify this mathematical cohomology with the module-sheaf formulation.
  That semantic identification is documented in the admission dossier; no separate module-derived Lean
  comparison is claimed." The docstring ends "INACTIVE TEMPLATE. Its declaration is not currently
  admitted or activated." — stale: the axiom is in the main theorem's dependency list.
* **Consumers.** `AdmissionProbe/ProperCohomologyConsumers` (5; a self-described "INACTIVE consumers"
  probe file), `Geometry/ProperAffineSectionsFinite` (1; "The accepted Stacks 02O6 theorem gives finite
  original derived H0 of a coherent module over the original Noetherian base ring"). Transitive only.

### S7. `KltDP.Literature.Stacks.properFlat_fiberEuler_literal`

* **File.** `Literature/Stacks/ProperFlatFiberEuler.lean`.
* **Published source.** "Stacks Project Lemma 36.32.2, Tag 0B9T, full statement. Revision
  540451b3e79a131df8eca4c4187448e49dcb262d, perfect.tex lines 7960-7983."
* **Plain statement.** For a proper, locally finitely presented morphism f : X → Y and a finitely
  presented O_X-module M flat over Y, the function y ↦ χ(X_y, M_y) (Euler characteristic on the fibre)
  is locally constant on Y and is compatible with arbitrary base change T → Y.
* **Lean signature.**
  ```lean
  axiom properFlat_fiberEuler_literal
      {X Y : Scheme.{u}} (f : X ⟶ Y)
      [IsProper f] [LocallyOfFinitePresentation f]
      (M : X.Modules) [M.IsFinitePresentation]
      (hflat : KltDP.Geometry.IsFlatModuleOver f M) :
      IsLocallyConstant (KltDP.Geometry.fiberEuler f M) ∧
        ∀ (T : Scheme.{u}) (g : T ⟶ Y) (t : T),
          KltDP.Geometry.fiberEuler (pullback.snd f g)
            ((KltDP.Geometry.schemeModulePullback (pullback.fst f g)).obj M) t =
          KltDP.Geometry.fiberEuler f M (g.base t)
  ```
  (The file also installs a `local instance sourceEulerOverLocallyBijective` used by the statement.)
* **Instance/specialisation notes.** "Both local constancy and unrestricted numerical base-change
  compatibility are retained. Independently reviewed native definitions and the exact full telescope
  are recorded in the adjacent ROOT_CANDIDATE_ADMISSION_DECISION.json dossier."
* **Consumers.** `Geometry/SquareZeroFamilyEulerBaseChange` (1), `Geometry/SquareZeroFamilyEuler` (1).
  Transitive only.

### S8. `KltDP.Literature.Stacks.proper_curve_pullback_degree_literal`

* **File.** `Literature/ProperCurvePullbackDegreeLiteral.lean`.
* **Published source.** Docstring gives: "The complete Stacks0AYZ degree formula for nonconstant proper
  curve maps, with the finite-rank Euler degree of0AYR unfolded on the original sheaves. The field
  degree of02NY uses the original generic stalk map." (No revision/commit recorded in this file.)
* **Plain statement.** For a nonconstant morphism f : C → D of integral proper curves over a field k
  and a locally free O_D-module E of rank n, deg(f\*E) = [K(C) : K(D)] · deg(E), where the degree of a
  rank-n sheaf is χ(E) − n·χ(O).
* **Lean signature.**
  ```lean
  axiom proper_curve_pullback_degree_literal :
      ∀ {k : Type u} [instField : Field k]
        {C D : Scheme.{u}} [instIntegralC : IsIntegral C] [instIntegralD : IsIntegral D]
        (σC : C ⟶ Spec (CommRingCat.of k)) [instProperC : IsProper σC]
        (σD : D ⟶ Spec (CommRingCat.of k)) [instProperD : IsProper σD]
        (hdimC : topologicalKrullDim C = 1) (hdimD : topologicalKrullDim D = 1)
        (f : C ⟶ D) (hf : f ≫ σD = σC)
        (hnonconstant : ¬ ∃ y : D, ∀ x : C, f.base x = y)
        (E : D.Modules) (n : ℕ) (hE : IsLocallyFreeOfRankOn D E n),
        letI : IsNoetherian D := isNoetherian_of_finiteType_toSpec σD
        letI : GenericPointPreserving f :=
          ProperNonconstantCurve.genericPointPreserving_of_nonconstant_base
            f hdimD.le hnonconstant
        letI : Algebra D.functionField C.functionField :=
          (functionFieldMap f).hom.toAlgebra
        eulerCharacteristic σC ((schemeModulePullback f).obj E) -
            (n : ℤ) * eulerCharacteristic σC (_root_.SheafOfModules.unit C.ringCatSheaf) =
          (Module.finrank D.functionField C.functionField : ℤ) *
            (eulerCharacteristic σD E -
              (n : ℤ) * eulerCharacteristic σD (_root_.SheafOfModules.unit D.ringCatSheaf))
  ```
* **Instance/specialisation notes.** As quoted above; "Root admission and the frozen source/definition
  dictionary are separate."
* **Consumers.** `Geometry/BirationalProjectionDegree` (2), `Geometry/ProperBirationalCurvePullbackDegree` (1).
  Transitive only.

### S9. `KltDP.Literature.Stacks.proper_curve_tensor_degree_literal`

* **File.** `Literature/Stacks/CurveTensorDegreeLiteral.lean`.
* **Published source.** "Stacks Project, Lemma 33.44.7, tag 0AYX; degree is Definition 33.44.1, tag
  0AYR. Preserved varieties.tex at revision 540451b3e79a131df8eca4c4187448e49dcb262d, lines 9475-9488
  and 9717-9733. The source and its GFDL license are bound in this proposal's manifest."
* **Plain statement.** On a proper scheme of dimension at most one over a field, for locally free
  sheaves E and V of ranks n and m, deg(E ⊗ V) = n·deg(V) + m·deg(E) (degrees as Euler differences).
* **Lean signature.**
  ```lean
  axiom proper_curve_tensor_degree_literal
      {k : Type u} [instField : Field k] {Y : Scheme.{u}}
      (f : Y ⟶ Spec (CommRingCat.of k)) [instProper : IsProper f]
      (hdim : topologicalKrullDim Y ≤ 1) (E V : Y.Modules) (n m : ℕ)
      (hE : IsLocallyFreeOfRankOn Y E n) (hV : IsLocallyFreeOfRankOn Y V m) :
      letI := Scheme.Modules.monoidalCategory Y
      finiteRankDegree f hdim (E ⊗ V) (n * m)
          (KltDP.SheafOfModules.IsLocallyFreeOfRank.tensor (X := Y) hE hV) =
        (n : ℤ) * finiteRankDegree f hdim V m hV +
        (m : ℤ) * finiteRankDegree f hdim E n hE
  ```
* **Instance/specialisation notes.** "The entire finite-rank statement is retained over every field and
  proper scheme of dimension at most one. The actual tensor product has rank n\*m by the separately
  proved local product-basis theorem, used explicitly below. The imported ordinary interpretation
  establishes that each degree is the published finite Euler difference, subject to its separate
  admission audit." The docstring is headed "INACTIVE TEXT ONLY. The prospective declaration below has
  not been admitted or installed in production." — stale: the axiom is in the main theorem's dependency
  list (the adapter `Literature/Stacks/CurveTensorDegree.lean` unfolds it to a plain Euler identity).
* **Consumers.** `Literature/Stacks/CurveTensorDegree` (adapter theorem `proper_curve_tensor_degree`),
  `Geometry/NumericalEquivalence` (1), `Geometry/CartierEulerPairingDegree` (1).
  `Geometry/NumericalEquivalence` is imported directly by `Manuscript/Datum/AnticanonicalDegrees` and
  `Manuscript/S01/Examples`: the resolution-datum vocabulary and §1 (Theorem 1.2).

### S10. `KltDP.Literature.Stacks.regularLocal_isUFD`

* **File.** `Literature/Stacks/RegularLocalUFD.lean`.
* **Published source.** "Literal statement of Stacks Project, Tag 0AG0, at revision
  540451b3e79a131df8eca4c4187448e49dcb262d. The UFD conclusion includes the domain property (Tag 034S).
  The generator definition of regular local ring is Tag 00KU."
* **Plain statement.** A regular local ring (Noetherian local ring whose maximal ideal is generated by
  dim-many elements) is a domain and a unique factorisation domain.
* **Lean signature.**
  ```lean
  axiom regularLocal_isUFD
      (R : Type u) [instCommRing : CommRing R] [instLocalRing : IsLocalRing R]
      (hregular : KltDP.Geometry.RegularLocalByGenerators R) :
      ∃ hDomain : IsDomain R,
        letI : IsDomain R := hDomain
        UniqueFactorizationMonoid R
  ```
* **Instance/specialisation notes.** None beyond the tag notes above.
* **Consumers.** `Geometry/RegularLocalUFD` (1). Transitive only.

### S11. `KltDP.Literature.Stacks.regular_smooth_loci_perfect_literal`

* **File.** `Literature/RegularSmoothLociLiteral.lean`.
* **Published source.** "Stacks 0B8X, full Lemma 33.25.8, frozen revision
  a04446e57ec1fbc252a871afcec7752fb2807b14."
* **Plain statement.** For a reduced scheme X locally of finite type over a perfect field k, the locus
  where X → Spec k is smooth coincides with the regular locus of X, and this locus is open and dense.
* **Lean signature.**
  ```lean
  axiom regular_smooth_loci_perfect_literal
      (k : Type u) [Field k] [PerfectField k]
      (X : Scheme.{u}) [AlgebraicGeometry.IsReduced X]
      (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
      let L : Set X := {x |
        KltDP.Geometry.AffineSmoothLocalizationTransport.algebraSmoothAt f x}
      let G : Set X := {x |
        KltDP.Geometry.RegularLocalByGenerators (X.presheaf.stalk x)}
      L = G ∧ IsOpen L ∧ Dense L
  ```
* **Instance/specialisation notes.** "Native smoothness uses the original affine ring maps. The regular
  locus is the literal maximal-ideal-generator definition; openness and density are retained."
* **Consumers.** `Geometry/RegularSurfaceSmoothLiteralUse` (2), imported directly by
  `Manuscript/S02/SquareDegree` and `Manuscript/S03/NefThresholdCore`: §2 (Lemma 2.5) and §3.

### S12. `KltDP.Literature.Stacks.smooth_standardSmooth_cover_literal`

* **File.** `Literature/SmoothStandardCoverLiteral.lean`.
* **Published source.** "Stacks 00TA, the individually stated FIRST cover assertion of Lemma 10.137.9,
  frozen revision a04446e57ec1fbc252a871afcec7752fb2807b14."
* **Plain statement.** If R → S is a smooth ring map, there are elements g ∈ S generating the unit
  ideal such that each composite R → S → S_g is standard smooth.
* **Lean signature.**
  ```lean
  axiom smooth_standardSmooth_cover_literal
      (R S : Type u) [CommRing R] [CommRing S] (φ : R →+* S)
      (hsmooth :
        letI : Algebra R S := φ.toAlgebra
        Algebra.Smooth R S) :
      ∃ T : Set S, Ideal.span T = ⊤ ∧
        ∀ g ∈ T, RingHom.IsStandardSmooth
          ((algebraMap S (Localization.Away g)).comp φ)
  ```
* **Instance/specialisation notes.** "This entry authorizes the actual standard-open localization cover
  only. The separate syntomic conclusion is not represented or supplied."
* **Consumers.** `Geometry/RegularSurfaceSmoothLiteralUse` (2): §2 (Lemma 2.5) and §3, as for S11.

### S13. `KltDP.Literature.Stacks.steinFactorization_noetherian_literal`

* **File.** `Literature/SteinFactorizationNoetherian.lean`; the statement
  `Stein03H0.FullStatement` is in `Literature/SteinFullStatement.lean`.
* **Published source.** "Full Stacks 03H0, with relative normalization as in 035H, revision
  540451b3e79a131df8eca4c4187448e49dcb262d." Decision:
  `stein_full_source_admission_review_20260914/ROOT_CANDIDATE_ADMISSION_DECISION.json`; source review
  `stein_full_source_admission_review_20260914/FULL_SOURCE_REVIEW.md`.
* **Plain statement.** Stein factorisation: every proper morphism f : X → S to a locally Noetherian
  scheme factors as X → T → S where X → T is proper with geometrically connected fibres and
  O_T = f'\*O_X, and T → S is finite; moreover T is the relative Spec of f\*O_X and also the relative
  normalisation of S in X, compatibly with the maps.
* **Lean signature.**
  ```lean
  axiom steinFactorization_noetherian_literal : Stein03H0.FullStatement.{u}
  ```
  Referenced statement (verbatim from `Literature/SteinFullStatement.lean`):
  ```lean
  def FullStatement : Prop :=
    ∀ (S X : Scheme.{u}) [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f],
      ∃ (T : Scheme.{u}) (f' : X ⟶ T) (π : T ⟶ S),
        f' ≫ π = f ∧
        IsProper f' ∧
        (∀ (K : Type u) [Field K] (q : Spec (CommRingCat.of K) ⟶ T),
          ConnectedSpace (pullback f' q : Scheme.{u})) ∧
        IsFinite π ∧
        IsIso f'.c ∧
        (∃ eR : T ≅ relativeSpec f,
          f' ≫ eR.hom = fromSource f ∧
          eR.hom ≫ toBase f = π) ∧
        (∃ eN : T ≅ normalization f,
          f' ≫ eN.hom = toNormalization f ∧
          eN.hom ≫ normalizationToBase f = π)
  ```
* **Instance/specialisation notes.** "retaining all five published clauses on one original
  factorization"; "The original locally Noetherian base and proper morphism are arbitrary, including
  empty and nonreduced schemes. The two output isomorphisms preserve the original source and base maps
  of the constructed relative spectrum and relative normalization."
* **Consumers.** `Geometry/SteinGeometricConnected` (1), `Geometry/ProperNonconstantCurveFinite` (1),
  `Geometry/ProperBirationalConnectedFibers` (1), `Geometry/KltSquareZeroPencilStein` (1).
  `KltSquareZeroPencilStein` is imported directly by `Manuscript/S03/RulingFibers` (§3, Lemma 3.2);
  `Manuscript/S02/AnticanonicalContraction` (§2, Theorem 2.6, "the Stein factorisation of the
  complete-system map") imports `Geometry/ProperSteinConnected`, which imports
  `Geometry/SteinGeometricConnected`.

---

## Lipman (as presented in the Stacks Project)

### L1. `KltDP.Literature.Stacks.lipman_resolution_of_normal_completions_literal`

* **File.** `Literature/LipmanResolutionLiteral.lean`.
* **Published source.** Docstring gives: "The entire implication (4) => (2) of Stacks 0BGP, Theorem
  54.14.5." (No revision/commit recorded; Lipman is not named in the docstring — the attribution to
  Lipman is the caller's grouping.)
* **Plain statement.** Let Y be an integral Noetherian scheme of dimension 2 whose normalisation N → Y
  (in its function field) is finite, such that N has only finitely many non-regular points and the
  completed local ring at each of them is normal. Then Y has a resolution of singularities: an integral,
  locally Noetherian scheme S, regular at every point, with a proper birational morphism S → Y.
* **Lean signature.**
  ```lean
  axiom lipman_resolution_of_normal_completions_literal :
    ∀ (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y],
      topologicalKrullDim Y = 2 →
      ∀ (N : Scheme.{u}) (ν : N ⟶ Y),
        IsNormalizationInFunctionField ν →
        IsFinite ν →
        {n : N | ¬ RegularLocalByGenerators (N.presheaf.stalk n)}.Finite →
        (∀ n ∈ {n : N | ¬ RegularLocalByGenerators (N.presheaf.stalk n)},
          IsNormalRingStacks (localCompletion (N.presheaf.stalk n))) →
        ∃ (S : Scheme.{u}) (π : S ⟶ Y) (_ : IsIntegral S),
          IsLocallyNoetherian S ∧
          (∀ s : S, RegularLocalByGenerators (S.presheaf.stalk s)) ∧
          IsProper π ∧ IsBirationalScheme π
  ```
* **Instance/specialisation notes.** "Normalization is presented by coherent integral-closure charts in
  the original function field. See the separate root admission and dictionary."
* **Consumers.** `Geometry/GeneralMinimalResolutionExistence` (1). Transitive only.

---

## Keel

### K1. `KltDP.Literature.Keel.semiampleness_completeSystem_literal`

* **File.** `Literature/KeelCompleteSystem.lean`.
* **Published source.** "Seán Keel, Annals of Mathematics 149 (1999), 253–286, Theorem 0.2 on printed
  p.254; definitions 0.0–0.1 on pp.253–254, conventions on p.259. DOI: 10.2307/121025. Published PDF
  SHA256: 4d87c752091896d480e6fdf3829f59db4c152e26568a6eb3a4297384ee98e272."
* **Plain statement.** Over a field of characteristic p > 0, a nef line bundle L on a projective scheme
  X is semiample if and only if its restriction to the exceptional locus of L (the locus where L fails
  to be big, as a reduced closed subscheme) is semiample.
* **Lean signature.**
  ```lean
  axiom semiampleness_completeSystem_literal
      {k : Type u} [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
      (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
      (hproj : IsProjectiveOverField f)
      (L : InvertibleSheaf X) (hnef : Positivity.IsNef f L) :
      letI : IsProper f := hproj.isProper
      Positivity.IsSemiample L ↔
        Positivity.IsSemiample (KeelCompleteSystem.exceptionalRestrict f L)
  ```
* **Instance/specialisation notes.** "Keel's full Theorem 0.2, using its original complete-system
  definition"; "a nef line on an arbitrary projective scheme in positive characteristic is semiample
  exactly when its actual exceptional restriction is semiample. The ambient scheme need not be reduced
  or integral."; "The original complete H0 map, eventual powers, reduced exceptional scheme,
  zero-dimensional filter, original-field Euler degree and actual generation comparisons are
  independently proved. No growth equivalence is assumed." Decision:
  `keel_complete_source_admission_review_20260913/ROOT_CANDIDATE_ADMISSION_DECISION.json`.
* **Consumers.** `Geometry/NefPositiveSquareKeelRestriction` (1),
  `Geometry/FrobeniusMultiCentreKeelSemiample` (1), `Manuscript/S02/AnticanonicalContraction` (1,
  docstring: consumed "through NefPositiveSquareKeelRestriction"). Section: §2, Theorem 2.6 (the paper's Theorem 2.3 is this statement).

---

## Zariski

### Z1. `KltDP.Literature.Zariski.closedPoint_normal_completion_literal`

* **File.** `Literature/ZariskiNormalCompletion.lean`.
* **Published source.** Docstring gives: "Zariski, Ann. Inst. Fourier 2 (1950), Theorem 2, printed page
  162." (Paper title not recorded in the docstring.)
* **Plain statement.** Let B be an integral finite-type algebra over a field k and p a maximal ideal
  whose local ring B_p is integrally closed. Then the completion of B_p at its maximal ideal is a local
  ring, a domain, and integrally closed (normal points of an affine variety are analytically normal).
* **Lean signature.**
  ```lean
  axiom closedPoint_normal_completion_literal
      (k : Type u) [Field k]
      (B : Type u) [CommRing B] [IsDomain B]
      [Algebra k B] [Algebra.FiniteType k B]
      (p : Ideal B) [p.IsMaximal]
      [IsIntegrallyClosed (Localization.AtPrime p)] :
      IsLocalRing
          (AdicCompletion
            (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p)) ∧
        IsDomain
          (AdicCompletion
            (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p)) ∧
        IsIntegrallyClosed
          (AdicCompletion
            (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p))
  ```
* **Instance/specialisation notes.** "Closed points of the original integral affine variety; full
  local-domain and integral-closedness conclusion for the original maximal-ideal completion. ... The
  field chosen internally in the published proof adds no premise here."
* **Consumers.** `Geometry/SingularStalkCompletionZariski` (2), `Geometry/GeneralMinimalResolutionExistence` (1).
  Transitive only.

---

## Tanaka

### T1. `KltDP.Literature.Tanaka.contraction_44_instance` —

* **File.** `Literature/Tanaka/ContractionTheorem.lean` (new; file mtime 2026-09-15 23:14).
* **Published source.** "Hiromu Tanaka, *Minimal model program for excellent surfaces*, Annales de
  l'Institut Fourier 68 (2018), no. 1, 345–376, doi:10.5802/aif.3163, Theorem 4.4 (printed p. 365;
  extracted text tanaka2018.txt lines 1012–1029)." The docstring quotes Theorem 4.4 verbatim
  (conclusions (1)–(5)).
* **Plain statement.** Let S be a regular projective surface over an algebraically closed field with
  canonical divisor K_S, and let R = ℝ≥0·v be an extremal ray of the closed cone of curves with
  K_S·v < 0. Then there is a morphism f : S → Y over k to a projective k-scheme Y such that
  f\*O_S = O_Y, a prime curve C of S is contracted to a point by f exactly when its class lies in R,
  and the Picard number drops by one: ρ(Y) = ρ(S) − 1.
* **Lean signature.**
  ```lean
  axiom contraction_44_instance {k : Type u} [Field k] [IsAlgClosed k]
      (S : NormalProjectiveSurface k) [FiniteDimensional ℚ S.NumericalClassGroup]
      (hreg : ∀ x : S.Point, RegularPoint S.toScheme x)
      (KS : CartierDivisor S.toScheme)
      (eKS : cartierDivisorModule S.toScheme KS ≅
        SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
      (v : V S) (hv : IsExtremalRay S (closedCurveCone S hreg) v)
      (hneg : pairReal S hreg (NefNullCurveNegativeSquare.cartierClass S KS) v < 0) :
      ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of k)) (f : S.toScheme ⟶ Y),
        IsProjectiveOverField g ∧
        f ≫ g = S.structureMorphism ∧
        IsIso f.c ∧
        (∀ C : S.PrimeCurve,
          (∃ y : Y, f.base '' (C : Set S.toScheme) = {y}) ↔
            curveClassReal S hreg C ∈ ray S v) ∧
        rhoReal Y g + 1 = S.picardRank
  ```
* **Instance/specialisation notes** (all from the docstring, "with every specialization recorded"):
  "B = S = Spec k for an algebraically closed field k. A field is excellent, regular, separated and of
  finite dimension, so Spec k satisfies Tanaka's Assumption 2.1"; "X = S.toScheme for an actual regular
  normal projective surface ... π = S.structureMorphism, which is projective"; "Δ = 0 ... then
  K_{X/B} + Δ = K_S, represented by the Cartier divisor KS whose divisor sheaf is the canonical sheaf
  ω_{S/k} = ∧² Ω_{S/k} (eKS), hence R-Cartier"; "NE(X/S) ... is the closed cone of curves closedCurveCone
  S hreg in the real Néron–Severi model V S ...: Tanaka's N_1(X/S)_ℝ is identified with V S = N¹(S)_ℝ
  through the perfect intersection pairing (rhoReal_eq_picardRank and pairingMap)"; extremal ray in the
  sense of "Kollár–Mori, Definition 1.16, the definition Tanaka uses"; "(1) f\*O_X = O_Y is IsIso f.c";
  "(2) The projective S-curves C on X with π(C) a point are all prime curves of S"; "(4) ρ(Y/S) =
  ρ(X/S) − 1, with Tanaka's ρ = dim_ℝ N_1(·/S)_ℝ ... formalized as NumericalOneCycles.rhoReal; on the
  source ρ(X/S) = ... S.picardRank by rhoReal_eq_picardRank, so (4) is stated as rhoReal Y g + 1 =
  S.picardRank"; "Conclusions (3) and (5) are omitted (an instance with fewer conclusions is implied by
  the theorem). Nothing is added: no manuscript consequence is packaged into the axiom."
* **Consumers.** `Manuscript/S03/NefThresholdCore` (2; one application at line 454, docstring at line 23),
  `Manuscript/Main/Final` (1, docstring). Section: §3 — `S03/NefThresholdCore` (`exists_minusOneCurve_of_extremalRay`,
  `exists_minusOneCurve_of_not_nef`, `nef_of_minusOne_nonneg`) and Lemma 3.3 in `S03/NefThreshold`
  (`thresholdClass_square_nonneg`).

---
