import KltDP.Geometry.SchemeKaehlerSheaf
import KltDP.Geometry.SmoothKaehlerLocallyFree
import KltDP.Geometry.InvertibleSheafPicard
import KltDP.Geometry.PicardEulerValue
import KltDP.Geometry.ProperCurveEuler
import KltDP.Geometry.RankIndexedCurveDegree
import KltDP.Compatibility.ConstantRankSheaf

/-!
# The canonical class and the genus of a curve over a field

For a scheme `C` over a field, `f : C ⟶ Spec k`, the accepted global sheaf of base-ring
differentials `Ω_{C/k} := SchemeKaehlerSheaf.baseRingSheaf f` is the cotangent sheaf. When it is
invertible (a smooth curve; local freeness is the accepted `SmoothKaehlerLocallyFree.isLocallyFree`,
rank one is a separate hypothesis here) it is the canonical sheaf `ω_C`, with canonical class
`K_C := [Ω_C] ∈ Pic C`. The genus is `g := dim_k H¹(C, O_C)` and the canonical degree is
`deg K_C := χ(Ω_C) − χ(O_C)` (Stacks 0AYR at rank one, `finiteRankDegree`).

Proved here: the definitions, `deg K_C` as a Picard invariant (`canonicalDegree_eq_picardEulerValue`),
its isomorphism invariance, its identification with the rank-one `finiteRankDegree`, and, for a proper
`C` of dimension `≤ 1`, the four-term form `deg K_C = (h⁰(Ω) − h¹(Ω)) − (h⁰(O) − g)`
(accepted `ProperCurveEuler`). The Riemann–Roch/duality identity `deg K_C = 2g − 2` is stated as the
predicate `CanonicalDegreeFormula` and **not proved in general**; the projective line is treated in
`KltDP.Geometry.ProjectiveLineCanonical*`.

Hypotheses: `k : Type u`, `[Field k]`, `f : C ⟶ Spec (CommRingCat.of k)`; invertibility of `Ω_C` is the
explicit argument `h`; the `h⁰/h¹` form needs `[IsProper f]` and `topologicalKrullDim C ≤ 1`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.CurveCanonical

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (CommRingCat.of k))

/-- `Ω_{C/k}`: the accepted global sheaf of base-ring differentials of `f : C ⟶ Spec k`. -/
abbrev cotangentSheaf : C.Modules := SchemeKaehlerSheaf.baseRingSheaf f

/-- Over a field, smoothness makes the cotangent sheaf locally free (accepted). -/
theorem cotangentSheaf_isLocallyFree [IsSmooth f] :
    _root_.SheafOfModules.IsLocallyFree (R := C.ringCatSheaf) (cotangentSheaf f) :=
  SmoothKaehlerLocallyFree.isLocallyFree f

/-- The canonical sheaf `ω_C = Ω_C` of a curve whose cotangent sheaf is invertible. -/
def canonicalSheaf
    (h : KltDP.SheafOfModules.IsInvertible (R := C.ringCatSheaf) (cotangentSheaf f)) :
    InvertibleSheaf C :=
  ⟨cotangentSheaf f, h⟩

@[simp]
theorem canonicalSheaf_obj
    (h : KltDP.SheafOfModules.IsInvertible (R := C.ringCatSheaf) (cotangentSheaf f)) :
    (canonicalSheaf f h).obj = cotangentSheaf f := rfl

/-- The canonical class `K_C := [Ω_C] ∈ Pic C`. -/
def canonicalClass
    (h : KltDP.SheafOfModules.IsInvertible (R := C.ringCatSheaf) (cotangentSheaf f)) : C.Pic :=
  (canonicalSheaf f h).toPic

/-- The genus `g := dim_k H¹(C, O_C)`. -/
def genus : ℕ :=
  cohomologyDimension f (_root_.SheafOfModules.unit C.ringCatSheaf) 1

/-- The canonical degree `deg K_C := χ(Ω_C) − χ(O_C)`. -/
def canonicalDegree : ℤ :=
  eulerCharacteristic f (cotangentSheaf f) -
    eulerCharacteristic f (_root_.SheafOfModules.unit C.ringCatSheaf)

/-- The canonical degree is the Euler value of the canonical class minus that of the identity. -/
theorem canonicalDegree_eq_picardEulerValue
    (h : KltDP.SheafOfModules.IsInvertible (R := C.ringCatSheaf) (cotangentSheaf f)) :
    canonicalDegree f = picardEulerValue f (canonicalClass f h) - picardEulerValue f 1 := by
  unfold canonicalDegree canonicalClass
  rw [picardEulerValue_toPic, picardEulerValue_one]
  rfl

/-- Any module isomorphic to `Ω_C` has the same Euler difference. -/
theorem canonicalDegree_eq_of_iso {L : C.Modules} (e : cotangentSheaf f ≅ L) :
    canonicalDegree f =
      eulerCharacteristic f L - eulerCharacteristic f (_root_.SheafOfModules.unit C.ringCatSheaf) := by
  unfold canonicalDegree
  rw [eulerCharacteristic_eq_of_iso f e]

/-- An invertible cotangent sheaf is locally free of rank one. -/
theorem cotangentSheaf_isLocallyFreeOfRank_one
    (h : KltDP.SheafOfModules.IsInvertible (R := C.ringCatSheaf) (cotangentSheaf f)) :
    KltDP.SheafOfModules.IsLocallyFreeOfRank (R := C.ringCatSheaf) (cotangentSheaf f) 1 := by
  haveI := h
  infer_instance

/-- The canonical degree is the rank-one degree of Stacks 0AYR. -/
theorem canonicalDegree_eq_finiteRankDegree [IsProper f] (hdim : topologicalKrullDim C ≤ 1)
    (h : KltDP.SheafOfModules.IsInvertible (R := C.ringCatSheaf) (cotangentSheaf f)) :
    canonicalDegree f =
      finiteRankDegree f hdim (cotangentSheaf f) 1 (cotangentSheaf_isLocallyFreeOfRank_one f h) := by
  simp [canonicalDegree, finiteRankDegree]

/-- On a proper curve, `deg K_C = (h⁰(Ω_C) − h¹(Ω_C)) − (h⁰(O_C) − g)`. -/
theorem canonicalDegree_eq_h0_sub_h1 [IsProper f] (hdim : topologicalKrullDim C ≤ 1) :
    canonicalDegree f =
      ((cohomologyDimension f (cotangentSheaf f) 0 : ℤ) -
          (cohomologyDimension f (cotangentSheaf f) 1 : ℤ)) -
        ((cohomologyDimension f (_root_.SheafOfModules.unit C.ringCatSheaf) 0 : ℤ) -
          (genus f : ℤ)) := by
  unfold canonicalDegree genus
  rw [proper_eulerCharacteristic_eq_h0_sub_h1 f hdim (cotangentSheaf f),
    proper_eulerCharacteristic_eq_h0_sub_h1 f hdim (_root_.SheafOfModules.unit C.ringCatSheaf)]

/-- **The Riemann–Roch / duality target** `deg K_C = 2g − 2`, as a predicate. It is **not proved**
in general in this tree; see the projective-line modules for the first instance. -/
def CanonicalDegreeFormula : Prop :=
  canonicalDegree f = 2 * (genus f : ℤ) - 2

theorem canonicalDegreeFormula_iff :
    CanonicalDegreeFormula f ↔ canonicalDegree f = 2 * (genus f : ℤ) - 2 :=
  Iff.rfl

end KltDP.Geometry.CurveCanonical
