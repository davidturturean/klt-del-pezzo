import KltDP.Geometry.RankIndexedCurveDegreeInterpretation
import KltDP.Compatibility.ConstantRankTensor

/-!
# Stacks 0AYX: isolated admission source proposal

INACTIVE TEXT ONLY. The prospective declaration below has not been admitted
or installed in production. Root must separately audit the full published
statement, actual-object interpretation, ordinary adapters and native output.

Source: Stacks Project, Lemma 33.44.7, tag 0AYX; degree is Definition 33.44.1,
tag 0AYR. Preserved varieties.tex at revision
540451b3e79a131df8eca4c4187448e49dcb262d, lines 9475-9488 and 9717-9733.
The source and its GFDL license are bound in this proposal's manifest.

The entire finite-rank statement is retained over every field and proper
scheme of dimension at most one. The actual tensor product has rank n*m
by the separately proved local product-basis theorem, used explicitly below.
The imported ordinary interpretation establishes that each degree is the
published finite Euler difference, subject to its separate admission audit.

Both instance binders are named (as in the three accepted literals) and the
two rank hypotheses use the transparent abbreviation `IsLocallyFreeOfRankOn`
(definitionally `KltDP.SheafOfModules.IsLocallyFreeOfRank (R := Y.ringCatSheaf)`),
so that the elaborated axiom type is a compact, independently reproducible
telescope for the trust auditor. Neither choice adds or removes a hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open scoped CategoryTheory.MonoidalCategory

universe u

namespace KltDP.Literature.Stacks

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- PROPOSED LITERATURE DECLARATION, INACTIVE: Stacks 0AYX in the ordinary
degree notation of 0AYR, with actual rank proofs and original coefficients. -/
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

end KltDP.Literature.Stacks
