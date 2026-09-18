import KltDP.Geometry.GluedAdjunctionBasisMapOpenLaws

/-!
# The original restriction law with its native open and proof arguments

The intermediate component retains its exact subopen proof. Proof
irrelevance is used only at this abstract family, and the Scheme.Opens
alias is reduced before returning the original restriction-law telescope.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u v
namespace KltDP.Geometry.GluedAdjunctionBasisRestrictionLaws

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem naturality_proof {X : Scheme.{u}} (M N : X.Modules)
    {ι : Type v} (B : ι → X.Opens)
    {c e : (InducedCategory X.Opens B)ᵒᵖ} (i : c ⟶ e)
    (h : B e.unop ≤ B c.unop) (hi : (homOfLE h).op = i)
    (gC : M.val.obj (op (B c.unop)) →+ N.val.obj (op (B c.unop)))
    (gD : (B e.unop ≤ B c.unop) →
      (M.val.obj (op (B e.unop)) →+ N.val.obj (op (B e.unop))))
    (gE : M.val.obj (op (B e.unop)) →+ N.val.obj (op (B e.unop)))
    (hAgree : gE = gD h)
    (hRes : ∀ m, gD (h.trans le_rfl) (M.val.map (homOfLE h).op m) =
      N.val.map (homOfLE h).op (gC m)) :
    ((inducedFunctor B).op ⋙ M.val.presheaf).map i ≫ AddCommGrp.ofHom gE =
      AddCommGrp.ofHom gC ≫ ((inducedFunctor B).op ⋙ N.val.presheaf).map i := by
  have hProof : gD h = gD (h.trans le_rfl) :=
    congrArg gD (Subsingleton.elim _ _)
  exact GluedAdjunctionBasisMapOpenLaws.naturality M N B i h hi
    gC (gD (h.trans le_rfl)) gE (hAgree.trans hProof) hRes

/-- The same original naturality, with the explicit native open type in its last premise. -/
def naturality {X : Scheme.{u}} (M N : X.Modules)
    {ι : Type v} (B : ι → X.Opens)
    {c e : (InducedCategory X.Opens B)ᵒᵖ} (i : c ⟶ e)
    (h : B e.unop ≤ B c.unop) (hi : (homOfLE h).op = i)
    (gC : M.val.obj (op (B c.unop)) →+ N.val.obj (op (B c.unop)))
    (gD : (B e.unop ≤ B c.unop) →
      (M.val.obj (op (B e.unop)) →+ N.val.obj (op (B e.unop))))
    (gE : M.val.obj (op (B e.unop)) →+ N.val.obj (op (B e.unop)))
    (hAgree : gE = gD h) := by
  have hNative := naturality_proof M N B i h hi gC gD gE hAgree
  dsimp only [Scheme.Opens] at hNative
  exact hNative

end KltDP.Geometry.GluedAdjunctionBasisRestrictionLaws
