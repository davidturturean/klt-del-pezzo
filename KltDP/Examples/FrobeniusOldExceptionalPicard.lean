import KltDP.Examples.FrobeniusOldExceptionalTotalProduct
import KltDP.Examples.FrobeniusStrictTransformClassesTower
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# The Picard class of the older exceptional curve on its birth stage

The whole-stage isomorphism `π^* I(E_j) ≅ I(E_{j+1}) ⊗ I(C_j)` of
`FrobeniusOldExceptionalTotalProduct` makes the kernel module of the strict transform
`C_j = previousStrictTransform (A.stage j)` an invertible sheaf on stage `j+2` (a tensor factor of
an invertible sheaf whose other factor is invertible), so `C_j` has a Picard class
`oldStrictPicardClass j` in the lane's ideal-sheaf sign convention, and

  `C_j = π^* E_j − E_{j+1}`   on stage `j+2`   (`oldStrictPicardClass_eq`),

i.e. `C_j = E_j^{(j+2)} − E_{j+1}^{(j+2)}` in terms of the tower's total exceptional classes
(`oldStrictPicardClass_eq_total`). The invariance of this relation under the later blowups of the
tower (the class of the image `finalOldMap N j` of `C_j` on stage `N ≥ j+2`) is not proved here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusOldExceptionalPicard

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
open FrobeniusStrictTransformProductKernel FrobeniusStrictTransformPicardStep
open FrobeniusStrictTransformClassesTower
open FrobeniusOldExceptionalChartIdeals FrobeniusOldExceptionalTotalProduct

attribute [local instance] Types.instFunLike Types.instConcreteCategory

-- No module-level monoidal instance: the Picard group operations must all come from the accepted
-- instances on `X.Pic`, and the tensor products below are taken under explicit `letI`.

variable {k : Type u} [Field k]

/-- The ideal line of the previous exceptional curve `E_j`, pulled back to stage `j+2`. -/
def oldPulledExceptionalLine (j : ℕ) : InvertibleSheaf (projectiveContactStage (k := k) (j + 1 + 1)) :=
  pullbackInvertibleSheaf ((projectiveProductInitial (k := k)).stepProjection (j + 1))
    (stepExceptionalIdealLine j)

/-- The whole-stage comparison, read on the underlying module sheaf of the accepted pulled line. -/
def oldPulledExceptionalLineIso (j : ℕ) :
    (oldPulledExceptionalLine (k := k) j).obj ≅ exceptionalOldTensor (k := k) j :=
  oldTotalProductIso j

/-- The tensor line is the tensor of the exceptional line and of the kernel of `C_j`, in the
monoidal structure fixed by the accepted Picard machinery. -/
theorem exceptionalOldTensor_eq (j : ℕ) :
    letI := Scheme.Modules.monoidalCategory (projectiveContactStage (k := k) (j + 1 + 1))
    exceptionalOldTensor (k := k) j =
      (stepExceptionalIdealLine (k := k) (j + 1)).obj ⊗
        schemeKernelIdeal (oldExceptionalStrictι (k := k) j) := rfl

/-- The kernel module of the strict transform `C_j` is invertible: it is a tensor factor of the
invertible pulled-back line, the other factor being the invertible exceptional line. -/
theorem oldStrictKernel_isInvertible (j : ℕ) :
    KltDP.SheafOfModules.IsInvertible
      (R := (projectiveContactStage (k := k) (j + 1 + 1)).ringCatSheaf)
      (schemeKernelIdeal (oldExceptionalStrictι j)) := by
  refine SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton _ ?_
  letI := Scheme.Modules.monoidalCategory (projectiveContactStage (k := k) (j + 1 + 1))
  have hE := (stepExceptionalIdealLine (k := k) (j + 1)).isUnit_toSkeleton
  have hmul : IsUnit (toSkeleton ((stepExceptionalIdealLine (k := k) (j + 1)).obj ⊗
      schemeKernelIdeal (oldExceptionalStrictι (k := k) j))) := by
    have e : toSkeleton ((stepExceptionalIdealLine (k := k) (j + 1)).obj ⊗
        schemeKernelIdeal (oldExceptionalStrictι (k := k) j)) =
          toSkeleton (oldPulledExceptionalLine (k := k) j).obj := by
      rw [← exceptionalOldTensor_eq]
      exact Quotient.sound ⟨(oldPulledExceptionalLineIso j).symm⟩
    rw [e]
    exact (oldPulledExceptionalLine (k := k) j).isUnit_toSkeleton
  rw [Skeleton.toSkeleton_tensorObj] at hmul
  have hmul' : IsUnit ((hE.unit : Skeleton (projectiveContactStage (k := k) (j + 1 + 1)).Modules) *
      toSkeleton (schemeKernelIdeal (oldExceptionalStrictι (k := k) j))) := by
    rw [IsUnit.unit_spec]
    exact hmul
  exact (Units.isUnit_units_mul hE.unit _).mp hmul'

/-- The ideal of the strict transform `C_j` as an invertible sheaf on stage `j+2`. -/
def oldStrictKernelLine (j : ℕ) : InvertibleSheaf (projectiveContactStage (k := k) (j + 1 + 1)) :=
  ⟨schemeKernelIdeal (oldExceptionalStrictι j), oldStrictKernel_isInvertible j⟩

@[simp] theorem oldStrictKernelLine_obj (j : ℕ) :
    (oldStrictKernelLine (k := k) j).obj = schemeKernelIdeal (oldExceptionalStrictι j) := rfl

/-- The pulled-back class of the ideal of `E_j` is the product of the ideal classes of `E_{j+1}`
and of `C_j`. -/
theorem oldPulledExceptionalLine_picard (j : ℕ) :
    (oldPulledExceptionalLine (k := k) j).toPic =
      (stepExceptionalIdealLine (j + 1)).toPic * (oldStrictKernelLine j).toPic := by
  letI := Scheme.Modules.monoidalCategory (projectiveContactStage (k := k) (j + 1 + 1))
  apply Units.ext
  change ((oldPulledExceptionalLine (k := k) j).toPic :
      Skeleton (projectiveContactStage (k := k) (j + 1 + 1)).Modules) =
    ((stepExceptionalIdealLine (k := k) (j + 1)).toPic :
      Skeleton (projectiveContactStage (k := k) (j + 1 + 1)).Modules) *
      ((oldStrictKernelLine (k := k) j).toPic :
        Skeleton (projectiveContactStage (k := k) (j + 1 + 1)).Modules)
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val,
    ← Skeleton.toSkeleton_tensorObj, oldStrictKernelLine_obj, ← exceptionalOldTensor_eq]
  exact Quotient.sound ⟨oldPulledExceptionalLineIso j⟩

/-- Pullback of the ideal class of `E_j` along the blowdown is exceptional times `C_j`. -/
theorem oldExceptionalIdealLine_picard_step (j : ℕ) :
    schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection (j + 1))
        (stepExceptionalIdealLine j).toPic =
      (stepExceptionalIdealLine (j + 1)).toPic * (oldStrictKernelLine j).toPic := by
  rw [schemePicardPullbackHom_toPic]
  exact oldPulledExceptionalLine_picard j

/-- The additive form of the multiplicative step, isolated so that only rewriting (never
unification of the concrete Picard classes) is needed. -/
private theorem neg_ofMul_mul_step (j : ℕ) : -Additive.ofMul ((stepExceptionalIdealLine (k := k) (j + 1)).toPic * (oldStrictKernelLine (k := k) j).toPic) =
    -Additive.ofMul (stepExceptionalIdealLine (k := k) (j + 1)).toPic + -Additive.ofMul (oldStrictKernelLine (k := k) j).toPic := by
  rw [ofMul_mul, neg_add]

/-- The Picard class of the strict transform `C_j` on stage `j+2`, in the lane's ideal-sheaf sign
convention (a curve's class is minus the class of its ideal line). -/
def oldStrictPicardClass (j : ℕ) : Additive (projectiveContactStage (k := k) (j + 1 + 1)).Pic :=
  -Additive.ofMul (oldStrictKernelLine (k := k) j).toPic

/-- The Picard pullback of the class of `E_j` is the class of `E_{j+1}` plus that of `C_j`. -/
theorem oldStrictPicardClass_pullback (j : ℕ) :
    (schemePicardPullbackHom (X := projectiveContactStage (k := k) (j + 1))
      (Y := projectiveContactStage (k := k) (j + 1 + 1))
      ((projectiveProductInitial (k := k)).stepProjection (j + 1))).toAdditive
        (stepExceptionalPicardClass j) =
      stepExceptionalPicardClass (j + 1) + oldStrictPicardClass j := by
  change (schemePicardPullbackHom
      ((projectiveProductInitial (k := k)).stepProjection (j + 1))).toAdditive
        (-Additive.ofMul (stepExceptionalIdealLine j).toPic) = _
  rw [map_neg]
  change -Additive.ofMul
      (schemePicardPullbackHom (X := projectiveContactStage (k := k) (j + 1))
      (Y := projectiveContactStage (k := k) (j + 1 + 1))
      ((projectiveProductInitial (k := k)).stepProjection (j + 1))
        (stepExceptionalIdealLine j).toPic) =
    -Additive.ofMul (stepExceptionalIdealLine (j + 1)).toPic +
      -Additive.ofMul (oldStrictKernelLine j).toPic
  rw [oldExceptionalIdealLine_picard_step]
  exact neg_ofMul_mul_step j

/-- `C_j = π^* E_j − E_{j+1}` on stage `j+2`. -/
theorem oldStrictPicardClass_eq (j : ℕ) :
    oldStrictPicardClass (k := k) j =
      (schemePicardPullbackHom (X := projectiveContactStage (k := k) (j + 1))
      (Y := projectiveContactStage (k := k) (j + 1 + 1))
      ((projectiveProductInitial (k := k)).stepProjection (j + 1))).toAdditive
        (stepExceptionalPicardClass (k := k) j) - stepExceptionalPicardClass (k := k) (j + 1) := by
  -- generalize the three concrete classes first: unifying them under the group-structure
  -- instances would unfold the Picard classes down to the sheaves and time out
  have h := oldStrictPicardClass_pullback (k := k) j
  revert h
  generalize (schemePicardPullbackHom (X := projectiveContactStage (k := k) (j + 1))
      (Y := projectiveContactStage (k := k) (j + 1 + 1))
      ((projectiveProductInitial (k := k)).stepProjection (j + 1))).toAdditive
    (stepExceptionalPicardClass (k := k) j) = A
  generalize stepExceptionalPicardClass (k := k) (j + 1) = B
  generalize oldStrictPicardClass (k := k) j = C
  intro h
  exact eq_sub_iff_add_eq'.mpr h.symm

/-- `C_j = E_j^{(j+2)} − E_{j+1}^{(j+2)}` in terms of the tower's total exceptional classes on the
birth stage `j+2` of `C_j` (`E_j` is the index `Fin.castSucc (Fin.last j)`, `E_{j+1}` the last index). -/
theorem oldStrictPicardClass_eq_total (j : ℕ) :
    oldStrictPicardClass (k := k) j =
      totalExceptionalClass (k := k) (j + 1 + 1) (Fin.castSucc (Fin.last j)) -
        totalExceptionalClass (k := k) (j + 1 + 1) (Fin.last (j + 1)) := by
  rw [totalExceptionalClass_castSucc, totalExceptionalClass_last, totalExceptionalClass_last]
  -- the tower lemma states the pullback with the stage in the `(A.stage (j+1+1)).carrier` form;
  -- at reducible transparency the two forms agree without unfolding the Picard classes
  with_reducible exact oldStrictPicardClass_eq j

/-- The same relation with the total exceptional classes indexed by the stage numbers `j` and
`j+1` of the two exceptional curves. -/
theorem oldStrictPicardClass_eq_total' (j : ℕ) :
    oldStrictPicardClass (k := k) j =
      totalExceptionalClass (k := k) (j + 1 + 1) ⟨j, by omega⟩ -
        totalExceptionalClass (k := k) (j + 1 + 1) ⟨j + 1, by omega⟩ := by
  rw [show (⟨j, by omega⟩ : Fin (j + 1 + 1)) = Fin.castSucc (Fin.last j) from rfl,
    show (⟨j + 1, by omega⟩ : Fin (j + 1 + 1)) = Fin.last (j + 1) from rfl]
  exact oldStrictPicardClass_eq_total j

end KltDP.Examples.FrobeniusOldExceptionalPicard
