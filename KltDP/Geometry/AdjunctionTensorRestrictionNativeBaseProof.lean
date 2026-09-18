import KltDP.Geometry.AdjunctionTensorRestrictionNativeSourceHom
import KltDP.Geometry.CategoryProofFamilySourceEquation

/-!
# Change the original proof inside the literal native source hom

The category-generic theorem sees only a proof-indexed morphism family.
Construct that family by replacing one argument along the original stored
Iso.trans/eqToIso/congrArg path, retaining every other native annotation.
The output is an ordinary kernel-checked theorem application.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
open Lean Meta Elab Term
universe u
namespace KltDP.Geometry.AdjunctionTensorRestrictionNativeBaseProof

private partial def headZeta (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ v b _ => headZeta (b.instantiate1 v)
  | e => e.headBeta

private def requireArgs (label : String) (e : Expr) (head : Name) (count : Nat) :
    MetaM (Array Expr) := do
  let e := headZeta e
  unless e.getAppFn.constName? == some head && e.getAppArgs.size == count do
    throwError "native base proof: unexpected {label} head/arity"
  return e.getAppArgs

elab "native_base_equation% " h:term : term => do
  let proof ← elabTerm h none
  let eq ← requireArgs "equation" (← inferType proof) ``Eq 3
  let rhs ← requireArgs "right side" eq[2]! ``CategoryTheory.CategoryStruct.comp 7
  let source ← requireArgs "source hom" rhs[5]! ``CategoryTheory.Iso.hom 5
  let trans ← requireArgs "native composite" source[4]! ``CategoryTheory.Iso.trans 7
  let secondExpr := headZeta trans[6]!
  let second ← requireArgs "native transport" secondExpr ``CategoryTheory.eqToIso 5
  let congrExpr := headZeta second[4]!
  let congr ← requireArgs "transport equality" congrExpr ``congrArg 6
  let originalBaseProof := congr[5]!
  let .const _ levels := congrExpr.getAppFn
    | throwError "native base proof: expected congrArg constant"
  let congrInfo ← getConstInfo ``congrArg
  let mut congrType := congrInfo.type.instantiateLevelParams congrInfo.levelParams levels
  for i in [:5] do
    let .forallE _ _ body _ := headZeta congrType
      | throwError "native base proof: unexpected congrArg telescope"
    congrType := body.instantiate1 congr[i]!
  let .forallE _ originalBaseType _ _ := headZeta congrType
    | throwError "native base proof: missing proof argument binder"
  withLocalDeclD `proofParameter originalBaseType fun parameter => do
    let variedCongr := mkAppN congrExpr.getAppFn (congr.set! 5 parameter)
    let variedSecond := mkAppN secondExpr.getAppFn (second.set! 4 variedCongr)
    let variedTrans := mkAppN (headZeta source[4]!).getAppFn
      (trans.set! 6 variedSecond)
    let variedSource := mkAppN (headZeta rhs[5]!).getAppFn
      (source.set! 4 variedTrans)
    let family ← mkLambdaFVars #[parameter] variedSource
    withLocalDeclD `hBase originalBaseType fun replacement => do
      let result ← mkAppOptM ``CategoryProofFamilySourceEquation.replace_proof #[
        some rhs[0]!, some source[1]!, some rhs[2]!, some rhs[3]!, some rhs[4]!,
        some originalBaseType, some family, some originalBaseProof,
        some eq[1]!, some rhs[6]!, some proof, some replacement]
      mkLambdaFVars #[replacement] result

/-- The native equation, accepting only a replacement proof of its own base equality. -/
def ring_square (R : Type u) [CommRing R] {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    {φ : A →+* B} {J : Ideal A} {J' : Ideal B} (hφ : J ≤ J'.comap φ)
    (d : J) (hJ : Ideal.span {(d : A)} = J)
    (hd : (d : A) ∈ nonZeroDivisors A)
    (hJ' : Ideal.span {φ (d : A)} = J')
    (hd' : φ (d : A) ∈ nonZeroDivisors B)
    (e : J') (hE : Ideal.span {(e : B)} = J')
    (he : (e : B) ∈ nonZeroDivisors B) :=
  let _ : Algebra A B := φ.toAlgebra
  fun (hTower : IsScalarTower R A B)
      (hA : Algebra.IsStandardSmoothOfRelativeDimension 2 R A)
      (hB : Algebra.IsStandardSmoothOfRelativeDimension 2 R B)
      (hQ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J))
      (hQ' : Algebra.IsStandardSmoothOfRelativeDimension 1 R (B ⧸ J'))
      (hOpen : IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap J' φ hφ)))) =>
    native_base_equation%
      (AdjunctionTensorRestrictionNativeSourceHom.ring_square R hφ
        d hJ hd hJ' hd' e hE he hTower hA hB hQ hQ' hOpen)

end KltDP.Geometry.AdjunctionTensorRestrictionNativeBaseProof
