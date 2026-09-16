import KltDP.Compatibility.ConstantRankSheaf
import KltDP.Compatibility.PresheafTensorColimits
import KltDP.Compatibility.SheafRestrictionTensor
import KltDP.Compatibility.SheafIteratedOverKernel
import KltDP.Geometry.SheafPicard

/-!
# Tensor products of actual finite local bases

The pinned coproduct comparisons distribute the actual presheaf tensor over
coproducts of its unit. The original module-sheafification adjunction and its
proved monoidal structure transport this comparison to the original free
module sheaves. No preservation theorem for sheaf tensor is assumed.

On a scheme, intersections of the original two atlases form an actual common
cover. Their original free presentations restrict to these intersections,
and the free-tensor comparison gives the product basis. Its finite cardinality
is the product of the original ranks, including when either rank is zero.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

universe u

namespace KltDP.SheafOfModules

section FreeTensor

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (S : Cᵒᵖ ⥤ CommRingCat.{u})

/-- Distribute the original presheaf tensor across its actual coproducts.
The index of the resulting unit coproduct is the product of the two indices. -/
def presheafUnitCoproductTensorIso (I K : Type u) :
    ((∐ fun _ : I => 𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))) ⊗
      (∐ fun _ : K => 𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)))) ≅
      (∐ fun _ : I × K => 𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))) := by
  let P := PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)
  let Q (A : Type u) : P := ∐ fun _ : A => 𝟙_ P
  letI := PresheafOfModules.preservesColimitsOfSize_tensorRight_aux (Q K)
  letI := PresheafOfModules.preservesColimitsOfSize_tensorLeft_aux (𝟙_ P)
  exact
    PreservesCoproduct.iso (tensorRight (Q K)) (fun _ : I => 𝟙_ P) ≪≫
    Sigma.mapIso (fun _ : I =>
      PreservesCoproduct.iso (tensorLeft (𝟙_ P)) (fun _ : K => 𝟙_ P)) ≪≫
    Sigma.mapIso (fun _ : I => Sigma.mapIso (fun _ : K => λ_ (𝟙_ P))) ≪≫
    sigmaSigmaIso (fun _ : I => K) (fun _ _ => 𝟙_ P) ≪≫
    Sigma.reindex (Equiv.sigmaEquivProd I K) (fun _ : I × K => 𝟙_ P)

variable (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))
  [HasWeakSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- The original free sheaf is the sheafification of the original presheaf
unit coproduct, through coproduct preservation and the actual counit. -/
def freeIsoSheafificationUnitCoproduct (I : Type u) :
    _root_.SheafOfModules.free
      (R := (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})) I ≅
      (PresheafOfModules.sheafification
        (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).val)).obj
        (∐ fun _ : I => 𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))) := by
  let R : Sheaf J RingCat.{u} := ⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩
  let F := PresheafOfModules.sheafification (𝟙 R.val)
  exact Sigma.mapIso (fun _ : I =>
      (PresheafOfModules.sheafificationForgetIso R (_root_.SheafOfModules.unit R)).symm) ≪≫
    (PreservesCoproduct.iso F
      (fun _ : I => 𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)))).symm

/-- The tensor of the original free sheaves has the original product basis.
Monoidal sheafification transports the presheaf coproduct comparison. -/
def freeTensorFreeIso (I K : Type u) :
    letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
    (_root_.SheafOfModules.free
        (R := (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})) I ⊗
      _root_.SheafOfModules.free K) ≅ _root_.SheafOfModules.free (I × K) := by
  letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
  letI := PresheafOfModules.sheafificationMonoidal S hS
  let R : Sheaf J RingCat.{u} := ⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩
  let F := PresheafOfModules.sheafification (𝟙 R.val)
  let Q (A : Type u) : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat) :=
    ∐ fun _ : A => 𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))
  exact tensorIso (freeIsoSheafificationUnitCoproduct S hS I)
      (freeIsoSheafificationUnitCoproduct S hS K) ≪≫
    Functor.Monoidal.μIso F (Q I) (Q K) ≪≫
    F.mapIso (presheafUnitCoproductTensorIso S I K) ≪≫
    (freeIsoSheafificationUnitCoproduct S hS (I × K)).symm

end FreeTensor

section SchemeRank

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} {M N : X.Modules} {n m : ℕ}

/-- Restrict an original standard-basis chart to any actual smaller open.
The existing iterated-Over functor retains its original presentation. -/
def ConstantRankTrivializations.isoOnSubopen
    (t : ConstantRankTrivializations (R := X.ringCatSheaf) M n) (i : t.I) (U : X.Opens) (hU : U ≤ t.X i) :
    _root_.SheafOfModules.free
      (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n)) ≅ M.over U := by
  let V : Over (t.X i) := Over.mk (homOfLE hU)
  exact _root_.SheafOfModules.overToSingleFreeIso X.ringCatSheaf V (ULift.{u} (Fin n)) ≪≫
    (_root_.SheafOfModules.overToSingleFunctor X.ringCatSheaf V).mapIso (t.iso i) ≪≫
    _root_.SheafOfModules.iteratedOverObjIso X.ringCatSheaf M V

set_option maxHeartbeats 800000 in
/-- The actual tensor product of constant finite-rank modules has the
product rank. The proof constructs the finite local product bases. -/
theorem IsLocallyFreeOfRank.tensor
    (hM : IsLocallyFreeOfRank (R := X.ringCatSheaf) M n)
    (hN : IsLocallyFreeOfRank (R := X.ringCatSheaf) N m) :
    letI := Scheme.Modules.monoidalCategory X
    IsLocallyFreeOfRank (R := X.ringCatSheaf) (M ⊗ N) (n * m) := by
  letI := Scheme.Modules.monoidalCategory X
  let t := hM.trivializations
  let s := hN.trivializations
  let U (a : t.I × s.I) : X.Opens := t.X a.1 ⊓ s.X a.2
  have hU : (Opens.grothendieckTopology X).CoversTop U := by
    intro W
    change ∀ x ∈ W, ∃ (T : X.Opens) (f : T ⟶ W),
      (Sieve.ofObjects U W) f ∧ x ∈ T
    intro x hx
    obtain ⟨T, f, ⟨i, ⟨g⟩⟩, hxT⟩ := t.coversTop W x hx
    obtain ⟨T', f', ⟨j, ⟨g'⟩⟩, hxT'⟩ := s.coversTop T x hxT
    exact ⟨T', f' ≫ f,
      ⟨(i, j), ⟨homOfLE (le_inf (f'.le.trans g.le) g'.le)⟩⟩, hxT'⟩
  let e (a : t.I × s.I) :
      _root_.SheafOfModules.free (R := X.ringCatSheaf.over (U a))
        (ULift.{u} (Fin n) × ULift.{u} (Fin m)) ≅ (M ⊗ N).over (U a) := by
    letI : MonoidalCategory (_root_.SheafOfModules.{u} (X.ringCatSheaf.over (U a))) :=
      PresheafOfModules.sheafOfModulesMonoidalCategory
        ((Over.forget (U a)).op ⋙ X.sheaf.val)
        (overRingSheafCondition X.sheaf.val X.ringCatSheaf.cond (U a))
    exact (freeTensorFreeIso ((Over.forget (U a)).op ⋙ X.sheaf.val)
        (overRingSheafCondition X.sheaf.val X.ringCatSheaf.cond (U a))
        (ULift.{u} (Fin n)) (ULift.{u} (Fin m))).symm ≪≫
      tensorIso (t.isoOnSubopen a.1 (U a) inf_le_left)
        (s.isoOnSubopen a.2 (U a) inf_le_right) ≪≫
      (overTensorIso X.sheaf.val X.ringCatSheaf.cond (U a) M N).symm
  let q : _root_.SheafOfModules.LocalGeneratorsData (R := X.ringCatSheaf) (M ⊗ N) := {
    I := t.I × s.I
    X := U
    coversTop := hU
    generators a := (_root_.SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf.over (U a))
      (ULift.{u} (Fin n) × ULift.{u} (Fin m))).ofEpi (e a).hom }
  refine { exists_localGeneratorsData := ⟨q, ?_⟩ }
  refine { isLocallyFreeData := { isIso := ?_ }, basisFinite := ?_, basisCard := ?_ }
  · intro a
    change IsIso ((_root_.SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf.over (U a))
      (ULift.{u} (Fin n) × ULift.{u} (Fin m))).ofEpi (e a).hom).π
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π,
      _root_.SheafOfModules.free.generatingSections_π]
    infer_instance
  · intro a
    change Finite (ULift.{u} (Fin n) × ULift.{u} (Fin m))
    infer_instance
  · intro a
    change Nat.card (ULift.{u} (Fin n) × ULift.{u} (Fin m)) = n * m
    simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_ulift, Fintype.card_fin]

end SchemeRank

end KltDP.SheafOfModules
