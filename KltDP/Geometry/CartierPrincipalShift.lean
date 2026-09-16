import KltDP.Geometry.CartierModuleMultiplication

/-!
# Multiplication on the original Cartier fractional modules

A nonzero rational function q acts on the original rational-function sheaf
by multiplication. Restricting that actual map gives O(D + div(q)) ≅ O(D),
with forward map multiplication by q and inverse multiplication by q⁻¹.
Both maps retain their original inclusions into rational functions.

The local membership proof uses the original equation charts and the
existing convention O(D) = f⁻¹ O. No divisor equivalence, module
factorization or local regularity is supplied as an extra premise.
The empty open retains its actual section ring throughout.

Reuse: pinned componentwise module isomorphisms and existing Cartier
fractional membership. The rational multiplication and inverse pattern
was compared with TauCeti d6741e26d8f7aa00504a8845648546fce231065f;
its valuation-defined Weil sheaf and extra hypotheses are not imported.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

local instance rationalShiftSectionCommRing (U : X.Opens) :
    CommRing ((rationalFunctionModule X).val.obj (op U)) :=
  inferInstanceAs (CommRing ((rationalFunctionSheaf X).val.obj (op U)))

/-- The actual global rational unit restricted to the original open. -/
private def rationalUnitOn (q : X.functionFieldˣ) (U : X.Opens) :
    ((rationalFunctionModule X).val.obj (op U))ˣ :=
  Units.map ((rationalFunctionSheaf X).val.map
      (homOfLE (le_top : U ≤ ⊤)).op).hom.toMonoidHom
    (Units.map (rationalFunctionSectionsIso X ⊤).inv.hom.toMonoidHom q)

private theorem rationalUnitOn_restrict (q : X.functionFieldˣ)
    {U V : X.Opens} (i : V ⟶ U) :
    (rationalFunctionSheaf X).val.map i.op
        (rationalUnitOn X q U : (rationalFunctionModule X).val.obj (op U)) =
      (rationalUnitOn X q V : (rationalFunctionModule X).val.obj (op V)) := by
  let r := (rationalFunctionSectionsIso X ⊤).inv (q : X.functionField)
  change (rationalFunctionSheaf X).val.map i.op
      ((rationalFunctionSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op r) =
    (rationalFunctionSheaf X).val.map (homOfLE (le_top : V ≤ ⊤)).op r
  calc
    _ = (rationalFunctionSheaf X).val.map
        ((homOfLE (le_top : U ≤ ⊤)).op ≫ i.op) r :=
      (ConcreteCategory.congr_hom ((rationalFunctionSheaf X).val.map_comp
        (homOfLE (le_top : U ≤ ⊤)).op i.op) r).symm
    _ = _ := congrArg (fun j => (rationalFunctionSheaf X).val.map j r)
      (Subsingleton.elim _ _)

private theorem rationalUnitOn_field (q : X.functionFieldˣ)
    (U : X.Opens) [Nonempty U] :
    Units.map (rationalFunctionSectionsIso X U).hom.hom.toMonoidHom
      (rationalUnitOn X q U) = q := by
  apply Units.ext
  change (rationalFunctionSectionsIso X U).hom
      ((rationalFunctionSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op
        ((rationalFunctionSectionsIso X ⊤).inv (q : X.functionField))) = q
  exact (ConcreteCategory.congr_hom
    (rationalFunctionSectionsIso_naturality X (le_top : U ≤ ⊤))
    ((rationalFunctionSectionsIso X ⊤).inv (q : X.functionField))).trans
      (ConcreteCategory.congr_hom (rationalFunctionSectionsIso X ⊤).inv_hom_id
        (q : X.functionField))

private def rationalFunctionMulSectionEquiv (q : X.functionFieldˣ) (U : X.Opens) :
    (rationalFunctionModule X).val.obj (op U) ≃ₗ[Γ(X, U)]
      (rationalFunctionModule X).val.obj (op U) where
  toFun s := (rationalUnitOn X q U : (rationalFunctionModule X).val.obj (op U)) * s
  invFun s := (↑((rationalUnitOn X q U)⁻¹) :
    (rationalFunctionModule X).val.obj (op U)) * s
  left_inv s := Units.inv_mul_cancel_left _ s
  right_inv s := Units.mul_inv_cancel_left _ s
  map_add' s t := mul_add _ s t
  map_smul' a s := by
    change @Mul.mul ((rationalFunctionSheaf X).val.obj (op U)) inferInstance
        (rationalUnitOn X q U).val
        (@Mul.mul ((rationalFunctionSheaf X).val.obj (op U)) inferInstance
          ((structureToRationalFunctions X).val.app (op U) a) s) =
      @Mul.mul ((rationalFunctionSheaf X).val.obj (op U)) inferInstance
        ((structureToRationalFunctions X).val.app (op U) a)
        (@Mul.mul ((rationalFunctionSheaf X).val.obj (op U)) inferInstance
          (rationalUnitOn X q U).val s)
    exact mul_left_comm _ _ _

/-- Multiplication by a field unit on the actual rational-function module.
The sectionwise inverse is multiplication by its original inverse unit. -/
def rationalFunctionMulIso (q : X.functionFieldˣ) :
    rationalFunctionModule X ≅ rationalFunctionModule X := by
  apply (_root_.SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
  refine _root_.PresheafOfModules.isoMk
    (fun U => (rationalFunctionMulSectionEquiv X q U.unop).toModuleIso) ?_
  intro U V i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change @Mul.mul ((rationalFunctionSheaf X).val.obj V) inferInstance
      (rationalUnitOn X q V.unop).val ((rationalFunctionSheaf X).val.map i s) =
    (rationalFunctionSheaf X).val.map i
      (@Mul.mul ((rationalFunctionSheaf X).val.obj U) inferInstance
        (rationalUnitOn X q U.unop).val s)
  exact (congrArg
    (fun t : (rationalFunctionSheaf X).val.obj V =>
      @Mul.mul ((rationalFunctionSheaf X).val.obj V) inferInstance t
        ((rationalFunctionSheaf X).val.map i s))
    (rationalUnitOn_restrict X q i.unop)).symm.trans
      (((rationalFunctionSheaf X).val.map i).hom.map_mul
        (rationalUnitOn X q U.unop).val s).symm

/-- The forward map is literal multiplication by q in the original field. -/
theorem rationalFunctionMulIso_hom_app_field (q : X.functionFieldˣ)
    (U : X.Opens) [Nonempty U] (s : (rationalFunctionModule X).val.obj (op U)) :
    rationalFunctionModuleSectionsEquiv X U
        ((rationalFunctionMulIso X q).hom.val.app (op U) s) =
      (q : X.functionField) * rationalFunctionModuleSectionsEquiv X U s := by
  change (rationalFunctionSectionsIso X U).hom.hom
      ((rationalUnitOn X q U : (rationalFunctionModule X).val.obj (op U)) * s) = _
  rw [map_mul]
  exact congrArg (fun a : X.functionField => a * rationalFunctionModuleSectionsEquiv X U s)
    (congrArg Units.val (rationalUnitOn_field X q U))

/-- The inverse map is literal multiplication by q⁻¹ in the original field. -/
theorem rationalFunctionMulIso_inv_app_field (q : X.functionFieldˣ)
    (U : X.Opens) [Nonempty U] (s : (rationalFunctionModule X).val.obj (op U)) :
    rationalFunctionModuleSectionsEquiv X U
        ((rationalFunctionMulIso X q).inv.val.app (op U) s) =
      (↑(q⁻¹) : X.functionField) * rationalFunctionModuleSectionsEquiv X U s := by
  change (rationalFunctionSectionsIso X U).hom.hom
      ((↑((rationalUnitOn X q U)⁻¹) : (rationalFunctionModule X).val.obj (op U)) * s) = _
  rw [map_mul]
  have h : Units.map (rationalFunctionSectionsIso X U).hom.hom.toMonoidHom
      ((rationalUnitOn X q U)⁻¹) = q⁻¹ := by
    rw [map_inv, rationalUnitOn_field]
  exact congrArg (fun a : X.functionField => a * rationalFunctionModuleSectionsEquiv X U s)
    (congrArg Units.val h)

/-- A principal divisor retains its original equation on every nonempty open. -/
theorem principalCartierDivisor_equation (q : X.functionFieldˣ)
    (U : X.Opens) [Nonempty U] :
    cartierEquationClassHom X U (Additive.ofMul q) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op
        (principalCartierDivisorHom X (Additive.ofMul q)) :=
  (cartierEquationClassHom_restrict X (le_top : U ≤ ⊤) q).symm

private theorem cartierPrincipalShift_hom_mem (D : CartierDivisor X)
    (q : X.functionFieldˣ) (U : X.Opens)
    (s : (cartierDivisorModule X
      (D + principalCartierDivisorHom X (Additive.ofMul q))).val.obj (op U)) :
    (rationalFunctionMulIso X q).hom.val.app (op U) s.val ∈
      cartierSectionSubmodule X D U := by
  intro V i hV f hf
  letI := hV
  have hsum := cartierGlobalEquation_mul X D
    (principalCartierDivisorHom X (Additive.ofMul q)) V f q hf
    (principalCartierDivisor_equation X q V)
  obtain ⟨a, ha⟩ := (mem_principalEquationSubmodule_iff X V (f * q) _).mp
    (s.property V i hV (f * q) hsum)
  rw [← _root_.PresheafOfModules.naturality_apply,
    rationalFunctionMulIso_hom_app_field]
  apply (mem_principalEquationSubmodule_iff X V f _).mpr
  refine ⟨a, ?_⟩
  exact ha.trans (mul_assoc (f : X.functionField) (q : X.functionField) _)

private theorem cartierPrincipalShift_inv_mem (D : CartierDivisor X)
    (q : X.functionFieldˣ) (U : X.Opens)
    (s : (cartierDivisorModule X D).val.obj (op U)) :
    (rationalFunctionMulIso X q).inv.val.app (op U) s.val ∈
      cartierSectionSubmodule X
        (D + principalCartierDivisorHom X (Additive.ofMul q)) U := by
  intro V i hV f hf
  letI := hV
  have hcancel : (D + principalCartierDivisorHom X (Additive.ofMul q)) +
      principalCartierDivisorHom X (Additive.ofMul (q⁻¹)) = D := by
    change (D + principalCartierDivisorHom X (Additive.ofMul q)) +
      principalCartierDivisorHom X (-(Additive.ofMul q)) = D
    rw [map_neg, add_neg_cancel_right]
  have hD := cartierGlobalEquation_mul X
    (D + principalCartierDivisorHom X (Additive.ofMul q))
    (principalCartierDivisorHom X (Additive.ofMul (q⁻¹))) V f (q⁻¹) hf
    (principalCartierDivisor_equation X (q⁻¹) V)
  rw [hcancel] at hD
  obtain ⟨a, ha⟩ := (mem_principalEquationSubmodule_iff X V (f * q⁻¹) _).mp
    (s.property V i hV (f * q⁻¹) hD)
  rw [← _root_.PresheafOfModules.naturality_apply,
    rationalFunctionMulIso_inv_app_field]
  apply (mem_principalEquationSubmodule_iff X V f _).mpr
  refine ⟨a, ?_⟩
  exact ha.trans (mul_assoc (f : X.functionField) (↑(q⁻¹) : X.functionField) _)

private def cartierPrincipalShiftSectionEquiv (D : CartierDivisor X)
    (q : X.functionFieldˣ) (U : X.Opens) :
    (cartierDivisorModule X
        (D + principalCartierDivisorHom X (Additive.ofMul q))).val.obj (op U) ≃ₗ[Γ(X, U)]
      (cartierDivisorModule X D).val.obj (op U) where
  toFun s := ⟨rationalFunctionMulSectionEquiv X q U s.val,
    cartierPrincipalShift_hom_mem X D q U s⟩
  invFun s := ⟨(rationalFunctionMulSectionEquiv X q U).symm s.val,
    cartierPrincipalShift_inv_mem X D q U s⟩
  left_inv s := Subtype.ext ((rationalFunctionMulSectionEquiv X q U).left_inv s.val)
  right_inv s := Subtype.ext ((rationalFunctionMulSectionEquiv X q U).right_inv s.val)
  map_add' s t := Subtype.ext ((rationalFunctionMulSectionEquiv X q U).map_add s.val t.val)
  map_smul' a s := Subtype.ext ((rationalFunctionMulSectionEquiv X q U).map_smul a s.val)

/-- Multiplication by q identifies the original O(D + div(q)) with O(D). -/
def cartierPrincipalShiftIso (D : CartierDivisor X) (q : X.functionFieldˣ) :
    cartierDivisorModule X (D + principalCartierDivisorHom X (Additive.ofMul q)) ≅
      cartierDivisorModule X D := by
  apply (_root_.SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
  refine _root_.PresheafOfModules.isoMk
    (fun U => (cartierPrincipalShiftSectionEquiv X D q U.unop).toModuleIso) ?_
  intro U V i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  exact _root_.PresheafOfModules.naturality_apply (rationalFunctionMulIso X q).hom.val i s.val

/-- The constructed forward map retains its original rational inclusion. -/
@[reassoc]
theorem cartierPrincipalShiftIso_hom_inclusion (D : CartierDivisor X)
    (q : X.functionFieldˣ) :
    (cartierPrincipalShiftIso X D q).hom ≫ cartierDivisorModuleInclusion X D =
      cartierDivisorModuleInclusion X
          (D + principalCartierDivisorHom X (Additive.ofMul q)) ≫
        (rationalFunctionMulIso X q).hom := rfl

/-- The constructed inverse retains the inverse rational multiplication. -/
@[reassoc]
theorem cartierPrincipalShiftIso_inv_inclusion (D : CartierDivisor X)
    (q : X.functionFieldˣ) :
    (cartierPrincipalShiftIso X D q).inv ≫ cartierDivisorModuleInclusion X
        (D + principalCartierDivisorHom X (Additive.ofMul q)) =
      cartierDivisorModuleInclusion X D ≫ (rationalFunctionMulIso X q).inv := rfl

/-- The Cartier isomorphism has the same multiplication formula on sections. -/
theorem cartierPrincipalShiftIso_hom_app_field (D : CartierDivisor X)
    (q : X.functionFieldˣ) (U : X.Opens) [Nonempty U]
    (s : (cartierDivisorModule X
      (D + principalCartierDivisorHom X (Additive.ofMul q))).val.obj (op U)) :
    rationalFunctionModuleSectionsEquiv X U
        ((cartierPrincipalShiftIso X D q).hom.val.app (op U) s).val =
      (q : X.functionField) * rationalFunctionModuleSectionsEquiv X U s.val :=
  rationalFunctionMulIso_hom_app_field X q U s.val

end KltDP.Geometry
