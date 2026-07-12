/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Preadditive.FreydCategory.RightFreyd
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Tactic.ApplyFun

/-!

# Functoriality of the right Freyd category

-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Arrow Preadditive RightFreyd

variable {V₁ : Type*} [Category* V₁] [Preadditive V₁] {V₂ : Type*} [Category* V₂] [Preadditive V₂]
  (G : V₁ ⥤ V₂) [G.Additive]
  {C : Type*} [Category* C] [Preadditive C] [HasCokernels C] (F : V₁ ⥤ C) [F.Additive]

namespace CategoryTheory

namespace Functor

set_option backward.isDefEq.respectTransparency false in
@[simps!]
def mapRightFreyd : RightFreyd V₁ ⥤ RightFreyd V₂ :=
  Quotient.lift (rightHomotopic V₁) (G.mapArrow ⋙ quotient V₂)
  (fun _ _ _ _ ⟨h⟩ ↦ (eq_of_rightHomotopy _ _ ⟨G.map h.hom, by simp [← G.map_sub, h.comm]; rfl⟩))

def mapRightFreyd_comp_quotient : quotient V₁ ⋙ G.mapRightFreyd ≅ G.mapArrow ⋙ quotient V₂ :=
  Quotient.lift.isLift _ _ _

set_option backward.isDefEq.respectTransparency false in
instance : G.mapRightFreyd.Additive where
  map_add {_ _} f g := by
    obtain ⟨f, rfl⟩ := (quotient V₁).map_surjective f
    obtain ⟨g, rfl⟩ := (quotient V₁).map_surjective g
    change (quotient V₂).map _ = (quotient V₂).map _ + (quotient V₂).map _
    rw [← (quotient V₂).map_add]
    simp
    rfl

set_option backward.isDefEq.respectTransparency false in
@[simps!]
def mapRightFreyd_id : (𝟭 V₁).mapRightFreyd ≅ 𝟭 (RightFreyd V₁) :=
  Quotient.natIsoLift _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp; rfl))

variable {V₃ : Type*} [Category* V₃] [Preadditive V₃] (H : V₂ ⥤ V₃) [H.Additive]

set_option backward.isDefEq.respectTransparency false in
@[simps!]
def mapRightFreyd_comp : (G ⋙ H).mapRightFreyd ≅ G.mapRightFreyd ⋙ H.mapRightFreyd :=
  Quotient.natIsoLift _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp; rfl))

variable [HasZeroObject V₁] [HasZeroObject V₂] in
def functorMapRightFreydIso : functor V₁ ⋙ G.mapRightFreyd ≅ G ⋙ functor V₂ :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Quotient.lift.isLift _ _ _) ≪≫
  Functor.isoWhiskerRight (rightFunctorMapArrowIso G) (quotient V₂)

set_option backward.isDefEq.respectTransparency false in
def preservesCokernels_mapRightFreyd_aux {u v : Arrow V₁} (f : u ⟶ v)
    [HasBinaryBiproduct v.left u.right] :
    IsColimit (G.mapRightFreyd.mapCocone (Candidate.cokernelCofork f)) := by
  have : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts _
  have Gb : HasBinaryBiproduct (G.obj v.left) (G.obj u.right) :=
    G.hasBinaryBiproduct_of_preserves _ _
  have : HasBinaryBiproduct (G.mapArrow.obj v).left (G.mapArrow.obj u).right := Gb
  set c := Candidate.cokernelCofork (G.mapArrow.map f)
  set c' := G.mapRightFreyd.mapCocone (Candidate.cokernelCofork f)
  set α : parallelPair ((quotient V₁).map f) 0 ⋙ G.mapRightFreyd ≅
      parallelPair ((quotient V₂).map (G.mapArrow.map f)) 0 := by
    refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_
    · simp; rfl
    · simp only [parallelPair_obj_zero, parallelPair_obj_one, parallelPair_map_right, Iso.refl_hom,
      comp_id, comp_map, id_comp]
      rw [G.mapRightFreyd.map_zero]
  set e : c' ≅ (Cocone.precompose α.hom).obj c := by
    refine Cocone.ext ?_ (fun j ↦ ?_)
    · refine G.mapRightFreyd_comp_quotient.app _ ≪≫ (quotient V₂).mapIso
        (Arrow.isoMk (G.mapBiprod _ _) (Iso.refl _) ?_)
      simp only [biprod.uniqueUpToIso_hom, mapBinaryBicone_fst, BinaryBiproduct.bicone_fst,
        mapBinaryBicone_snd, BinaryBiproduct.bicone_snd, mk_hom, mapArrow_map, homMk_right,
        biprod.lift_desc, Iso.refl_hom, comp_id]
      change _ ≫ G.map _ + _ = _
      rw [← G.map_comp, ← G.map_comp, ← G.map_add]
      refine congrArg G.map (by cat_disch)
    · match j with
      | .zero => simp only [mapCocone_ι_app, parallelPair_obj_zero, Cofork.app_zero_eq_comp_π_left,
        CokernelCofork.condition, Iso.trans_hom, Iso.app_hom, mapIso_hom,
        Cocone.precompose_obj_ι, NatTrans.comp_app, mapArrow_map, comp_zero,
        IsIso.comp_right_eq_zero, c, c']
                 exact G.mapRightFreyd.map_zero _ _
      | .one => refine congrArg (quotient V₂).map ?_
                ext
                · have : HasBinaryBiproduct (G.mapArrow.obj v).left (G.obj u.right) := Gb
                  have : HasBinaryBiproduct (G.obj v.left) (G.mapArrow.obj u).right := Gb
                  simp only [parallelPair_obj_one, Candidate.π, mapArrow_map, homMk_left,
                    homMk_right, comp_left, id_left, isoMk_hom_left, biprod.uniqueUpToIso_hom,
                    mapBinaryBicone_fst, BinaryBiproduct.bicone_fst, mapBinaryBicone_snd,
                    BinaryBiproduct.bicone_snd, id_comp]
                  erw [id_comp]
                  refine biprod.hom_ext _ _ ?_ ?_
                  · simp only [assoc, BinaryBicone.inl_fst]
                    erw [biprod.lift_fst]
                    rw [← G.map_comp]
                    have : HasBinaryBiproduct ((quotient V₁).obj v).as.left u.right :=
                      inferInstanceAs (HasBinaryBiproduct v.left u.right)
                    erw [biprod.inl_fst]
                    exact G.map_id _
                  · simp only [assoc, BinaryBicone.inl_snd]
                    erw [biprod.lift_snd]
                    rw [← G.map_comp]
                    have : HasBinaryBiproduct ((quotient V₁).obj v).as.left u.right :=
                      inferInstanceAs (HasBinaryBiproduct v.left u.right)
                    erw [biprod.inl_snd]
                    exact G.map_zero _ _
                · simp only [parallelPair_obj_one, Candidate.π, mapArrow_map, homMk_left,
                  homMk_right, comp_right, id_right, isoMk_hom_right, Iso.refl_hom, id_comp]
                  erw [id_comp, comp_id]
                  exact G.map_id _
  refine IsColimit.ofIsoColimit ?_ e.symm
  refine (IsColimit.precomposeHomEquiv α _).invFun ?_
  exact Candidate.isColimitCokernelCofork _

variable [HasBinaryBiproducts V₁]

set_option backward.isDefEq.respectTransparency false in
def preservesCokernels_mapRightFreyd {u v : RightFreyd V₁} (f : u ⟶ v) {c : CokernelCofork f}
    (hc : IsColimit c) : IsColimit (G.mapRightFreyd.mapCocone c) :=
  let h := (quotient V₁).map_surjective f
  let α : parallelPair f 0 ≅ parallelPair ((quotient V₁).map h.choose) 0 :=
    parallelPair.ext (eqToIso rfl) (eqToIso rfl) (by simp [h.choose_spec])
  IsColimit.ofIsoColimit (IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv
    (Functor.isoWhiskerRight α G.mapRightFreyd) _ ).invFun (preservesCokernels_mapRightFreyd_aux G
    h.choose)) G.mapRightFreyd.mapCoconePrecompose.symm)
    ((Cocone.functoriality _ G.mapRightFreyd).mapIso (hc.uniqueUpToIso
    ((IsColimit.precomposeHomEquiv α (Candidate.cokernelCofork h.choose)).invFun
    (Candidate.isColimitCokernelCofork h.choose)))).symm

variable [HasFiniteProducts V₁]

instance : HasFiniteProducts (Arrow V₁) where
  out _ := inferInstance

instance : HasFiniteProducts (RightFreyd V₁) :=
  have : (quotient V₁).EssSurj := inferInstance
  (quotient V₁).hasFiniteProducts_of_additive_of_essSurj

instance : PreservesFiniteColimits G.mapRightFreyd := by
  have : HasBinaryBiproducts (RightFreyd V₁) := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasFiniteBiproducts (RightFreyd V₁) := HasFiniteBiproducts.of_hasFiniteProducts
  have : HasBinaryBiproducts V₁ := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasCoequalizers (RightFreyd V₁) := Preadditive.hasCoequalizers_of_hasCokernels
  have : HasZeroObject V₁ := hasZeroObject_of_hasTerminal_object
  have : HasZeroObject (RightFreyd V₂) := G.mapRightFreyd.hasZeroObject_of_additive
  have : ∀ {X Y : RightFreyd V₁} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) G.mapRightFreyd :=
    fun f ↦ {preserves hc := Nonempty.intro (preservesCokernels_mapRightFreyd G f hc)}
  exact G.mapRightFreyd.preservesFiniteColimits_of_preservesCokernels

end Functor

namespace NatTrans

variable {G} {G' G'' : V₁ ⥤ V₂} [G'.Additive] [G''.Additive] (α : G ⟶ G')

def mapRightFreyd : G.mapRightFreyd ⟶ G'.mapRightFreyd :=
  Quotient.natTransLift _ ((Quotient.lift.isLift _ _ _).hom ≫ Functor.whiskerRight
  ((Functor.mapArrowFunctor V₁ V₂).map α) (quotient V₂) ≫ (Quotient.lift.isLift _ _ _).inv)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma mapRightFreyd_app (a : RightFreyd V₁) : α.mapRightFreyd.app a =
    (quotient V₂).map (homMk (α.app a.as.left) (α.app a.as.right) (α.naturality a.as.hom).symm):=
  (id_comp _).trans (comp_id _)

@[simp]
lemma mapRightFreyd_id : NatTrans.mapRightFreyd (𝟙 G) = 𝟙 G.mapRightFreyd := by cat_disch

@[simp]
lemma mapRightFreyd_comp (β : G' ⟶ G'') :
    (α ≫ β).mapRightFreyd = α.mapRightFreyd ≫ β.mapRightFreyd := by cat_disch

end NatTrans

namespace Functor

@[simps]
def mapRightFreydFunctor : (V₁ ⥤+ V₂) ⥤ (RightFreyd V₁ ⥤ RightFreyd V₂) where
  obj F := Functor.mapRightFreyd F.1
  map {F G} α := α.hom.mapRightFreyd

end Functor

end CategoryTheory
