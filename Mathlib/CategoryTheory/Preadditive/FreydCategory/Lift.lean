/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Preadditive.FreydCategory.RightFreyd
public import Mathlib.CategoryTheory.Preadditive.FreydCategory.Functoriality
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Tactic.ApplyFun

/-!

# Lifting functors to the right Freyd category

-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Arrow

variable {V : Type*} [Category* V] [Preadditive V]
  {C : Type*} [Category* C] [Preadditive C] [HasCokernels C] (F : V ⥤ C) [F.Additive]

namespace CategoryTheory.Preadditive

namespace RightFreyd

section Lift

/-- If `C` is a preadditive category with cokernels, any additive functor `F : V ⥤ C`
extends to an additive functor `functorLift F : RightFreyd V ⥤ C` by sending an object of
`RightFreyd V` represented by `u : Arrow V` to the cokernel of `F.map u`. -/
@[simps!]
def functorLift : RightFreyd V ⥤ C := F.mapRightFreyd ⋙ projection C

instance : (RightFreyd.functorLift F).Additive := by
  dsimp [functorLift]
  infer_instance

def functorLiftIsLift [HasZeroObject V] [HasZeroObject C] : functor V ⋙ functorLift F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight F.functorMapRightFreydIso
  (projection C) ≪≫ Functor.associator _ _ _ ≪≫ F.isoWhiskerLeft (functorProjectionIso C)
  ≪≫ F.rightUnitor

/-- If `C` is a preadditive category with cokernels and `F : V ⥤ C` is an additive functor,
the composition of `functor : V ⥤ RightFreyd V` and of `functorLift F` is isomorphic to `F`. -/
def functorLiftIso [HasZeroObject V] [HasZeroObject C] : functor V ⋙ functorLift F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight F.functorMapRightFreydIso
  (projection C) ≪≫ Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F (functorProjectionIso C)
  ≪≫ F.rightUnitor

variable [HasZeroObject V] [HasBinaryBiproducts V]

def functorLiftUnique (G : RightFreyd V ⥤ C) [G.Additive] [PreservesFiniteColimits G] :
    functorLift (functor V ⋙ G) ≅ G := by
  dsimp [functorLift]
  refine NatIso.ofComponents (fun a ↦ ?_) (fun {a b} f ↦ ?_)
  · sorry
  · sorry



#exit

variable {F} {F' : V ⥤ C} [F'.Additive]

set_option backward.isDefEq.respectTransparency false in
/-- If `α : F ⟶ F'` is a morphism between additive functors `V ⥤ C`, it lifts to a morphism
`natTransLiftAux α : functorLiftAux F ⟶ functorLiftAux F'`. -/
@[simps!]
def natTransLiftAux (α : F ⟶ F') : functorLiftAux F ⟶ functorLiftAux F' where
  app u := cokernel.map _ _ (α.app u.left) (α.app u.right) (α.naturality u.hom)
  naturality _ _ _ := (cancel_epi (cokernel.π _)).mp (by simp [functorLiftAux])

/-- If `α : F ⟶ F'` is a morphism between additive functors `V ⥤ C`, it lifts to a morphism
`natTransLift α : functorLift F ⟶ functorLift F'`. -/
@[simps!]
def natTransLift (α : F ⟶ F') : functorLift F ⟶ functorLift F' :=
  Quotient.natTransLift _ (natTransLiftAux α)

variable (F) in
lemma natTransLift_id : natTransLift (𝟙 F) = 𝟙 (functorLift F) := by cat_disch

set_option backward.isDefEq.respectTransparency false in
lemma natTransLift_comp {F'' : V ⥤ C} [F''.Additive] (α : F ⟶ F') (β : F' ⟶ F'') :
    natTransLift (α ≫ β) = natTransLift α ≫ natTransLift β := by
  ext
  refine (cancel_epi (cokernel.π _)).mp (by simp)

variable (F) [HasZeroObject V]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma functorLiftIso_inv_app (X : V) :
    (functorLiftIso F).inv.app X = cokernel.π (F.map ((rightFunctor V).obj X).hom) := by
  dsimp [functorLiftIso, functorLiftAux, rightFunctor]
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, assoc, NatTrans.comp_app,
    rightFunctorLiftAuxIso_inv_app, Functor.whiskerLeft_app, Quotient.lift.isLift_inv,
    Functor.associator_inv_app, comp_id]
  exact comp_id _

def functorLiftAuxUnique (G : Arrow V ⥤ C) [G.Additive] [PreservesFiniteColimits G] :
    functorLiftAux (rightFunctor V ⋙ G) ≅ G := by
  refine NatIso.ofComponents (fun u ↦ ?_) ?_
  · simp [rightFunctor, functorLiftAux]
    sorry
  · sorry

variable [HasBinaryBiproducts V]

def functorLiftUnique (G : RightFreyd V ⥤ C) [G.Additive] [PreservesFiniteColimits G] :
    functorLift (functor V ⋙ G) ≅ G := by
  refine NatIso.ofComponents (fun a ↦ ?_) (fun {a b} f ↦ ?_)
  · set e := quotient_obj_surjective a
    rw [← e.choose_spec]
    refine (PreservesCokernel.iso G ((functor V).map e.choose.hom)).symm ≪≫ G.mapIso ?_
    exact (cokernelIsCokernel _).coconePointUniqueUpToIso (coforkRightFunctorIsColimit e.choose)
  · set e := quotient_obj_surjective a
    set f := quotient_obj_surjective b
    simp


/-
lemma functorLiftUnique_naturality (G G' : RightFreyd V ⥤ C) [G.Additive] [G'.Additive]
    (α : G ⟶ G') :
    ((lift V C).map ((shrink V C).map α)).hom.app x✝ ≫ (functorLiftUnique Y✝.obj).hom.app x✝ =
  (functorLiftUnique X✝.obj).hom.app x✝ ≫ α.hom.app x✝
-/

end Lift

section PreservesCokernels

variable [HasBinaryBiproducts V]

variable {u v : Arrow V} (f : u ⟶ v)

set_option backward.isDefEq.respectTransparency false in
def pi : cokernel (F.map v.hom) ⟶ cokernel (F.map ((Candidate.cokernel f).hom)) := by
  refine cokernel.desc _ (cokernel.π (F.map ((Candidate.cokernel f).hom))) ?_
  have := (Candidate.π f).w
  dsimp [Candidate.π] at this
  simp only [Arrow.homMk_left, Arrow.homMk_right, comp_id] at this
  apply_fun F.map at this
  rw [← this, F.map_comp, assoc, cokernel.condition, comp_zero]

set_option backward.isDefEq.respectTransparency false in
instance : Epi (pi F f) := by
    refine epi_of_epi_fac (f := cokernel.π (F.map v.hom))
      (h := cokernel.π (F.map (Candidate.cokernel f).hom)) ?_
    simp [pi]

set_option backward.isDefEq.respectTransparency false in
def cc : CokernelCofork ((functorLift F).map ((quotient V).map f)) := by
  refine CokernelCofork.ofπ (pi F f) ?_
  rw [← cancel_epi (cokernel.π (F.map u.hom))]
  simp only [Candidate.cokernel, functorLift_map, functorLiftAux, pi,
    cokernel.π_desc_assoc, assoc, cokernel.π_desc, comp_zero]
  have := cokernel.condition (F.map ((Candidate.cokernel f).hom))
  simp only [Candidate.cokernel, mk_hom] at this
  apply_fun (fun x ↦ F.map (biprod.inr (X := v.left) (Y := u.right)) ≫ x) at this
  rw [← F.map_comp_assoc, biprod.inr_desc, comp_zero] at this
  exact this

set_option backward.isDefEq.respectTransparency false in
def e₀ : (parallelPair ((quotient V).map f) 0 ⋙ functorLift F) ≅
    parallelPair ((functorLift F).map ((quotient V).map f)) 0 :=
  diagramIsoParallelPair (parallelPair ((quotient V).map f) 0 ⋙ functorLift F) ≪≫
  parallelPair.ext (Iso.refl _) (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
def e : (functorLift F).mapCocone (CandidateCokernelCofork f) ≅ (Cocone.precompose
    (e₀ F f).hom).obj (cc F f) := by
  refine Cocone.ext (Iso.refl _) (fun j ↦ ?_)
  match j with
  | .zero => simp
  | .one =>
    rw [← cancel_epi (cokernel.π _)]
    simp only [parallelPair_obj_one, e₀, Functor.comp_map, parallelPair_obj_zero,
      parallelPair_map_left, parallelPair_map_right, Candidate.cokernel,
      CandidateCokernelCofork, Candidate.π, Functor.mapCocone_ι_app, Cofork.ofπ_ι_app,
      functorLift_map, functorLiftAux, homMk_left, homMk_right, Functor.map_id,
      Iso.refl_hom, comp_id, Cocone.precompose_obj_ι, Iso.trans_hom, assoc, NatTrans.comp_app,
      diagramIsoParallelPair_hom_app, eqToHom_refl, parallelPair.ext_hom_app, id_comp]
    refine (cokernel.π_desc _ _ _).trans ?_
    rw [id_comp]
    exact (cokernel.π_desc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
def colim_desc (s : Cofork ((functorLift F).map ((quotient V).map f)) 0) : (cc F f).pt ⟶ s.pt := by
  refine cokernel.desc _ (cokernel.π _ ≫ Cofork.π s) ?_
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  rw [← cancel_epi (F.mapBiprod v.left u.right).inv]
  simp only [biprod.uniqueUpToIso_inv, Functor.mapBinaryBicone_inl, BinaryBiproduct.bicone_inl,
    Functor.mapBinaryBicone_inr, BinaryBiproduct.bicone_inr, Candidate.cokernel, mk_hom,
    comp_zero]
  ext
  · simp only [biprod.inl_desc_assoc, comp_zero]
    rw [← F.map_comp_assoc, biprod.inl_desc]
    exact (cokernel.condition_assoc (F.map v.hom) _).trans zero_comp
  · simp only [biprod.inr_desc_assoc, comp_zero]
    rw [← F.map_comp_assoc, biprod.inr_desc, ← assoc]
    change (_ ≫ cokernel.π (F.map v.hom)) ≫ _ = _
    rw [← cokernel.π_desc (F.map u.hom) (F.map (Hom.right f) ≫ cokernel.π (F.map v.hom))
      (by rw [← F.map_comp_assoc, ← f.w, F.map_comp, assoc, cokernel.condition, comp_zero]), assoc]
    convert comp_zero
    have := Cofork.condition s
    simp only [functorLift_map, functorLiftAux, zero_comp] at this
    exact this

set_option backward.isDefEq.respectTransparency false in
lemma colim_fac (s : Cofork ((functorLift F).map ((quotient V).map f)) 0) :
    (cc F f).π ≫ colim_desc F f s = s.π := by
  rw [← cancel_epi (cokernel.π _)]
  exact (cokernel.π_desc_assoc _ _ _ _).trans (cokernel.π_desc _ _ _)

def colim : IsColimit (cc F f) := by
  refine Cofork.IsColimit.mk _ (colim_desc F f) (colim_fac F f) (fun s m hm ↦ ?_)
  rw [← colim_fac F f s] at hm
  exact (cancel_epi (pi F f)).mp hm

def iscolim : IsColimit ((functorLift F).mapCocone (CandidateCokernelCofork f)) :=
  ((IsColimit.precomposeHomEquiv (e₀ F f) _).invFun (colim F f)).ofIsoColimit (e F f).symm

set_option backward.isDefEq.respectTransparency false in
def preservesCokernel_functorLift {u v : RightFreyd V} (f : u ⟶ v) {c : CokernelCofork f}
    (hc : IsColimit c) : IsColimit ((functorLift F).mapCocone c) := by
  set g := ((quotient V).map_surjective f).choose
  set eq : (quotient V).map g = f := ((quotient V).map_surjective f).choose_spec
  set e : parallelPair ((quotient V).map g) 0 ≅ parallelPair f 0 :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [eq])
  set e' := ((IsColimit.precomposeHomEquiv e.symm _).invFun
    (candidateCokernelCoforkIsCokernel g)).uniqueUpToIso hc
  set e'' : (functorLift F).mapCocone _ ≅ (functorLift F).mapCocone c :=
    (Cocone.functoriality (parallelPair f 0) (functorLift F)).mapIso e'
  set e''' := (functorLift F).mapCoconePrecompose (α := e.symm.hom) (c := CandidateCokernelCofork g)
  exact (((IsColimit.precomposeHomEquiv (Functor.isoWhiskerRight e.symm (functorLift F))
    ((functorLift F).mapCocone (CandidateCokernelCofork g))).invFun (iscolim F g)).ofIsoColimit
    e'''.symm).ofIsoColimit e''

end PreservesCokernels

section RightExact

variable [HasFiniteProducts V]

instance : HasFiniteProducts (Arrow V) where
  out _ := inferInstance

instance : HasFiniteProducts (RightFreyd V) :=
  have : (quotient V).EssSurj := inferInstance
  (quotient V).hasFiniteProducts_of_additive_of_essSurj

instance : PreservesFiniteColimits (functorLift F) := by
  have : HasBinaryBiproducts (RightFreyd V) := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasFiniteBiproducts (RightFreyd V) := HasFiniteBiproducts.of_hasFiniteProducts
  have : HasBinaryBiproducts V := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasCoequalizers (RightFreyd V) := Preadditive.hasCoequalizers_of_hasCokernels
  have : HasZeroObject V := hasZeroObject_of_hasTerminal_object
  have : HasZeroObject C := F.hasZeroObject_of_additive
  have : ∀ {X Y : RightFreyd V} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) (functorLift F) :=
    fun f ↦ {preserves hc := Nonempty.intro (preservesCokernel_functorLift F f hc)}
  exact (functorLift F).preservesFiniteColimits_of_preservesCokernels

end RightExact

section UniversalProperty

variable (V C) [HasFiniteProducts V] [HasZeroObject C]

local instance : HasZeroObject V := hasZeroObject_of_hasTerminal_object

local instance : HasBinaryBiproducts (RightFreyd V) := HasBinaryBiproducts.of_hasBinaryProducts

def liftAux : (V ⥤+ C) ⥤ (RightFreyd V ⥤ C) where
  obj F :=
    letI := F.2
    functorLift F.1
  map {F G} α :=
    letI := F.2
    letI := G.2
    natTransLift α.hom
  map_comp _ _ := natTransLift_comp _ _

def lift : (V ⥤+ C) ⥤ (RightFreyd V ⥤ᵣ C) :=
  ObjectProperty.lift _ (liftAux V C)
  (fun F ↦ inferInstanceAs (PreservesFiniteColimits (functorLift F.1)))

def shrink : (RightFreyd V ⥤ᵣ C) ⥤ (V ⥤+ C) := by
  refine ObjectProperty.lift _ ?_ ?_
  · exact AdditiveFunctor.ofRightExact _ _ ⋙ ObjectProperty.ι (additiveFunctor _ _) ⋙
      (Functor.whiskeringLeft _ _ _).obj (functor V)
  · intro F
    have : F.1.Additive := rightExactFunctor_le_additiveFunctor _ _  _ F.2
    exact inferInstanceAs ((functor V ⋙ F.1).Additive)

set_option backward.isDefEq.respectTransparency false in
def lift_shrink : lift V C ⋙ shrink V C ≅ 𝟭 (V ⥤+ C) := by
  refine NatIso.ofComponents (fun F ↦ ?_) ?_
  · exact ObjectProperty.isoMk _ (functorLiftIso F.1)
  · intro F G α
    ext X
    dsimp [shrink, lift, liftAux, functorLiftIso]
    simp only [ObjectProperty.lift_map, Functor.comp_map, ObjectProperty.ιOfLE_map,
      ObjectProperty.homMk_hom, ObjectProperty.ι_obj, AdditiveFunctor.ofRightExact_obj_fst,
      ObjectProperty.ι_map, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app,
      natTransLift_app, ObjectProperty.isoMk_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.associator_hom_app, Quotient.lift.isLift_hom,
      rightFunctorLiftAuxIso_hom_app, assoc]
    erw [id_comp, id_comp, id_comp, id_comp]
    rw [← cancel_epi ((cokernel.π (F.obj.map ((rightFunctor V).obj X).hom))),
      IsIso.hom_inv_id_assoc]
    erw [cokernel.π_desc_assoc, assoc, IsIso.hom_inv_id]
    exact comp_id _

variable [HasBinaryBiproducts V] in
def shrink_lift : shrink V C ⋙ lift V C ≅ 𝟭 (RightFreyd V ⥤ᵣ C) := by
  refine NatIso.ofComponents (fun F ↦ ?_) (fun α ↦ ?_)
  · have : F.1.Additive := rightExactFunctor_le_additiveFunctor _ _  _ F.2
    exact ObjectProperty.isoMk _ (functorLiftUnique F.1)
  · refine (ObjectProperty.ι _).map_injective ?_
    dsimp
    ext
    dsimp
    simp
    sorry

end UniversalProperty

end RightFreyd

end CategoryTheory.Preadditive
