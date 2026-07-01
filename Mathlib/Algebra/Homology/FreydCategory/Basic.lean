/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Homology.FreydCategory.ArrowHomotopy
public import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Homotopies in the arrow category

We define left and right homotopies between arrows.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex Arrow

variable (V : Type*) [Category* V] [Preadditive V]

namespace CategoryTheory.Preadditive

section RightFunctor

variable [HasZeroObject V]

/-- If `V` has a zero object, the functor from `V` to `Arrow V` that sends an object `X`
to the arrow `0 ⟶ X`. -/
def rightFunctor : V ⥤ Arrow V where
  obj X := Arrow.mk 0
  map f := Arrow.homMk 0 f (HasZeroObject.from_zero_ext _ _)
  map_id _ := by
    ext
    · exact HasZeroObject.from_zero_ext _ _
    · rfl

instance : (rightFunctor V).Additive where
  map_add {_ _ _ _} := by
    ext
    · exact HasZeroObject.from_zero_ext _ _
    · rfl

end RightFunctor

/-- If `V` is a preadditive category, then `RightFreyd V` is the category of arrows in `V`,
with morphisms identified when they are right homotopic. -/
def RightFreyd :=
  CategoryTheory.Quotient (rightHomotopic V)

instance : Category (RightFreyd V) :=
  inferInstanceAs <| Category (CategoryTheory.Quotient (rightHomotopic V))

namespace RightFreyd

instance : Preadditive (CategoryTheory.Quotient (rightHomotopic V)) :=
  Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨RightHomotopy.add h h'⟩)

instance : Preadditive (RightFreyd V) :=
  inferInstanceAs <| Preadditive (CategoryTheory.Quotient (rightHomotopic V))

/-- The quotient functor from `Arrow V` to `RightFreyd V`. -/
def quotient : Arrow V ⥤ RightFreyd V :=
  CategoryTheory.Quotient.functor _

instance : (quotient V).Full := Quotient.full_functor _

instance : (quotient V).EssSurj := Quotient.essSurj_functor _

instance : (quotient V).Additive where

variable {V}

/-- If two morphisms in `Arrow V` are right homotopic, then they become equal in the right
Freyd category. -/
theorem eq_of_rightHomotopy {u v : Arrow V} (f g : u ⟶ v) (h : RightHomotopy f g) :
    (quotient V).map f = (quotient V).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/-- If two morphisms of `Arrow V` become equal in the right Freyd category,
then they are right homotopic. -/
def homotopyOfEq {u v : Arrow V} (f g : u ⟶ v)
    (w : (quotient V).map f = (quotient V).map g) : RightHomotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp w).some

variable {u v : Arrow V} (f g : u ⟶ v)

lemma quotient_map_eq_iff :
    (quotient V).map f = (quotient V).map g ↔ Nonempty (RightHomotopy f g) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_rightHomotopy _ _ h⟩

lemma quotient_map_eq_zero_iff : (quotient V).map f = 0 ↔ Nonempty (RightHomotopy f 0) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_rightHomotopy _ _ h⟩

/--
If `f` is a morphism of `Arrow V` such that `f.right` is an isomorphism, then the image of `f`
in the right Freyd category is an epimorphism. -/
lemma isEpi_of_right_iso [IsIso f.right] : Epi ((quotient V).map f) where
  left_cancellation g₁ g₂ eq := by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    apply eq_of_rightHomotopy
    set h : RightHomotopy (f ≫ g₁) (f ≫ g₂) := homotopyOfEq _ _ eq
    exact ⟨inv f.right ≫ h.hom, by simp [dsimp% h.comm]⟩

section Functor

variable (V) [HasZeroObject V]

def functor : V ⥤ RightFreyd V := rightFunctor V ⋙ quotient V

instance : (functor V).Additive := by dsimp [functor]; infer_instance

instance : (functor V).Full where
  map_surjective a := by
    obtain ⟨u, rfl⟩ := (quotient V).map_surjective a
    use u.right
    apply congrArg (quotient V).map
    ext
    · exact HasZeroObject.from_zero_ext _ _
    · rfl

instance : (functor V).Faithful where
  map_injective {_ _} _ _ eq := by
    refine eq_of_sub_eq_zero (((quotient_map_eq_iff _ _).mp eq).some.comm.trans ?_)
    convert comp_zero
    · exact HasZeroObject.from_zero_ext _ _
    · rfl

end Functor

section

variable {C : Type*} [Category* C] [Preadditive C] [HasCokernels C] (F : V ⥤ C) [F.Additive]

/-- If `C` is a preadditive category with cokernels, any additive functor `F : V ⥤ C`
extends to a functor `lift F : Arrow V ⥤ C` by sending an arrow `u` of `V` to the cokernel
of `F.map u`. -/
@[simps]
def functorLiftAux :
    Arrow V ⥤ C where
      obj u := cokernel (F.map u.hom)
      map f := cokernel.map _ _ (F.map f.left) (F.map f.right)
        (by rw [← F.map_comp, ← f.w, F.map_comp])

set_option backward.isDefEq.respectTransparency false in
instance : (functorLiftAux F).Additive where
  map_add {_ _} {_ _}:= by
    rw [← cancel_epi (cokernel.π _)]
    simp

lemma functorLiftAux_eq_of_rightHomotopic {u v : Arrow V} (f g : u ⟶ v) (h : rightHomotopic V f g) :
    (functorLiftAux F).map f = (functorLiftAux F).map g := by
  simp only [functorLiftAux_map]
  refine (cancel_epi (cokernel.π (F.map u.hom))).mp ?_
  rw [cokernel.π_desc, sub_eq_iff_eq_add.mp h.some.comm]
  simp

def functorLift : RightFreyd V ⥤ C :=
  Quotient.lift _ (functorLiftAux F) (fun _ _ ↦ functorLiftAux_eq_of_rightHomotopic F)

lemma functorLift_spec : quotient V ⋙ functorLift F = functorLiftAux F :=
  Quotient.lift_spec _ _ _

lemma functorLift_spec_map {u v : Arrow V} (f : u ⟶ v) :
    (functorLift F).map ((quotient V).map f) = (functorLiftAux F).map f := by
  rw [← Functor.comp_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
instance : (functorLift F).Additive where
  map_add {_ _} {f g} := by
    obtain ⟨a, rfl⟩ := (quotient V).map_surjective f
    obtain ⟨b, rfl⟩ := (quotient V).map_surjective g
    rw [← (quotient V).map_add]
    simp only [functorLift_spec_map, (functorLiftAux F).map_add]

variable {F} {F' : V ⥤ C} [F'.Additive]

set_option backward.isDefEq.respectTransparency false in
@[simps!]
def natTransLiftAux (α : F ⟶ F') : functorLiftAux F ⟶ functorLiftAux F' where
  app u := cokernel.map _ _ (α.app u.left) (α.app u.right) (α.naturality u.hom)
  naturality _ _ _ := (cancel_epi (cokernel.π _)).mp (by simp)

@[simps!]
def natTransLift (α : F ⟶ F') : functorLift F ⟶ functorLift F' :=
  Quotient.natTransLift _ (natTransLiftAux α)

variable (F)
lemma natTransLift_id : natTransLift (𝟙 F) = 𝟙 (functorLift F) := by cat_disch

set_option backward.isDefEq.respectTransparency false in
lemma natTransLift_comp {F'' : V ⥤ C} [F''.Additive] (α : F ⟶ F') (β : F' ⟶ F'') :
    natTransLift α ≫ natTransLift β = natTransLift (α ≫ β) := by
  ext
  refine (cancel_epi (cokernel.π _)).mp (by simp)

--lemma functorLiftIso_naturality : Functor.whiskerLeft

variable [HasFiniteProducts V]

instance : HasFiniteProducts (Arrow V) where
  out _ := inferInstance

instance : HasFiniteProducts (RightFreyd V) :=
  have : (quotient V).EssSurj := inferInstance
  (quotient V).hasFiniteProducts_of_additive_of_essSurj

variable [HasZeroObject V]

set_option backward.isDefEq.respectTransparency false in
@[simps!]
def rightFunctorLiftAuxIso : rightFunctor V ⋙ functorLiftAux F ≅ F := by
  refine NatIso.ofComponents (fun X ↦ ?_) (fun u ↦ ?_)
  · have : IsIso (cokernel.π (F.map (((rightFunctor V).obj X).hom))) :=
      coequalizer.π_of_eq (F.map_zero _ _)
    exact (asIso (cokernel.π (F.map (((rightFunctor V).obj X).hom)))).symm
  · simp [rightFunctor]

def functorLiftIso : functor V ⋙ functorLift F ≅ F :=
  Functor.associator _ _ _ ≪≫ (rightFunctor V).isoWhiskerLeft
  (Quotient.lift.isLift (rightHomotopic V) (functorLiftAux F)
  (fun _ _ f g h ↦ functorLiftAux_eq_of_rightHomotopic F f g h)) ≪≫ rightFunctorLiftAuxIso F

omit [HasFiniteProducts V] in
@[simp]
lemma functorLiftIso_inv_app (X : V) :
    (functorLiftIso F).inv.app X = cokernel.π (F.map ((rightFunctor V).obj X).hom) := by
  dsimp [functorLiftIso]
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, assoc, NatTrans.comp_app,
    rightFunctorLiftAuxIso_inv_app, Functor.whiskerLeft_app, Quotient.lift.isLift_inv,
    Functor.associator_inv_app]
  erw [comp_id, comp_id]

variable (V C)

noncomputable def liftAux : (V ⥤+ C) ⥤ (RightFreyd V ⥤ C) where
  obj F :=
    letI := F.2
    functorLift F.1
  map {F G} α :=
    letI := F.2
    letI := G.2
    natTransLift α.hom
  map_comp _ _ := (natTransLift_comp _ _ _).symm

noncomputable def lift : (V ⥤+ C) ⥤ (RightFreyd V ⥤ᵣ C) := by
  refine ObjectProperty.lift _ (liftAux V C) ?_
  intro F
  sorry

end

end RightFreyd

section LeftFunctor

variable [HasZeroObject V]

/-- If `V` has a zero object, the functor from `V` to `Arrow V` that sends an object `X`
to the arrow `X ⟶ 0`. -/
def leftFunctor : V ⥤ Arrow V where
  obj X := Arrow.mk ((isZero_zero V).from_ X)
  map f := Arrow.homMk f 0 (HasZeroObject.to_zero_ext _ _)
  map_id _ := by
    ext
    · rfl
    · exact HasZeroObject.to_zero_ext _ _

instance : (leftFunctor V).Additive where
  map_add {_ _ _ _} := by
    ext
    · rfl
    · exact HasZeroObject.to_zero_ext _ _

end LeftFunctor

/-- If `V` is a preadditive category, then `LeftFreyd V` is the category of arrows in `V`,
with morphisms identified when they are left homotopic. -/
def LeftFreyd :=
  CategoryTheory.Quotient (leftHomotopic V)

instance : Category (LeftFreyd V) :=
  inferInstanceAs <| Category (CategoryTheory.Quotient (leftHomotopic V))

namespace LeftFreyd

instance : Preadditive (CategoryTheory.Quotient (leftHomotopic V)) :=
  Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨LeftHomotopy.add h h'⟩)

instance : Preadditive (LeftFreyd V) :=
  inferInstanceAs <| Preadditive (CategoryTheory.Quotient (leftHomotopic V))

/-- The quotient functor from `Arrow V` to `LeftFreyd V`. -/
def quotient : Arrow V ⥤ LeftFreyd V :=
  CategoryTheory.Quotient.functor _

instance : (quotient V).Full := Quotient.full_functor _

instance : (quotient V).EssSurj := Quotient.essSurj_functor _

instance : (quotient V).Additive where

variable {V}

/-- If two morphisms in `Arrow V` are left homotopic, then they become equal in the left
Freyd category. -/
theorem eq_of_leftHomotopy {u v : Arrow V} (f g : u ⟶ v) (h : LeftHomotopy f g) :
    (quotient V).map f = (quotient V).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/-- If two morphisms of `Arrow V` become equal in the left Freyd category,
then they are rleft homotopic. -/
def homotopyOfEq {u v : Arrow V} (f g : u ⟶ v)
    (w : (quotient V).map f = (quotient V).map g) : LeftHomotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp w).some

variable {u v : Arrow V} (f g : u ⟶ v)

lemma quotient_map_eq_iff :
    (quotient V).map f = (quotient V).map g ↔ Nonempty (LeftHomotopy f g) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_leftHomotopy _ _ h⟩

lemma quotient_map_eq_zero_iff : (quotient V).map f = 0 ↔ Nonempty (LeftHomotopy f 0) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_leftHomotopy _ _ h⟩

/--
If `f` is a morphism of `Arrow V` such that `f.left` is an isomorphism, then the image of `f`
in the right Freyd category is a monomorphism. -/
lemma isMono_of_left_iso [IsIso f.left] : Mono ((quotient V).map f) where
  right_cancellation g₁ g₂ eq := by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    apply eq_of_leftHomotopy
    set h : LeftHomotopy (g₁ ≫ f) (g₂ ≫ f) := homotopyOfEq _ _ eq
    exact ⟨h.hom ≫ inv f.left, by simp [← cancel_mono f.left, dsimp% h.comm]⟩

section Functor

variable (V) [HasZeroObject V]

def functor : V ⥤ LeftFreyd V := leftFunctor V ⋙ quotient V

instance : (functor V).Additive := by dsimp [functor]; infer_instance

instance : (functor V).Full where
  map_surjective a := by
    obtain ⟨u, rfl⟩ := (quotient V).map_surjective a
    use u.left
    apply congrArg (quotient V).map
    ext
    · rfl
    · exact HasZeroObject.to_zero_ext _ _

instance : (functor V).Faithful where
  map_injective {_ _} _ _ eq := by
    refine eq_of_sub_eq_zero (((quotient_map_eq_iff _ _).mp eq).some.comm.trans ?_)
    convert zero_comp
    · exact HasZeroObject.to_zero_ext _ _
    · rfl

end Functor

end LeftFreyd

end CategoryTheory.Preadditive
