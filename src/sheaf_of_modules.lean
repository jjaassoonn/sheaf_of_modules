import topology.sheaves.sheaf
import topology.category.Top.opens
import algebra.category.CommRing
import cats

open category_theory Top topological_space opposite

structure PresheafOfModules1 (X : Top) :=
(𝒪 : presheaf CommRing X) 
(ℱ : presheaf AddCommGroup X)
[is_module : Π (U : (opens X)ᵒᵖ), module (𝒪.obj U) (ℱ.obj U)]
(res_compatible : Π (U V : (opens X)ᵒᵖ) (h : U ⟶ V) (r : 𝒪.obj U) (a: ℱ.obj U),
  ℱ.map h (r • a) = 𝒪.map h r • ℱ.map h a)

-- Now I believe this is not the correct definition, because for `h : U ⟶ V`, `ℱ.map h` is only an `AddCommGroup`-map not a `Module`-map


open restriction_of_scalar

/--
This is a presheaf of Modules over ℱ ⋙ BundledModule.forget

If `h : U ⊆ V`, then `ℱ.map h` is a pair `⟨res₁, res₂⟩`, and `res₁` is the restriction map of sheaf of ring while `res₂` is the restriction map of sheaf of module.
-/

class PresheafOfModules2 {X : Top} (ℱ : @presheaf BundledModule BundledModule.is_cat X):=
(res_compatible : Π (U V : (opens X)ᵒᵖ) (h : U ⟶ V) (r : (ℱ.obj U).R) (m : (ℱ.obj U).M), (ℱ.map h).2 (r • m) = (r • (ℱ.map h).2 m))

open ulift

@[reducible] instance int_as_cring.has_add : has_add (ulift ℤ) :=
⟨λ x y, up (down x + down y)⟩

@[simp] lemma int_as_cring.add_def (x y : ℤ) : (up x) + (up y) = up (x + y) := rfl

@[reducible] instance int_as_cring.has_neg : has_neg (ulift ℤ) :=
⟨λ x, up (- down x)⟩

@[simp] lemma int_as_cring.neg_def (z : ℤ) : -(up z) = up (- z) := rfl

@[reducible] instance int_as_cring.has_mul : has_mul (ulift ℤ) :=
⟨λ x y, up (down x * down y)⟩

@[simp] lemma int_as_cring.mul_def (x y : ℤ) : up x * up y = up (x * y) := rfl

def int_as_cring : CommRing :=
{ α := ulift ℤ,
  str := { add_assoc := λ a b c, begin
             cases a, cases b, cases c,
             dsimp only, rw add_assoc,
           end,

           zero := up 0,
           add_zero := λ a, begin
             cases a,
             dsimp only, rw add_zero,
           end,
           zero_add := λ a, begin
             cases a, dsimp only, rw zero_add,
           end,

           neg := λ r, up (- down r),
           add_left_neg := λ a, 
           begin
             cases a, rw [int_as_cring.neg_def, int_as_cring.add_def, int.add_left_neg], 
             refl,
           end,

           add_comm := λ x y, begin
             cases x, cases y,
             rw [int_as_cring.add_def, add_comm, int_as_cring.add_def],
           end,

           mul_assoc := λ x y z, begin 
             cases x, cases y, cases z,
             rw [int_as_cring.mul_def, int_as_cring.mul_def, mul_assoc],
           end,
           mul_comm := λ x y, begin
             cases x, cases y,
             rw [int_as_cring.mul_def, mul_comm, int_as_cring.mul_def],
           end,

           one := up 1,
           one_mul := λ a, begin
             cases a, rw [int_as_cring.mul_def, one_mul],
           end,
           mul_one := λ a, begin
             cases a, rw [int_as_cring.mul_def, mul_one],
           end,

           left_distrib := λ a b c, begin
             cases a, cases b, cases c,
             rw [int_as_cring.add_def, int_as_cring.mul_def, mul_add],
           end,
           right_distrib := λ a b c, begin
             cases a, cases b, cases c,
             rw [int_as_cring.add_def, int_as_cring.mul_def, add_mul],
           end,
           ..(int_as_cring.has_add),
           ..(int_as_cring.has_neg),
           ..(int_as_cring.has_mul) } }

@[simp] lemma lift_int.add_down (x y : int_as_cring) : (x + y).down = x.down + y.down := rfl
@[simp] lemma lift_int.zero_down : (0 : int_as_cring).down = 0 := rfl

instance int_as_cring.distrib_mul_action (A : AddCommGroup) : distrib_mul_action (int_as_cring) A :=
{ smul := λ x y, x.1 • y,
  one_smul := λ x, by erw one_zsmul,
  mul_smul := λ x y r, begin 
    cases x, cases y,
    rw [int_as_cring.mul_def, mul_zsmul],
  end,
  smul_add := λ r x y, by rw zsmul_add,
  smul_zero := λ r, by rw zsmul_zero }

@[simp] lemma lift_int.zsmul (A : AddCommGroup) (r : int_as_cring) (a : A) : r • a = r.1 • a := rfl

instance is_int_module (A : AddCommGroup) : module int_as_cring A :=
{ add_smul := λ x y r, begin
    cases x, cases y,
    unfold has_scalar.smul,
    simp only [zsmul_eq_smul],
    rw [lift_int.add_down], dsimp only, rw add_smul,
  end,
  zero_smul := λ x, begin
    unfold has_scalar.smul,
    simp only [zsmul_eq_smul],
    rw [lift_int.zero_down, zero_smul],
  end}

def as_int_module (A : AddCommGroup) : module ℤ A := by apply_instance

-- @[reducible] def psh_m {X : Top} (𝒪 : presheaf AddCommGroup X) :
--   @presheaf BundledModule BundledModule.is_cat X :=
-- { obj := λ U, { R := int_as_cring, M := { carrier := 𝒪.obj U, is_module := is_int_module (𝒪.obj U)} },
--   map := λ U V h,
--     ⟨𝟙 _, { to_fun := λ m, 𝒪.map h m,
--             map_add' := λ x y, by rw add_monoid_hom.map_add,
--             map_smul' := λ r m, begin
--             dsimp only at *,
--             rw [ring_hom.id_apply],
--             erw add_monoid_hom.map_zsmul,
--             erw [lift_int.zsmul],
--           end }⟩ }


-- instance {X : Top} (𝒪 : presheaf AddCommGroup X) :
--   (PresheafOfModules2 (psh_m 𝒪)) :=
-- { res_compatible := λ U V h r m, begin
--     dsimp only,
--     erw [smul_def', id_apply, add_monoid_hom.map_zsmul, lift_int.zsmul],
--   end }

example (X : Top) (ℱ : @presheaf BundledModule BundledModule.is_cat X) [PresheafOfModules2 ℱ]: PresheafOfModules1 X :=
{ 𝒪 := { obj := λ U, (ℱ.obj U).R,
         map := λ _ _ h, (ℱ.map h).1 },
  ℱ :=
    { obj := λ U, AddCommGroup.of (ℱ.obj U).M,
      map := λ U V h, @AddCommGroup.of_hom (AddCommGroup.of (ℱ.obj U).M) (AddCommGroup.of (ℱ.obj V).M) _ _
        { to_fun := (ℱ.map h).2,
          map_zero' :=  linear_map.map_zero _,
          map_add' := λ m m', begin
            -- rw linear_map.map_add,
            sorry,
          end, }, },
  is_module := λ U, begin
    dsimp only [AddCommGroup.coe_of], apply_instance,
  end,
  res_compatible := λ U V h r m, begin
    dsimp only [AddCommGroup.coe_of, linear_map.map_zero, functor.map_comp, functor.map_id] at *,
    erw PresheafOfModules2.res_compatible U V h r m,
    erw [smul_def'],
  end}

@[reducible] def convert_to2 (X : Top) (psofm : PresheafOfModules1 X) : @presheaf BundledModule BundledModule.is_cat X :=
{ obj := λ U,{ R := psofm.𝒪.obj U,
               M := { carrier := psofm.ℱ.obj U,
               is_module := psofm.is_module U } },
  map := λ U V h, ⟨psofm.𝒪.map h,
        { to_fun := λ m, psofm.ℱ.map h m,
          map_add' := λ m m', begin
            dsimp only at *,
            simp only [add_monoid_hom.map_add],
          end,
          map_smul' := λ r m, begin
            dsimp only at *,
            rw [ring_hom.id_apply, psofm.res_compatible _ _ h],
            -- erw (smul_def' (psofm.𝒪.map h) r { carrier := psofm.ℱ.obj V,
            --    is_module := psofm.is_module V } (psofm.ℱ.map h m)).symm,

            sorry,
          end}⟩ }

instance (X : Top) (psofm : PresheafOfModules1 X) : PresheafOfModules2 (convert_to2 X psofm) :=
{ res_compatible := λ U V h r m, begin
  dsimp only [convert_to2] at *,
  rw smul_def',
  erw psofm.res_compatible, refl,
end }