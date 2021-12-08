import topology.sheaves.sheaf
import topology.category.Top.opens
import algebra.category.CommRing
import cats

open category_theory Top topological_space opposite

-- class PresheafOfModules1 (X : Top) (𝒪 : presheaf CommRing X) (ℱ : presheaf AddCommGroup X) :=
-- [is_module : Π (U : opens X), module (𝒪.obj (op U)) (ℱ.obj (op U))]
-- (res_compatible : Π (U V : opens X) (h : (op U) ⟶ (op V)) (r : 𝒪.obj (op U)) (a: ℱ.obj (op U)), ℱ.map h (r • a) = 𝒪.map h r • ℱ.map h a)

-- Now I believe this is not the correct definition, because for `h : U ⟶ V`, `ℱ.map h` is only an `AddCommGroup`-map not a `Module`-map


open restriction_of_scalar

/--
This is a presheaf of Modules over ℱ ⋙ BundledModule.forget

If `h : U ⊆ V`, then `ℱ.map h` is a pair `⟨res₁, res₂⟩`, and `res₁` is the restriction map of sheaf of ring while `res₂` is the restriction map of sheaf of module.
-/

class PresheafOfModules2 {X : Top} (ℱ : @presheaf BundledModule BundledModule.is_cat X):=
(res_compatible : Π (U V : opens X) (h : op U ⟶ op V) (r : (ℱ.obj (op U)).R) (m : (ℱ.obj (op U)).M), (ℱ.map h).2 (r • m) = (r • (ℱ.map h).2 m))

open ulift

def int_as_cring : CommRing :=
{ α := ulift ℤ,
  str := { add := λ x y, up (down x + down y),
           add_assoc := sorry,

           zero := up 0,
           add_zero := sorry,
           zero_add := sorry,

           neg := λ r, up (- down r),
           add_left_neg := sorry,

           add_comm := sorry,

           mul := λ x y, up (down x * down y),
           mul_assoc := sorry,
           mul_comm := sorry,

           one := up 1,
           one_mul := sorry,
           mul_one := sorry,

           left_distrib := sorry,
           right_distrib := sorry } }

@[simp] lemma lift_int.add_down (x y : int_as_cring) : (x + y).down = x.down + y.down := rfl
@[simp] lemma lift_int.zero_down : (0 : int_as_cring).down = 0 := rfl

instance test (A : AddCommGroup) : distrib_mul_action (int_as_cring) A :=
{ smul := λ x y, x.1 • y,
  one_smul := λ x, sorry,
  mul_smul := λ x y r, sorry,
  smul_add := sorry,
  smul_zero := sorry }

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

@[reducible] def psh_m {X : Top} (𝒪 : presheaf AddCommGroup X) :
  @presheaf BundledModule BundledModule.is_cat X :=
{ obj := λ U, { R := int_as_cring, M := { carrier := 𝒪.obj U, is_module := is_int_module (𝒪.obj U)} },
  map := λ U V h,
    ⟨𝟙 _, { to_fun := λ m, 𝒪.map h m,
            map_add' := λ x y, by rw add_monoid_hom.map_add,
            map_smul' := λ r m, begin
            dsimp only at *,
            rw [ring_hom.id_apply],
            erw add_monoid_hom.map_zsmul,
            simp only [lift_int.zsmul],
          end }⟩ }


instance {X : Top} (𝒪 : presheaf AddCommGroup X) :
  (PresheafOfModules2 (psh_m 𝒪)) :=
{ res_compatible := λ U V h r m, begin
    dsimp only,
    erw [smul_def', id_apply, add_monoid_hom.map_zsmul, lift_int.zsmul],
  end }

#exit
-- example (X : Top) (𝒪 : presheaf AddCommGroup X) : PresheafOfModules2 X :=
-- { ℱ := { obj := λ U, { R := ℤ,
--                         M := as_int_module (𝒪.obj U) },
--           map := λ U V h,
--             ⟨𝟙 _, { to_fun := λ m, 𝒪.map h m,
--                     map_add' := λ x y, by rw add_monoid_hom.map_add,
--                     map_smul' := λ r m, begin
--                       dsimp only at *,
--                       rw [ring_hom.id_apply],
--                       erw add_monoid_hom.map_zsmul,
--                       erw (lift_int.zsmul _ r (𝒪.map h m)).symm,
--                     end }⟩ },
--   res_compatible := λ U V h r m, begin
--     dsimp only [smul_def', add_monoid_hom.map_zsmul, add_monoid_hom.map_add, ring_hom.id_apply, id_apply] at *,
--     erw [smul_def', id_apply, add_monoid_hom.map_zsmul],
--     refl,
--   end, }

-- example (X : Top) (psofm : PresheafOfModules2 X) : PresheafOfModules1 X :=
-- { 𝒪 := psofm.ℱ ⋙ BundledModule.forget,
--   ℱ :=
--     { obj := λ U, AddCommGroup.of (psofm.ℱ.obj U).M,
--       map := λ U V h, @AddCommGroup.of_hom (AddCommGroup.of (psofm.ℱ.obj U).M) (AddCommGroup.of (psofm.ℱ.obj V).M) _ _
--         { to_fun := (psofm.ℱ.map h).2,
--           map_zero' :=  linear_map.map_zero _,
--           map_add' := λ m m', begin
--             dsimp only [AddCommGroup.coe_of] at m m',
--             rw linear_map.map_add,
--             -- sorry,
--           end, }, },
--   is_module := λ U, begin
--     rw [BundledModule.forget, functor.comp_obj],
--     dsimp [AddCommGroup.coe_of], apply_instance,
--   end,
--   res_compatible := λ U V h r m, begin
--     dsimp only [linear_map.map_zero, functor.comp_obj, AddCommGroup.coe_of, BundledModule.forget] at r m,
--     have := psofm.res_compatible U V h r m,
--     erw [functor.comp_map, this, restriction_as, smul_def'],
--   end}

-- example (X : Top) (psofm : PresheafOfModules1 X) : PresheafOfModules2 X :=
-- { ℱ := { obj := λ U,
--             { R := psofm.𝒪.obj U,
--               M := { carrier := psofm.ℱ.obj U,
--                 is_module := psofm.is_module (unop U) } },
--           map := λ U V h, ⟨psofm.𝒪.map h,
--             { to_fun := λ m, psofm.ℱ.map h m,
--               map_add' := λ m m', begin
--                 dsimp only at *,
--                 simp only [add_monoid_hom.map_add],
--               end,
--               map_smul' := λ r m, begin
--                 dsimp only at *,
--                 rw [ring_hom.id_apply],
--                 have := smul_def' (psofm.𝒪.map h) r { carrier := psofm.ℱ.obj V, is_module := _ } (psofm.ℱ.map h m),
--                 rw [restriction_as, as_restriction] at this, dsimp only at this, rw this,

--                 sorry
--               end}⟩ },
--   res_compatible := sorry }

-- example (X : Top) (ℱ : @presheaf BundledModule BundledModule.is_cat X)
--   (U V : opens X) (h : op U ⟶ op V) (r : (ℱ.obj (op U)).R) (m : (ℱ.obj (op U)).M) : true :=
-- begin
--   -- type_check r, -- 𝒪(U)
--   -- type_check resRing r, -- 𝒪(V)
--   -- type_check resMod m, -- resRing* ℱ(V) is a 𝒪(U) module
--   -- type_check (r • resMod m), --resRing* ℱ(V) is a 𝒪(U) module
--   have : (ℱ.map h).2 (r • m) = restriction_as (r • (ℱ.map h).2 m),
--   { rw [restriction_of_scalar.smul_def' (ℱ.map h).1, restriction_as, as_restriction, restriction_as],
--     dsimp only,
--     -- squeeze_simp,
--      },

--   trivial,
-- end

-- def ex1 (X : Top) (𝒪 : presheaf CommRing X) :
--   @presheaf BundledModule BundledModule.is_cat X :=
-- { obj := λ U, { R := 𝒪.obj U, M := { carrier := 𝒪.obj U } },
--   map := λ U V f, ⟨𝒪.map f,
--     { to_fun := 𝒪.map f,
--       map_add' := ring_hom.map_add _,
--       map_smul' := λ r m, begin
--         rw [ring_hom.id_apply, smul_def' (𝒪.map f) r (Module.mk (𝒪.obj V)) (𝒪.map f m), as_restriction, restriction_as,
--           algebra.id.smul_eq_mul, algebra.id.smul_eq_mul],
--         dsimp only,
--         rw ring_hom.map_mul (𝒪.map f) r m,
--         sorry
--       end, }⟩ }
