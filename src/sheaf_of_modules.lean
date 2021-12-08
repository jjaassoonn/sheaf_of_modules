import topology.sheaves.sheaf
import topology.category.Top.opens
import algebra.category.CommRing
import cats

open category_theory Top topological_space opposite

structure PreSheafOfModules1 (X : Top) :=
(𝒪 : presheaf CommRing X)
(ℱ : presheaf AddCommGroup X)
[is_module : Π (U : opens X), module (𝒪.obj (op U)) (ℱ.obj (op U))]
(res_compatible : Π (U V : opens X) (h : (op U) ⟶ (op V)) (r : 𝒪.obj (op U)) (a: ℱ.obj (op U)), ℱ.map h (r • a) = 𝒪.map h r • ℱ.map h a)

-- structure SheafOfModules (X : Top) extends PreSheafOfModules X :=
-- (is_sheaf : presheaf.is_sheaf ℱ)

open restriction_of_scalar

/--
This is a presheaf of Modules over ℱ ⋙ BundledModule.forget

If `h : U ⊆ V`, then `ℱ.map h` is a pair `⟨res₁, res₂⟩`, and `res₁` is the restriction map of sheaf of ring while `res₂` is the restriction map of sheaf of module.
-/
structure PresheafOfModules2 (X : Top) := 
(ℱ : @presheaf BundledModule BundledModule.is_cat X)
(res_compatible : Π (U V : opens X) (h : op U ⟶ op V) (r : (ℱ.obj (op U)).R) (m : (ℱ.obj (op U)).M), (ℱ.map h).2 (r • m) = @restriction_as _ _ (ℱ.map h).1 _ (r • (ℱ.map h).2 m))

example (X : Top) (psofm : PresheafOfModules2 X) : PreSheafOfModules1 X :=
{ 𝒪 := psofm.ℱ ⋙ BundledModule.forget,
  ℱ := 
    { obj := λ U, AddCommGroup.of (psofm.ℱ.obj U).M, 
      map := λ U V h, @AddCommGroup.of_hom (AddCommGroup.of (psofm.ℱ.obj U).M) (AddCommGroup.of (psofm.ℱ.obj V).M) _ _
        { to_fun := (psofm.ℱ.map h).2,
          map_zero' :=  linear_map.map_zero _,
          map_add' := λ m m', begin 
            dsimp only [AddCommGroup.coe_of] at m m',
            -- rw linear_map.map_add,
            sorry,
          end, }, },
  is_module := λ U, begin
    rw [BundledModule.forget, functor.comp_obj],
    dsimp [AddCommGroup.coe_of], apply_instance,
  end,
  res_compatible := λ U V h r m, begin
    dsimp only [linear_map.map_zero, functor.comp_obj, AddCommGroup.coe_of, BundledModule.forget] at r m,
    have := psofm.res_compatible U V h r m,
    erw [functor.comp_map, this, restriction_as, smul_def'],
  end}

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
