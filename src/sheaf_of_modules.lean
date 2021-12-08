import topology.sheaves.sheaf
import topology.category.Top.opens
import algebra.category.CommRing
import cats

open category_theory Top topological_space opposite

section attempt1

class PreSheafOfModules.core (X : Top) :=
(𝒪 : sheaf CommRing X)
(ℱ : presheaf Ab X)

class PreSheafOfModules (X : Top) extends PreSheafOfModules.core X :=
[is_module : Π (U : opens X), module (𝒪.1.obj (op U)) (ℱ.obj (op U))]
[res_scalar : Π (U V : opens X) (h : (op U) ⟶ (op V)) (r : 𝒪.1.obj (op U)) (a: ℱ.obj (op U)), ℱ.map h (r • a) = 𝒪.1.map h r • ℱ.map h a]


class SheafOfModules (X : Top) extends PreSheafOfModules X :=
(is_sheaf : presheaf.is_sheaf ℱ)

end attempt1

section attempt2

open restriction_of_scalar

/--
This is a presheaf of Modules over ℱ ⋙ BundledModule.forget

If `h : U ⊆ V`, then `ℱ.map h` is a pair `⟨res₁, res₂⟩`, and `res₁` is the restriction map of sheaf of ring while `res₂` is the restriction map of sheaf of module.
-/
def PresheafOfModules' (X : Top) := @presheaf BundledModule BundledModule.is_cat X

example (X : Top) (ℱ : @presheaf BundledModule BundledModule.is_cat X) 
  (U V : opens X) (h : op U ⟶ op V) (r : (ℱ.obj (op U)).R) (m : (ℱ.obj (op U)).M) : true :=
begin
  rcases ℱ.map h with ⟨resRing, resMod⟩,
  type_check resRing r, -- 𝒪(V)
  type_check resMod m, -- resRing* ℱ(V) is a 𝒪(U) module
  type_check r • m, -- ℱ(V)
  type_check resMod (r • m), --resRing* ℱ(V) is a 𝒪(U) module
  -- type_check resRing r • resMod m,
  -- haveI : has_scalar (ℱ.obj (op V)).R (restriction_of_scalar.module resRing (ℱ.obj (op V)).M) :=
  -- { smul := begin intros r' m', sorry end },

  -- type_check @restriction_of_scalar.has_scalar (ℱ.obj (op V)).R,
  sorry,
end

def ex1 (X : Top) (𝒪 : presheaf CommRing X) : 
  @presheaf BundledModule BundledModule.is_cat X :=
{ obj := λ U, { R := 𝒪.obj U, M := { carrier := 𝒪.obj U } },
  map := λ U V f, ⟨𝒪.map f, 
    { to_fun := 𝒪.map f,
      map_add' := ring_hom.map_add _,
      map_smul' := λ r m, begin
        rw [ring_hom.id_apply, smul_def' (𝒪.map f) r (Module.mk (𝒪.obj V)) (𝒪.map f m), as_restriction, restriction_as, 
          algebra.id.smul_eq_mul, algebra.id.smul_eq_mul],
        dsimp only,
        rw ring_hom.map_mul (𝒪.map f) r m,
        sorry
      end, }⟩ }

end attempt2