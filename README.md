# [The Category of `Mod`](https://ncatlab.org/nlab/show/Mod)

I defined the category of modules at [here](src/cats.lean#L72) following the link above.
This may or may not be useful to define sheaf of modules.

# Sheaf of Modules

There is also a formalisation of sheaf of modules at [here](src/sheaf_of_modules.lean#L25).

I defined sheaf of module as
```lean
structure PresheafOfModules1 (X : Top) :=
(𝒪 : presheaf CommRing X) 
(ℱ : presheaf AddCommGroup X)
[is_module : Π (U : (opens X)ᵒᵖ), module (𝒪.obj U) (ℱ.obj U)]
(res_compatible : Π (U V : (opens X)ᵒᵖ) (h : U ⟶ V) (r : 𝒪.obj U) (a: ℱ.obj U),
  ℱ.map h (r • a) = 𝒪.map h r • ℱ.map h a)
```

And also as

```lean
class PresheafOfModules2 {X : Top} (ℱ : @presheaf BundledModule BundledModule.is_cat X):=
(res_compatible : 
  Π (U V : (opens X)ᵒᵖ) (h : U ⟶ V) (r : (ℱ.obj U).R) (m : (ℱ.obj U).M), 
    (ℱ.map h).2 (r • m) = (r • (ℱ.map h).2 m))
```

So `ℱ` is a functor `(opens X)ᵒᵖ ⥤ BundledModule`. 
We can interpret `ℱ ⋙ BundledModule.forget : (opens X)ᵒᵖ ⥤ CommRing` as the presheaf of rings.

So if `U : (opens X)ᵒᵖ`, then `ℱ.obj U` is of the form `(R, M)` where `R : CommRing` and `M : Module R`; Similarly `ℱ.obj V` is `(S, N)` where `S : CommRing` and `N : Module N`. 
And if `h : U ⟶ V`, then `(ℱ.map h).1` can be seen as the restriction map of the presheaf of rings so call it `res_ring` and `(ℱ.map h).2` can be seen as the restriction map of the "presheaf of modules" in the usual sense so call it `res_module`. `res_compatible` is saying:

For `r : R` and `m : M`, `res_module (r • m) = r • res_module m`.
Note that the `smul` on the right hand side is restriction of scalar.
So `r • res_module m` is secretly `res_ring r • res_module m`.


I wrote two functions to convert back and forth from `PresheafOfModules1` and `PresheafOfModules2`.

## Example

Here is a trivial example on how to actually use this definition.

So `𝒪` is a presheaf of `AddCommGroup`. We can define turn it into a
presheaf of modules over constant sheaf of `ℤ`.

```lean
@[reducible] def psh_m {X : Top} (𝒪 : presheaf AddCommGroup X) :
  @presheaf BundledModule BundledModule.is_cat X :=
{ obj := λ U, { R := int_as_cring, 
                M := { carrier := 𝒪.obj U, 
                       is_module := is_int_module (𝒪.obj U)} },
  map := λ U V h,
    ⟨𝟙 _, { to_fun := λ m, 𝒪.map h m,
            map_add' := λ x y, by rw add_monoid_hom.map_add,
            map_smul' := λ r m, begin
            dsimp only at *,
            rw [ring_hom.id_apply],
            erw add_monoid_hom.map_zsmul,
            erw [lift_int.zsmul],
          end }⟩ }


instance {X : Top} (𝒪 : presheaf AddCommGroup X) :
  (PresheafOfModules2 (psh_m 𝒪)) :=
{ res_compatible := λ U V h r m, begin
    dsimp only,
    erw [smul_def', id_apply, add_monoid_hom.map_zsmul, lift_int.zsmul],
  end }
```
