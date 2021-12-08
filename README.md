# [The Category of `Mod`](https://ncatlab.org/nlab/show/Mod)

I defined the category of modules at [here](src/cats.lean#L66) following the link above.
This may or may not be useful to define sheaf of modules.

# Sheaf of Modules

There is also a formalisation of sheaf of modules at [here](src/sheaf_of_modules.lean#L25).

I tried to define sheaf of module as
```lean
class PresheafOfModules1 (X : Top) (𝒪 : presheaf CommRing X) (ℱ : presheaf AddCommGroup X) :=
[is_module : Π (U : opens X), module (𝒪.obj (op U)) (ℱ.obj (op U))]
(res_compatible : 
  Π (U V : opens X) (h : (op U) ⟶ (op V)) (r : 𝒪.obj (op U)) (a: ℱ.obj (op U)), 
    ℱ.map h (r • a) = 𝒪.map h r • ℱ.map h a)
```

But now I believe that this definition is not actually correct, the reason is that
`ℱ.map h` for `h : U ⟶ V` is only a map in `AddCommGroup`, but we want something stronger.

So I believe the better definition is:
```lean
class PresheafOfModules2 {X : Top} (ℱ : @presheaf BundledModule BundledModule.is_cat X):=
(res_compatible : 
  Π (U V : opens X) (h : op U ⟶ op V) (r : (ℱ.obj (op U)).R) (m : (ℱ.obj (op U)).M), 
  (ℱ.map h).2 (r • m) = (r • (ℱ.map h).2 m))
```

So `ℱ` is a functor `(opens X)ᵒᵖ ⥤ BundledModule`. 
We can interpret `ℱ ⋙ BundledModule.forget : (opens X)ᵒᵖ ⥤ CommRing` as the presheaf of rings.

So if `U : (opens X)ᵒᵖ`, then `ℱ.obj U` is of the form `(R, M)` where `R : CommRing` and `M : Module R`; Similarly `ℱ.obj V` is `(S, N)` where `S : CommRing` and `N : Module N`. 
And if `h : U ⟶ V`, then `(ℱ.map h).1` can be seen as the restriction map of the presheaf of rings so call it `res_ring` and `(ℱ.map h).2` can be seen as the restriction map of the "presheaf of modules" in the usual sense so call it `res_module`. `res_compatible` is saying:

For `r : R` and `m : M`, `res_module (r • m) = r • res_module m`.
Note that the `smul` on the right hand side is restriction of scalar.
So `r • res_module m` is secretly `res_ring r • res_module m`.