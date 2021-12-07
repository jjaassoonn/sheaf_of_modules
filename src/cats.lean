import topology.sheaves.sheaf
import topology.category.Top.opens
import algebra.category.CommRing
import algebra.category.Group
import algebra.category.Module.basic

open category_theory Top topological_space opposite


-- class PreSheafOfModules.core (X : Top) :=
-- (𝒪 : sheaf CommRing X)
-- (ℱ : presheaf Ab X)

-- class PreSheafOfModules (X : Top) extends PreSheafOfModules.core X :=
-- [is_module : Π (U : opens X), module (𝒪.1.obj (op U)) (ℱ.obj (op U))]
-- [res_add : Π (U V : opens X) (h : (op U) ⟶ (op V)) (a b : ℱ.obj (op U)), ℱ.map h (a + b) = ℱ.map h a + ℱ.map h b]
-- [res_scalar : Π (U V : opens X) (h : (op U) ⟶ (op V)) (r : 𝒪.1.obj (op U)) (a: ℱ.obj (op U)), ℱ.map h (r • a) = 𝒪.1.map h r • ℱ.map h a]


-- class SheafOfModules (X : Top) extends PreSheafOfModules X :=
-- (is_sheaf : presheaf.is_sheaf ℱ)


structure BundledModule :=
(R : CommRing)
(M : Module R.α)

@[reducible] instance restriction_of_scalar.bu
{M1 M2 : BundledModule} (f : M1.R ⟶ M2.R) : has_scalar M1.R M2.M :=
{ smul := λ r m, f r • m }

instance restriction_of_scalar.mul_action
{M1 M2 : BundledModule} (f : M1.R ⟶ M2.R) : mul_action M1.R M2.M :=
{ one_smul := λ m, begin
    unfold has_scalar.smul,
    rw [ring_hom.map_one, one_smul],
  end,
  mul_smul := λ r r' m, begin
    unfold has_scalar.smul,
    rw [ring_hom.map_mul, mul_smul],
  end,
  ..(restriction_of_scalar.bu f) }

instance restriction_of_scalar.distrib_mul_action
{M1 M2 : BundledModule} (f : M1.R ⟶ M2.R) : distrib_mul_action M1.R M2.M :=
{ smul_add := λ r2 r1 m, begin
    unfold has_scalar.smul,
    rw [smul_add],
  end,
  smul_zero := λ m, begin
    unfold has_scalar.smul,
    rw [smul_zero],
  end,
  ..(restriction_of_scalar.mul_action f)}

def restriction_of_scalar.M {M1 M2 : BundledModule} (f : M1.R ⟶ M2.R) : Module M1.R :=
{ carrier := M2.M,
  is_module :=
    { add_smul := λ r r' m, begin
        unfold has_scalar.smul,
        rw [ring_hom.map_add, add_smul],
      end,
      smul_zero := λ m, begin
        unfold has_scalar.smul,
        rw [smul_zero],
      end,
      zero_smul := λ m, begin
        unfold has_scalar.smul,
        rw [ring_hom.map_zero, zero_smul],
      end,
      ..(restriction_of_scalar.distrib_mul_action f) } }

def restriction_of_scalar.M_as {M1 M2 : BundledModule} {f : M1.R ⟶ M2.R} :
  restriction_of_scalar.M f → M2.M := λ m, m

def restriction_of_scalar.as_restriction  {M1 M2 : BundledModule} {f : M1.R ⟶ M2.R} :
  M2.M → restriction_of_scalar.M f := λ m, m

open restriction_of_scalar

@[simp] lemma restriction_of_scalar.smul_def {M1 M2 : BundledModule} (f : M1.R ⟶ M2.R)
  (r : M1.R) (m : restriction_of_scalar.M f) :
  (r • m) = as_restriction (f r • M_as m) := rfl

def restriction_of_scalar {M1 M2 : BundledModule} (f : M1.R ⟶ M2.R) : BundledModule :=
{ R := M1.R,
  M := restriction_of_scalar.M f, }

def bundledMap (M1 M2 : BundledModule) : Type* :=
Σ (f : M1.R ⟶ M2.R), M1.M ⟶ restriction_of_scalar.M f

instance BundledModule.is_cat : category BundledModule :=
{ hom := λ M1 M2, bundledMap M1 M2,
  id := λ M, ⟨𝟙 M.R, { to_fun := λ m, m,
                       map_add' := λ _ _, rfl,
                       map_smul' := λ _ _, rfl }⟩,
  comp := λ M1 M2 M3 f g, ⟨f.1 ≫ g.1, { to_fun := λ m, g.2 (f.2 m),
                                         map_add' := λ m1 m2, by simp only [linear_map.map_add],
                                         map_smul' := λ r m, begin
                                           rcases f with ⟨f, f'⟩,
                                           rcases g with ⟨g, g'⟩,
                                           rw [ring_hom.id_apply, linear_map.map_smulₛₗ, ring_hom.id_apply, restriction_of_scalar.smul_def,
                                            restriction_of_scalar.smul_def, comp_apply, as_restriction, as_restriction, M_as, M_as,
                                            linear_map.map_smul, restriction_of_scalar.smul_def, as_restriction, M_as],
                                         end }⟩,
  comp_id' := λ M1 M2 f, begin
    ext, refl, rw heq_iff_eq, ext, refl,
  end,
  id_comp' := λ M1 M2 f, begin
    ext, refl, rw heq_iff_eq, ext, refl,
  end }

def BundledModule.forget : @category_theory.functor BundledModule BundledModule.is_cat CommRing _ :=
{ obj := λ M, M.R,
  map := λ M1 M2 f, f.1 }
