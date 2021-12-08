import algebra.category.CommRing
import algebra.category.Module.basic

open category_theory

instance restriction_of_scalar.has_scalar {R S : CommRing} (f : R ⟶ S) (N : Module S) :
   has_scalar R N :=
{ smul := λ r m, f r • m }

@[reducible] def restriction_of_scalar.restrict {R S : CommRing} (f : R ⟶ S) (N : Module S) : 
  Module R :=
{ carrier := N,
  is_module :=
  { one_smul := λ b, begin
      unfold has_scalar.smul,
      rw [ring_hom.map_one, one_smul],
    end,
    mul_smul := λ _ _ _, begin
      unfold has_scalar.smul,
      rw [ring_hom.map_mul, mul_smul],
    end,
    smul_add := λ _ _ _,by { unfold has_scalar.smul, rw [smul_add] },
    smul_zero := λ _, by { unfold has_scalar.smul, rw [smul_zero] },
    add_smul := λ _ _ _, begin
      unfold has_scalar.smul,
      rw [ring_hom.map_add, add_smul],
    end,
    zero_smul := λ _, begin
      unfold has_scalar.smul,
      rw [ring_hom.map_zero, zero_smul],
    end,
    ..(restriction_of_scalar.has_scalar f N) } }

instance restriction_of_scalar.has_scalar' {R S : CommRing} (f : R ⟶ S) (N : Module S) :
  has_scalar S (restriction_of_scalar.restrict f N) :=
{ smul := λ r n, r • n }

open restriction_of_scalar

@[simp] lemma restriction_of_scalar.smul_def' {R S : CommRing} (f : R ⟶ S)
  (r : R) (N : Module S)
  (n : restriction_of_scalar.restrict f N) :
  (r • n) = (f r • n) := rfl

def restriction_of_scalar.functor
  {R S : CommRing} (f : R ⟶ S) : Module S ⥤ Module R :=
{ obj := λ m, restriction_of_scalar.restrict f m,
  map := λ m1 m2 l,
    { to_fun := l,
      map_add' := λ x y, by rw [linear_map.map_add],
      map_smul' := λ r y, begin
        simp only [restriction_of_scalar.smul_def', ring_hom.id_apply],
        convert linear_map.map_smul l (f r) y,
      end } }

structure BundledModule :=
(R : CommRing)
(M : Module R.α)

def restriction_of_scalar {M1 M2 : BundledModule} (f : M1.R ⟶ M2.R) : BundledModule :=
{ R := M1.R,
  M := restriction_of_scalar.restrict f M2.M }

@[simp] lemma restriction_of_scalar.R {M1 M2 : BundledModule} (f : M1.R ⟶ M2.R) :
  (restriction_of_scalar f).R = M1.R := rfl
@[simp] lemma restriction_of_scalar.M {M1 M2 : BundledModule} (f : M1.R ⟶ M2.R) :
  (restriction_of_scalar f).M = restriction_of_scalar.restrict f M2.M := rfl

def bundledMap (M1 M2 : BundledModule) : Type* :=
Σ (f : M1.R ⟶ M2.R), M1.M ⟶ (restriction_of_scalar f).M

instance BundledModule.is_cat : large_category BundledModule :=
{ hom := λ M1 M2, bundledMap M1 M2,
  id := λ M, ⟨𝟙 M.R, { to_fun := λ m, m,
                       map_add' := λ _ _, rfl,
                       map_smul' := λ _ _, rfl }⟩,
  comp := λ M1 M2 M3 f g, 
    ⟨f.1 ≫ g.1, 
     { to_fun := λ m, g.2 (f.2 m),
       map_add' := λ m1 m2, by simp only [linear_map.map_add],
       map_smul' := λ r m, begin
        rcases f with ⟨f, f'⟩,
        rcases g with ⟨g, g'⟩,
        dsimp only,
        rw [ring_hom.id_apply, linear_map.map_smulₛₗ, ring_hom.id_apply, 
          restriction_of_scalar.smul_def', restriction_of_scalar.smul_def', comp_apply],
        convert linear_map.map_smul g' (f r) (f' m),
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
