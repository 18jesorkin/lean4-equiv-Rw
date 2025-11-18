import Tactic.translate

-- From: https://cs.ioc.ee/ewscs/2009/dybjer/mainPalmse-revised.pdf

inductive Exp (α : Type)
| app : Exp α → Exp α → Exp α
| id  : Exp α
| elem : α → Exp α


inductive R : (Exp α) → (Exp α) → Prop
| assoc {e e' e'' : Exp α} : R ((e.app e').app e'') (e.app (e'.app e''))
| id_left {e  : Exp α}     : R ((Exp.id).app e) (e)
| id_right {e : Exp α}     : R (e.app Exp.id) (e)
| refl     {e : Exp α}     : R (e) (e)
| symm      {e e' : Exp α}  : R (e) (e') → R (e') (e)
| trans {e e' e'' : Exp α} : R (e) (e') → R (e') (e'') → R (e) (e'')
| app {a b c d : Exp α}    : R (a) (b) → R (c) (d) → R (a.app c) (b.app d)


-- Setoid instance here:
instance R_Setoid : Setoid (Exp α) :=
  { r := R
    iseqv :=
      { refl := λ _ => R.refl
        symm := R.symm
        trans := R.trans
      }
  }

--User-given:
-- @[map₂]
def app_resp {α} : ∀ ⦃a₁ a₂ : Exp α⦄, R a₁ a₂ → ∀ ⦃b₁ b₂ : Exp α⦄, R b₁ b₂ → R (a₁.app b₁) (a₂.app b₂)
  := fun ⦃a₁ a₂⦄ a ⦃b₁ b₂⦄ a_1 => R.app a a_1


-- May create new version of tactic that expects input to be of the form:
  -- R     : (p₁ : P₁) → ⋯ → (pₙ : Pₙ)  → Rel  (X)
  -- lift  : (p₁ : P₁) → ⋯ → (pₘ : Pₘ) → Lift (X) (Y)
  -- lift₂ : (p₁ : P₁) → ⋯ → (pₘ : Pₘ) → Lift₂(X) (Y) (Z)
  -- map   : (p₁ : P₁) → ⋯ → (pₘ : Pₘ) → Map  (X) (Y)
  -- map₂  : (p₁ : P₁) → ⋯ → (pₘ : Pₘ) → Map₂ (X) (Y) (Z)
-- where:
  -- Rel (X)               := X → X → Prop
  -- Lift (X) (Y)          := X → Y
  -- Lift₂ (X) (Y) (Z)     := X → Y → Z
  -- Map (X) (Y)           := X → Y
  -- Map₂ (X) (Y) (Z)      := X → Y → Z
-- This change would make scanning for the number of parameters (i.e. calculating "n" and "m") easier
-- while getting rid of the "map₁", "map₂", "lift₁", "lift₂" tags.

-- Problem with "Quotient.lift" here:
-- Without "Lift_End", will incorrectly calculate "m = 2"
-- instead of "m = 1".
def Lift_End.{u} := fun τ : Sort u => τ
def eval : (Exp α) → Lift_End (Exp α → Exp α)
  | Exp.app a b => (λ e => eval a (eval b e))
  | Exp.id      => id
  | Exp.elem x  => (λ e => (Exp.elem x).app e)

#check Quotient.map₂_mk
#check Quotient.lift₂_mk
-- ∀ b, a.app b ~ [[a]]b
lemma eval_lemma1 (a : Exp α) : ∀ b, R (a.app b) ((eval a) b) :=
by
  induction a

  case app c d c_ih d_ih =>
    unfold eval
    intro b
    specialize d_ih b
    specialize c_ih (eval d b)

    have R.assoc := @R.assoc
    translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩]
    -- (c ⬝ d) ⬝ b ~ c ⬝ (d ⬝ b) ~ c ⬝ (eval d b) ~ eval c (eval d b)
    rw [R.assoc, d_ih, c_ih]

  case id =>
    intro b
    exact R.id_left

  case elem =>
    intro b
    exact R.refl

--User-given:
-- @[lift]
lemma eval_resp (a b : Exp α) (h : R a b) : (eval a) = (eval b) :=
by
  apply funext
  induction h

  any_goals
    intros; aesop

  case app a b c d _ _ ab_ih cd_ih =>
    clear * - ab_ih cd_ih
    intro e
    specialize cd_ih e
    specialize ab_ih ((eval d) e)
    simp only [eval]
    rw [cd_ih, ab_ih]

def reify (f : Exp α → Exp α) : (Exp α) := f Exp.id

def nbe (e : Exp α) : Exp α := reify (eval e)

-- Shows decidability of e ~ e'
theorem correctness (e e' : Exp α) : (R (e) (e')) ↔ (nbe e = nbe e') :=
by
  apply Iff.intro
  · intro h
    induction h
    any_goals
      aesop
    case mp.app a b c d a_r_b c_r_d _ _ =>
      clear * - a_r_b c_r_d
      unfold nbe reify
      translateF R R_Setoid
                [⟨map₂, Exp.app, app_resp⟩,
                 ⟨lift, eval, eval_resp⟩]
      grind

  · unfold nbe reify
    intro h0
    -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
    have R.id_right := @R.id_right
    have eval_lemma1:= @eval_lemma1
    translateF R R_Setoid []
    -- e ~ e ⬝ id ~ nbe e = nbe e' ~ e' ⬝ id ~ e'
    rw [← R.id_right, eval_lemma1 e Exp.id, h0,
                    ← eval_lemma1 e' Exp.id, R.id_right]

-- Examples:

-- ((1, 2), ((0, 0), 3)) ~ ((0, 0), (1, (2, (0, 3))))
def zero := (Exp.id : Exp Nat)
def one  := Exp.elem 1
def two  := Exp.elem 2
def three := Exp.elem 3
example : R
          ( (one.app two).app  ((zero.app zero).app three) )
          ( (zero.app zero).app (one.app (two.app (zero.app three)))) :=
  by
  -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
  have R.id_left  := @R.id_left
  have R.assoc   := @R.assoc
  translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩]

  unfold zero
  --Minor hiccup here:
  have eq : ∀ α : Type, ∀ q : @Quotient (Exp α) R_Setoid, (Quotient.map₂ Exp.app app_resp) ⟦Exp.id⟧ q = q := fun α => Quotient.ind (fun a => R.id_left)
  replace R.id_left := eq ; clear eq

  simp only [R.id_left]
  apply R.assoc



-- ∀ x y, ((x, (0,0)), y) ~ (x, (y, (0,0)))
example : ∀ x y : Exp Nat, R ((x.app (zero.app zero)).app y) (x.app (y.app (zero.app zero))) :=
  by
  unfold zero
  -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
  have R.id_right:= @R.id_right
  translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩]
  grind


-- ∀ x y, ((x, (0,0)), y) ~ (x, (y, (0,0)))
example : ∀ x y : Exp ℕ, R ((x.app (zero.app zero)).app y) (x.app (y.app (zero.app zero))) :=
  by
  unfold zero
  -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
  have R.id_right:= @R.id_right
  translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩]
  intro x y
  grind

-- ∀ x y, ((x, (0,0)), y) ~ (x, (y, (0,0)))
example : ∀ x y : Exp Nat, R ((x.app (zero.app zero)).app y) (x.app (y.app (zero.app zero))) :=
  by
  unfold zero
  have R.id_right:= @R.id_right
  -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
  translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩]
  grind

example {α β} : ∀ a b : Exp α, ∀ c d : Exp β,
  R ((a.app ((Exp.id).app (Exp.id))).app b) (a.app (b.app ((Exp.id).app (Exp.id))))
∧ R ((c.app ((Exp.id).app (Exp.id))).app d) (c.app (d.app ((Exp.id).app (Exp.id)))) :=
  by
  have R.id_right:= @R.id_right
  -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
  translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩]
  grind
