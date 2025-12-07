--import Tactic.translate
import Tactic.signature
import Mathlib.Tactic

-- From: https://cs.ioc.ee/ewscs/2009/dybjer/mainPalmse-revised.pdf

inductive Ty : Type
| nat : Ty
| arrow : Ty → Ty → Ty
open Ty
infixr : 100 " ⇒' " => arrow

inductive Exp : Ty → Type
| K {a b : Ty}     :  Exp (a ⇒' b ⇒' a)
| S {a b c : Ty}   :  Exp ((a ⇒' b ⇒' c) ⇒' (a ⇒' b) ⇒' (a ⇒' c))
| app {a b : Ty}   :  Exp (a ⇒' b) → Exp a → Exp b
| zero             :  Exp nat
| succ             :  Exp (nat ⇒' nat)
| recN {a : Ty}    :  Exp (a ⇒' (nat ⇒' a ⇒' a) ⇒' nat ⇒' a)
open Exp
infixl : 100 " ⬝ " => app

-- Didn't declare Setoid instance yet
inductive R : {α : Ty} → (Exp α) → (Exp α) → Prop
| refl {α : Ty}{e : Exp α}
        : R (e) (e)
| symm   {α : Ty}{e e' : Exp α}
        : R (e) (e') → R (e') (e)
| trans {α : Ty}{e e' e'' : Exp α}
        : R (e) (e') → R (e') (e'') → R (e) (e'')
| K     {α β : Ty}{x : Exp α} {y : Exp β}
        : R (K ⬝ x ⬝ y) (x)
| S     {α β γ: Ty}{x : Exp (γ ⇒' β ⇒' α)} {y : Exp (γ ⇒' β)} {z : Exp γ}
        : R (S ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z))
| app   {α β : Ty} {a b : Exp (β ⇒' α)} {c d : Exp β}
        : R (a) (b) → R (c) (d) → R (a ⬝ c) (b ⬝ d)
| recN_zero {α : Ty} {e : Exp α} {f : Exp (nat ⇒' α ⇒' α)}
        : R (recN ⬝ e ⬝ f ⬝ zero) (e)
| recN_succ {α : Ty} {n : Exp nat} {e : Exp α} {f : Exp (nat ⇒' α ⇒' α)}
        : R (recN ⬝ e ⬝ f ⬝ (succ ⬝ n)) (f ⬝ n ⬝ (recN ⬝ e ⬝ f ⬝ n))

-- Setoid instance here:
instance R_Setoid {α} : Setoid (Exp α) :=
  { r := R
    iseqv :=
      { refl := λ _ => R.refl
        symm := R.symm
        trans := R.trans
      }
  }

--User-given:
--@[map₂]
def app_resp : ∀ ⦃a₁ a₂ : Exp (α ⇒' β)⦄, R a₁ a₂ → ∀ ⦃b₁ b₂ : Exp α⦄, R b₁ b₂ → R (a₁.app b₁) (a₂.app b₂)
  :=
  fun ⦃a₁ a₂⦄ a ⦃b₁ b₂⦄ a_1 => R.app a a_1


def app_sig (α β : Ty) : Signature (@Exp.app α β) ( (R_Setoid).r ⟹ (R_Setoid).r ⟹ (R_Setoid).r )
  :=
  by
  sorry

example {α β : Ty} : True :=
  by

  letSignature Exp.app (@app_sig)
  sorry




def Ty_inter : Ty → Type
| nat => ℕ

| arrow α β => Exp (α ⇒' β) × (Ty_inter α → Ty_inter β)


def numeral : ℕ → Exp nat
| 0 => zero

| n+1 => succ ⬝ (numeral n)


def reify (α : Ty) (e : Ty_inter α) : Exp α :=
  match α,e with
  | nat, e            => numeral e

  | arrow α β, (c, f) => c


def appsem {α β : Ty} (t : Ty_inter (α ⇒' β)) (e' : Ty_inter α) : Ty_inter β := (t.snd e')


def Exp_inter (α : Ty) : (e : Exp α) → Ty_inter α
| @K α β => (K,
            (λ p ↦ (K ⬝ (reify α p),
            (λ _ ↦ p))))
| @S α β γ => (S,
              (λ x ↦ (S ⬝ (reify (α⇒'β⇒'γ) x),
              (λ y ↦ (S ⬝ (reify (α⇒'β⇒'γ) x) ⬝ (reify (α⇒'β) y),
              (λ z ↦ appsem (appsem x z) (appsem y z)))))))
| @app α β f e  => appsem (Exp_inter (α ⇒' β) f) (Exp_inter α e)
| zero          => (0 : ℕ)
| succ          => (succ,
                   (λ n : ℕ ↦ n+1) )
| @recN α       => (recN,
                   (λ p ↦ (recN ⬝ (reify α p),
                   (λ q ↦ (recN ⬝ (reify α p) ⬝ (reify (nat⇒'α⇒'α) q),
                   (λ n0 ↦ Nat.rec p (λ n r ↦ appsem (appsem q n) r) n0))))))


def nbe (α : Ty) (e : Exp α) : (Exp α) := reify α (Exp_inter α e)


-- e ~ e'  implies [[e]]a = [[e']]a
--User-given:
--@[lift]
lemma Exp_inter_resp (α : Ty) : Signature (Exp_inter α) ((@Setoid.r (Exp α) (@R_Setoid α)) ⟹ Eq) :=
by
  intro e e' h
  induction h
  any_goals aesop
  case app α β a b c d a_r_b c_r_d ab_ih cd_ih =>
    unfold Exp_inter
    rw [ab_ih, cd_ih]

-- e ~ e'  implies nbe a e = nbe a e'
--User-given:
--@[lift]
lemma soundness {a : Ty} {e e' : Exp a} : R e e' → nbe a e = nbe a e' :=
by
  unfold nbe
  intro h1

  letSignature Exp_inter Exp_inter_resp

  --translateF R R_Setoid [⟨lift, Exp_inter, Exp_inter_resp⟩]
  --grind

-- Tait-reducibility relation
def Red : (α : Ty) → (e : Exp α) → Prop
| nat, e       => R e (nbe nat e)

| arrow α β, e => R e (nbe (α ⇒' β) e)  ∧  ∀ e', Red α e' → Red β (app e e')

-- Red a e  implies  e ~ nbe a e
lemma Red_R_nbe (h : Red α e)  : R e (nbe α e) :=
  by
  cases α
  all_goals (unfold Red at h); aesop

-- e ~ e' implies  Red α e = Red α e'
-- User given:
--[@lift]
lemma Red_resp : ∀ e e', R e e' → (Red α e = Red α e')  :=
  by
  refine fun e e' α ↦ ?_ ; apply propext ; revert α e' e
  induction α
  · unfold Red
    intro a b a_R_b
    translateF R R_Setoid [⟨lift, nbe, soundness⟩]
    rw [a_R_b]

  · rename_i α β αIH βIH; clear αIH
    intros f1 f2 f1_R_f2
    apply Iff.intro
    · intro Red_f1
      apply And.intro
      · have f1_R_nbe := Red_R_nbe Red_f1; clear Red_f1
        -- Translate "R a b" to "⟦a⟧ = ⟦b⟧":
        translateF R R_Setoid [⟨lift, nbe, soundness⟩]
        -- f2 ~ f1 ~ nbe f1 = nbe f2
        -- "rewrite [← f1_r_f2, f1_r_nbe, soundness f1_r_f2]"
        grind
      · intro e' Red_e'



        rewrite [← βIH (f1 ⬝ e') (f2 ⬝ e')
                    (by translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩] ; grind)]
        rcases Red_f1 with ⟨left, h0⟩ ; clear left
        exact h0 e' Red_e'

    · intro Red_f2
      apply And.intro
      · have f2_R_nbe := Red_R_nbe Red_f2; clear Red_f2
        -- Translate "R a b" to "⟦a⟧ = ⟦b⟧":
        translateF R R_Setoid [⟨lift, nbe, soundness⟩]
        -- f1 ~ f2 ~ nbe f2 = nbe f1
        -- "rewrite [f1_r_f2, f2_r_nbe, ← soundness f1_r_f2]"
        grind
      · intro e' Red_e'
        rewrite [βIH (f1 ⬝ e') (f2 ⬝ e')
                    (by translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩] ; grind)]
        rcases Red_f2 with ⟨left, h0⟩ ; clear left
        exact h0 e' Red_e'

lemma Red_numeral : Red nat (numeral n) :=
  by
  unfold Red
  induction n
  case zero => exact R.refl

  case succ n' IH =>
    unfold numeral
    have eq : nbe nat (succ ⬝ numeral n') = succ ⬝ (nbe nat $ numeral n') := rfl
    rewrite [eq] ; clear eq
    -- Translate "R a b" to "⟦a⟧ = ⟦b⟧":
    translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩]
    -- succ ⬝ numeral n' ~ succ ⬝ nbe (numeral n')
    -- "rewrite [IH]"
    grind


-- for all e, Red a e
lemma all_Red {e : Exp α} : Red α e :=
  by
  induction e
  all_goals clear α
  case K α β =>
    apply And.intro
    · exact R.refl
    · intro e' Red_e'
      apply And.intro
      · have e'_R_nbe := Red_R_nbe Red_e'; clear Red_e'
        have eq : nbe (β ⇒' α) (K ⬝ e') = K ⬝ nbe α e' := rfl ; rewrite [eq] ; clear eq
        -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
        translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩]
        -- K ⬝ e' ~ K ⬝ nbe e'
        -- "rewrite [e'_r_nbe]"
        grind

      · intro e'' Red_e''; clear Red_e''

        -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
        have R.K := @R.K
        translateF R R_Setoid [⟨lift,Red, Red_resp⟩, ⟨map₂, Exp.app, app_resp⟩]
        -- (K ⬝ e' ⬝ e'') ~ e'
        -- "rewrite [R.K]"
        rewrite [R.K]
        exact Red_e'

  case S α β γ =>
    apply And.intro
    · exact R.refl
    · intro x Red_x
      apply And.intro
      · have x_R_nbe := Red_R_nbe Red_x; clear Red_x
        have eq : nbe ((α ⇒' β) ⇒' α ⇒' γ) (S ⬝ x) = S ⬝ nbe (α ⇒' β ⇒' γ)  x := rfl ; rewrite [eq] ; clear eq
        -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
        translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩]
        -- S ⬝ x ~ S ⬝ nbe x
        -- "rewrite [x_r_nbe]"
        rw [x_R_nbe]
      · intro y Red_y
        apply And.intro
        · have x_R_nbe := Red_R_nbe Red_x; clear Red_x; have y_r_nbe := Red_R_nbe Red_y; clear Red_y
          have eq : nbe (α ⇒' γ) (S ⬝ x ⬝ y) = S ⬝ nbe (α ⇒' β ⇒' γ) x ⬝ nbe (α ⇒' β) y := rfl ; rewrite [eq] ; clear eq
          -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
          translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩]
          -- S ⬝ x ⬝ y ~ S ⬝ nbe x ⬝ y ~ S ⬝ nbe x ⬝ nbe y
          -- "rewrite [x_r_nbe, y_r_nbe]"
          grind
        · intro z Red_z
          rcases Red_x with ⟨left, Red_xz⟩; clear left; specialize Red_xz z Red_z
          rcases Red_y with ⟨left, Red_yz⟩; clear left; specialize Red_yz z Red_z
          rcases Red_xz with ⟨left, Red_xzyz⟩; clear left; specialize Red_xzyz (y ⬝ z) Red_yz

          -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
          have R.S := @R.S
          translateF R R_Setoid [⟨lift, Red, Red_resp⟩]
          -- "rewrite [R.S]"
          grind

  case app α β f x Red_f Red_x =>
    rcases Red_f with ⟨left, h0⟩ ; clear left
    exact h0 x Red_x

  case zero =>
    exact R.refl

  case succ =>
    apply And.intro
    · exact R.refl
    · intro x Red_x
      unfold Red at *; rename' Red_x => x_R_nbe
      have eq : nbe nat (succ ⬝ x) = succ ⬝ (nbe nat x) := rfl ; rewrite [eq] ; clear eq

      -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
      translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩]
      -- succ ⬝ x ~ succ ⬝ nbe x
      -- "rewrite [x_r_nbe]"
      grind

  case recN α =>
    apply And.intro
    · have eq : (nbe (α ⇒' (nat ⇒' α ⇒' α) ⇒' nat ⇒' α) recN) = recN := rfl ; rewrite [eq] ; clear eq
      -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
      translateF R R_Setoid []
      grind
    · intro e' Red_e'
      apply And.intro
      · have e'_R_nbe := Red_R_nbe Red_e'; clear Red_e'
        have eq : nbe ((nat ⇒' α ⇒' α) ⇒' nat ⇒' α) (recN ⬝ e') = recN ⬝ nbe α e' := rfl ; rewrite [eq] ; clear eq
        -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
        translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩]
        -- recN ⬝ e' ~ recN ⬝ nbe e'
        -- "rewrite [e'_r_nbe]"
        grind
      · intro e'' Red_e''
        apply And.intro
        · have e'_R_nbe := Red_R_nbe Red_e'; clear Red_e'; have e''_R_nbe := Red_R_nbe Red_e''; clear Red_e''
          have eq : nbe (nat ⇒' α) (recN ⬝ e' ⬝ e'') = recN ⬝ nbe α e' ⬝ nbe (nat ⇒' α ⇒' α) e'' := rfl
          rewrite [eq] ; clear eq
          -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
          translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩]
          grind
        · intro n Red_n
          have n_R_nbe := Red_n; unfold Red at n_R_nbe ; clear Red_n



          translateF R R_Setoid [⟨lift,Red, Red_resp⟩, ⟨map₂, Exp.app, app_resp⟩]
          rewrite [n_R_nbe]
          translateB R R_Setoid [⟨lift,Red, Red_resp⟩, ⟨map₂, Exp.app, app_resp⟩]

          unfold nbe ; simp [reify]
          induction ((Exp_inter nat n))
          · unfold numeral

            have R.recN_zero := @R.recN_zero
            translateF R R_Setoid [⟨lift, Red, Red_resp⟩]
            -- "rewrite [R.recN_zero]"
            grind
          · rename_i n' IH
            unfold numeral
            rcases Red_e'' with ⟨left, h0⟩; clear left
            specialize h0 (numeral n') (Red_numeral)
            rcases h0 with ⟨left, h0⟩; clear left

            have R.recN_succ := @R.recN_succ
            translateF R R_Setoid [⟨lift,Red, Red_resp⟩]
            -- "rewrite [R.recN_succ]"
            grind

-- e ~ nbe a e
lemma R_nbe {e : Exp a} : R e (nbe a e) := Red_R_nbe all_Red

-- nbe a e = nbe a e' implies e ~ e'
lemma completeness : nbe a e = nbe a e' → R e e' :=
  by
  intro eq
  -- Translate "R a b" to "⟦a⟧ = ⟦b⟧"
  have R_nbe := @R_nbe
  translateF R R_Setoid []
  -- e ~ nbe e = nbe e' ~ e'
  -- "rewrite [R_nbe, eq, ← R_nbe]"
  rw [R_nbe, eq, ← R_nbe]

-- e ~ e' ↔ nbe a e = nbe a e'
lemma correctness {e e' : Exp a} : R e e' ↔ nbe a e = nbe a e' := ⟨soundness, completeness⟩



-- Examples:

example {α : Ty} {a b : Exp α}
                        (f : (x y : Exp α) → (@R α x y) → Nat)
                        (hf : (x y : Exp α) → (xRy : @R α x y) → f x y xRy = 3)
                        (aRb : R a b)
                        : (f a b aRb) = 3 :=
  by
  /-
  revert aRb hf f b a α
  generalize eq : @R = R'
  rewrite [R_eq] at eq
  subst eq
  beta_reduce
  intro α a b f hf aRb

  exact hf a b aRb
  -/
  sorry


example : (α : Ty) → (a b c : Exp α) → (R a a) ∧ (R a b → R b a) ∧ (R a b → R b c → R a c) :=
  by
  /-
  intro α a b c
  repeat any_goals apply And.intro
  · exact R.refl
  · exact R.symm
  · exact R.trans
  -/
  translateF R R_Setoid []
  grind



example :
      (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Exp nat)
      → (@R nat x1 x13)
      → (@R nat x10 x5)
      → (@R nat x4 x12)
      → (@R nat x7 x12)
      → (@R nat x14 x6)
      → (@R nat x14 x9)
      → (@R nat x12 x12)
      → (@R nat x12 x17)
      → (@R nat x20 x3)
      → (@R nat x7 x1)
      → (@R nat x3 x14)
      → (@R nat x9 x18)
      → (@R nat x19 x14)
      → (@R nat x12 x6)
      → (@R nat x10 x4)
      → (@R nat x6 x8)
      → (@R nat x16 x9)
      → (@R nat x6 x17)
  := by
    translateF R R_Setoid []
    grind

example :
      (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : Exp nat)
      → (@R nat x12 x4)
      → (@R nat x5 x1)
      → (@R nat x6 x9)
      → (@R nat x17 x7)
      → (@R nat x1 x9)
      → (@R nat x4 x17)
      → (@R nat x17 x12)
  := by
    translateF R R_Setoid []
    grind

example : ∀ x y : Exp (nat ⇒' nat), R (x.app (x.app (x.app zero))) (x.app (y.app (x.app zero))) :=
  by
  translateF R R_Setoid [⟨map₂, Exp.app, app_resp⟩]
  sorry
