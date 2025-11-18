import Tactic.translate

def R : Nat → Nat → Prop := fun n₁ n₂ => ∃ m, n₁ % m = n₂ % m ∧ m = 0

-- Setoid instance here:
instance R_Setoid : Setoid Nat :=
  { r := R
    iseqv :=
      { refl :=
          by
          unfold R
          aesop
        symm :=
          by
          unfold R
          aesop
        trans :=
          by
          unfold R
          aesop
                }
                  }

--User-given:
-- @[map₂]
def add_resp : ∀ ⦃a₁ a₂ : Nat⦄, R a₁ a₂ → ∀ ⦃b₁ b₂ : Nat⦄, R b₁ b₂ → R (Nat.add a₁ b₁) (Nat.add a₂ b₂)
  :=
  by
  unfold R
  intro a₁ a₂ h1 b₁ b₂ h2
  simp only [exists_eq_right, Nat.mod_zero] at *
  aesop


example : (a b c : Nat) → (R a a) ∧ (R a b → R b a) ∧ (R a b → R b c → R a c) :=
  by
  intro a b c
  /-
  repeat any_goals apply And.intro
  all_goals unfold R ; aesop
  -/
  translateF R R_Setoid []
  grind

example : (x y : Nat) → R x y →  R (x.add (x.add (x.add (x.add y)))) (y.add (y.add (y.add (y.add x)))) :=
  by
  /-
  intro x y xRy
  repeat any_goals apply add_resp
  all_goals unfold R at * ; aesop
  -/
  translateF R R_Setoid [⟨map₂, Nat.add, add_resp⟩]
  grind


--Before:   resp_list = [⟨map₂, Nat.add, add_resp⟩]
-- @[map₂]
def mul_resp :  ∀ ⦃a₁ a₂ : ℕ⦄, R a₁ a₂ → ∀ ⦃b₁ b₂ : ℕ⦄, R b₁ b₂ → R (a₁.mul b₁) (a₂.mul b₂)
  := by unfold R ; aesop
--After:    resp_list = [⟨map₂, Nat.add, add_resp⟩, ⟨map₂, Nat.mul, mul_resp⟩]

lemma test (x_R_y : R x y) : R (3 * (1 + (7 + x) + 5)) ((1 + 7 + y + 5) * 3)   :=
  by
  simp_rw [HAdd.hAdd, Add.add, HMul.hMul, Mul.mul]

  translateF R R_Setoid [⟨map₂, Nat.add, add_resp⟩, ⟨map₂, Nat.mul, mul_resp⟩]
  rewrite [x_R_y]
  translateB R R_Setoid [⟨map₂, Nat.add, add_resp⟩, ⟨map₂, Nat.mul, mul_resp⟩]

  suffices eq : (Nat.mul 3 ((Nat.add 1 (Nat.add 7 y)).add 5)) = ((((Nat.add 1 7).add y).add 5).mul 3)
    by
    rewrite [eq] ; clear eq
    apply R_Setoid.iseqv.refl
  grind


lemma test2 (x_R_y : R x y) (h0 : R (3 + (1 * (7 + x) * 5)) ((1 + 7 * y + 5) * 3)) : R (3 * (1 + (7 + x) + 5)) ((1 + 7 + y + 5) * 3)   :=
  by
  simp_rw [HAdd.hAdd, Add.add, HMul.hMul, Mul.mul] at *

  translateF R R_Setoid
    [⟨map₂, Nat.add, add_resp⟩,
     ⟨map₂, Nat.mul, mul_resp⟩]
  rw [x_R_y]
  translateB R R_Setoid
    [⟨map₂, Nat.add, add_resp⟩,
     ⟨map₂, Nat.mul, mul_resp⟩]

  suffices eq : (Nat.mul 3 ((Nat.add 1 (Nat.add 7 y)).add 5)) = ((((Nat.add 1 7).add y).add 5).mul 3)
    by
    rewrite [eq] ; clear eq
    apply R_Setoid.iseqv.refl
  grind


def mul2 := fun n : Nat => 2*n

lemma mul2_resp : R a b → R (mul2 a) (mul2 b) :=
  by
  unfold R
  simp_all only [exists_eq_right, Nat.mod_zero, implies_true]

example  (x_R_y : R x y) : R (mul2 (x+y)) (mul2 (y+x)) :=
  by
  simp only [HAdd.hAdd, Add.add]
  translateF R R_Setoid [⟨map, mul2, mul2_resp⟩, ⟨map₂, Nat.add, add_resp⟩]
  grind
