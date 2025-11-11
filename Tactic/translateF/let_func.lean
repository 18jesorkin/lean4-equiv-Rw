import Lean
import Mathlib
import Tactic.respList
import Tactic.translateF.replace_R

open Lean Elab Tactic Term Meta


-- R         : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → (_ : X) → (_ : X) → Prop
-- R_Setoid  : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → Setoid X
-- map₂      : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₘ : Tₘ) → (_ : X) → (_ : X) → X
-- map₂_resp : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₘ : Tₘ) →
--             ∀ ⦃a₁ a₂ : X⦄, R a₁ a₂ → ∀ ⦃b₁ b₂ : X⦄, R b₁ b₂ → R (map₂ a₁ b₁) (map₂ a₂ b₂)

--map₂'_eq   : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₘ : Tₘ) →
--             (e₁ : X) → (e₂ : X) → ⟦@map₂ x₁ ... xₘ e₁ e₂⟧ = @map₂' x₁ ... xₘ ⟦e₁⟧ ⟦e₂⟧
--           := fun x₁ ... xₘ e₁ e₂ => (Quotient.map₂_mk (@Exp.app α β) (@app_resp α β) e₁ e₂).symm

--For Godel-T:
  -- (R)    R    : {α : Ty} → (_ : Exp α) → (_ : Exp α) → Prop
  -- (n = 1)
  -- (map₂) app  : {α : Ty} → {β : Ty} → (_ : Exp (α ⇒' β)) → (_ : Exp α) → Exp β
  -- (m = 2)
  -- (map₂'_eq) app'_mk {α} {β} : (x : Exp (α ⇒' β)) → (y : Exp α) → ⟦x.app y⟧ = app' ⟦x⟧ ⟦y⟧
  -- := fun x y => (Quotient.map₂_mk (@Exp.app α β) (@app_resp α β) x y).symm


def let_func (tag : Tag) (func : Name) (func_resp : Name) : TacticM Name := do
  --Step1: Count number of parameters for func, m
  let func_Expr := (Expr.const func [])
  let func_Type := ← inferType func_Expr
  let func_resp_Expr := (Expr.const func_resp [])
  let m := func_Type.getNumHeadForalls-2

  --Step2: Add constant func_eq to Local-Context
  let value : Expr := ← forallBoundedTelescope func_Type (some $ m) fun xs _ => do
      let QuotientApp := ← mkAppM tag.toName #[(mkAppN func_Expr xs), (mkAppN func_resp_Expr xs)]
      mkLambdaFVars xs QuotientApp
  let type := ← inferType value
  withMainContext do
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.define (func.appendAfter "_eq") type value
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

  --Step 3: Return new identififer
  return (func.appendAfter "_eq")


def translateF (R : Name) (R_Setoid : Name) (resp_list : List (Tag × Name × Name)) : TacticM Unit := do
  replace_R R R_Setoid

  let mut eq_list := []
  for (tag, func, func_resp) in resp_list do
    let eq := mkIdent (← let_func tag func func_resp)
    eq_list := eq_list.concat eq

  let mut restart := true
  while restart do
    restart := false
    for eq in eq_list do
      try
        (evalTactic (← `(tactic| simp only [← $eq] at *)))
        restart := true
      catch err => continue


  /-
  For "translateB":

  restart := true
  while restart do
    restart := false
    for eq in eq_list do
      try
        (evalTactic (← `(tactic| simp only [$eq:term] at *)))
        restart := true
      catch err => continue


  let R_Setoid := mkIdent R_Setoid
  evalTactic (← `(tactic| simp only [Quotient.eq, $R_Setoid:term] at *))
  -/

  for eq in eq_list do
    (evalTactic (← `(tactic| clear $eq)))






syntax list := ( "⟨" ident "," ident "," ident "⟩")*

elab "translateF" R:ident R_Setoid:ident resp_list:list : tactic =>
  do
  --let `(list| $[$resp_list]*) := resp_list | unreachable!
  translateF @R.getId @R_Setoid.getId [⟨.map₂, `Nat.add, `add_resp⟩, ⟨.map₂, `Nat.mul, `mul_resp⟩]


@[app_unexpander Quotient.lift]
def unexpandLift : Lean.PrettyPrinter.Unexpander
  | `($_ $t:term ⋯) => `(⟦$t⟧)
  | `($_ $t:term $_:term) => `(⟦$t⟧)
  | _ => throw ()

@[app_unexpander Quotient.lift₂]
def unexpandLift₂ : Lean.PrettyPrinter.Unexpander
  | `($_ $t:term ⋯) => `(⟦$t⟧)
  | `($_ $t:term $_:term) => `(⟦$t⟧)
  | _ => throw ()

@[app_unexpander Quotient.map]
def unexpandMap : Lean.PrettyPrinter.Unexpander
  | `($_ $t:term ⋯) => `(⟦$t⟧)
  | `($_ $t:term $_:term) => `(⟦$t⟧)
  | _ => throw ()

@[app_unexpander Quotient.map₂]
def unexpandMap₂ : Lean.PrettyPrinter.Unexpander
  | `($_ $t:term ⋯) => `(⟦$t⟧)
  | `($_ $t:term $_:term) => `(⟦$t⟧)
  | _ => throw ()
