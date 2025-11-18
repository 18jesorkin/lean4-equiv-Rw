import Lean
import Mathlib
import Tactic.respList
import Tactic.replace_R

open Lean Elab Tactic Term Meta

-- R         : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → (_ : X) → (_ : X) → Prop
-- R_Setoid  : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → Setoid X

-- If tag = "map" or "lift":
-- func      : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₘ : Tₘ) → (X_inst₁) → (X_inst₂)

-- If tag = "map₂" or "lift₂":
-- func      : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₘ : Tₘ) → (X_inst₁) → (X_inst₂) → (X_inst₃)

-- If tag = "map₂":
-- func_resp : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₘ : Tₘ) →
--             ∀ ⦃a₁ a₂ : X_inst₁⦄, (R_inst₁) a₁ a₂
--           → ∀ ⦃b₁ b₂ : X_inst₂⦄, (R_inst₂) b₁ b₂
--           → (R_inst₃) (func a₁ b₁) (func a₂ b₂)

-- If tag = "lift₂":
-- func_resp : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₘ : Tₘ) →
--             ∀ (a₁ : X_inst₁) (a₂ : X_inst₂)
--               (b₁ : X_inst₁) (b₂ : X_inst₂),
--            (R_inst₁) a₁ b₁ → (R_inst₂) a₂ b₂ → f a₁ a₂ = f b₁ b₂
def let_func (tag : Tag) (func : Name) (func_resp : Name) : TacticM Name := do
  --Step1: Count number of parameters for func, m
  let func_Expr := (Expr.const func [])
  let func_Type := ← inferType func_Expr
  let func_resp_Expr := (Expr.const func_resp [])
  let mut m := 0
  match tag with
    | Tag.map => m   := func_Type.getNumHeadForalls-1
    | Tag.map₂ => m  := func_Type.getNumHeadForalls-2
    | Tag.lift => m  := func_Type.getNumHeadForalls-1
    | Tag.lift₂ => m := func_Type.getNumHeadForalls-2

  --Step2: Add constant func_eq to Local-Context where:
  --  If tag = "map₂":
  --      func_eq : (x₁ : T₁) → ⋯ → (xₘ : Tₘ)
  --              → (a : X_inst₁) → (b : X_inst₂) → ⟦f⟧ ⟦a⟧ ⟦b⟧ = ⟦f a b⟧
  --
   --  If tag = "lift₂":
  --      func_eq : (x₁ : T₁) → ⋯ → (xₘ : Tₘ)
  --              → (a : X_inst₁) → (b : X_inst₂) → ⟦f⟧ ⟦a⟧ ⟦b⟧ = f a b
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


def translateF (R : Name) (R_Setoid : Name) (resp_list : Array (Tag × Name × Name)) : TacticM Unit := do
  --Step 1: Replace all instances of "R x₁⋯xₙ a b" with "⟦a⟧ = ⟦b⟧"
  replace_R R R_Setoid

  --Step 2: For each respectful func, add "func_eq" to a list
  let mut eq_list := []
  for (tag, func, func_resp) in resp_list do
    let eq := mkIdent (← let_func tag func func_resp)
    eq_list := eq_list.concat eq

  -- Step 3:
  -- For each eq in eq_list:
  --  if "simp only [← $eq] at *" succeeds:
  --    restart the for-loop
  --  else:
  --    continue
  --
  -- This replaces all functions with their Quotient-versions
  let mut restart := true
  while restart do
    restart := false
    for eq in eq_list do
      try
        (evalTactic (← `(tactic| simp only [← $eq] at *)))
        restart := true
      catch err => continue

  -- Step 4:
  -- eq_list is no longer
  -- needed in Local-Context
  for eq in eq_list do
    (evalTactic (← `(tactic| clear $eq)))


elab "translateF" R:ident R_Setoid:ident resp_list:resp_list : tactic =>
  do
  let `(resp_list| [$[$resp_list],*]) := resp_list | unreachable!
  let resp_list := resp_list.map parse_entry
  translateF @R.getId @R_Setoid.getId resp_list



def translateB (R : Name) (R_Setoid : Name) (resp_list : Array (Tag × Name × Name)) : TacticM Unit := do
  --Step 1: For each respectful func, add "func_eq" to a list
  let mut eq_list := []
  for (tag, func, func_resp) in resp_list do
    let eq := mkIdent (← let_func tag func func_resp)
    eq_list := eq_list.concat eq

  -- Step 2:
  -- For each eq in eq_list:
  --  if "simp only [$eq] at *" succeeds:
  --    restart the for-loop
  --  else:
  --    continue
  --
  -- This translates the Quotient-functions back to their original versions.
  let mut restart := true
  while restart do
    restart := false
    for eq in eq_list do
      try
        (evalTactic (← `(tactic| simp only [$eq:term] at *)))
        restart := true
      catch err => continue

  -- Step 3:
  -- eq_list is no longer
  -- needed in Local-Context
  for eq in eq_list do
    (evalTactic (← `(tactic| clear $eq)))

  --Step 4: Replace all instances of "⟦a⟧ = ⟦b⟧" with "R x₁⋯xₙ a b"
  let R_Setoid := mkIdent R_Setoid
  evalTactic (← `(tactic| simp only [Quotient.eq, $R_Setoid:term] at *))

elab "translateB" R:ident R_Setoid:ident resp_list:resp_list : tactic =>
  do
  let `(resp_list| [$[$resp_list],*]) := resp_list | unreachable!
  let resp_list := resp_list.map parse_entry
  translateB @R.getId @R_Setoid.getId resp_list



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
