import Lean
import Mathlib.Data.Quot

open Lean Elab Tactic Term Meta

/-
From:
  https://github.com/FWuermse/grw/blob/main/Grw/Morphism.lean
{
-/
def relation (α : Sort u) := α → α → Prop

def respectful {α : Sort u} {β : Sort v} (r : relation α) (r' : relation β) : relation (α → β) :=
  fun f g => ∀ x y, r x y → r' (f x) (g y)
notation:55 r " ⟹ " r' => respectful r r'

def Signature {α : Sort u} (m : α) (r : relation α) := r m m
/-
                                        }
-/

/-
We will be considering respectful operations of the form:
  f_sig : α₁ → ⋯ → αₘ → Signature f (R₁ ⟹ R₂)
  f_sig : α₁ → ⋯ → αₘ → Signature f (R₁ ⟹ R₂ ⟹ R₃)
  f_sig : α₁ → ⋯ → αₘ → Signature f (R₁ ⟹ Eq)
  f_sig : α₁ → ⋯ → αₘ → Signature f (R₁ ⟹ R₂ ⟹ Eq)
-/


--Does NOT Typecheck #check fun n => Quotient.map₂_mk (Nat.add) (add_sig n)
def arrowsToLift (arrows : Expr) : Option Name :=
  match arrows with
    | .app (.app (.app (.app (.const ``respectful _) _) _) R₁) arrows  =>
      match arrows with
                                    --Signature f (R₁ ⟹ Eq)
      | .app (.const ``Eq _) _  => return ``Quotient.lift_mk
                                                  --Signature f (R₁ ⟹ R₂)
      | .app (.app (.const ``Setoid.r _) _) _    => return ``Quotient.map_mk
      | .app R₂ arrows =>
        match arrows with
                                      --Signature f (R₁ ⟹ R₂ ⟹ Eq)
        | .app (.const ``Eq _) _ => return ``Quotient.lift₂_mk
                                      --Signature f (R₁ ⟹ R₂ ⟹ R₃)
        | .app (.app (.const ``Setoid.r _) _) _ => return ``Quotient.map₂_mk

        | _ => none
      | _ => none
    | _ => none


def letSignature (f : Name) (f_sig : Name) : TacticM Name := do
  let f_sig     := Lean.mkConst f_sig
  let f_sigType := ← inferType f_sig

  -- eq_pf := fun α₁ ... αₙ => liftFxn (f₁) (f_sig α₁ ... αₙ)
  let eq_pf   := ← forallTelescope f_sigType fun alphas sig_f₁_arrows₁ => do
    let f₁                   := (sig_f₁_arrows₁.getAppArgs)[1]!
    let arrows₁              := (sig_f₁_arrows₁.getAppArgs)[2]!
    let .some liftFxn       := arrowsToLift arrows₁ | throwError "Must have type ∀ α₁ ... αₙ, Signature f₁ (R₁ ⟹ ...)"
    mkLambdaFVars alphas (← mkAppM liftFxn #[f₁, (← mkAppM' f_sig alphas)])
  let eq_Type := ← inferType eq_pf

  withMainContext do
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.define (f.appendAfter "_eq") eq_Type eq_pf
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

  return f.appendAfter "_eq"


syntax entry    := "⟨" ident "," ident "⟩"
syntax sig_list := "[" entry,* "]"

def parse_entry : TSyntax `entry → (Name × Name)
  | `(entry| ⟨$f, $f_sig⟩) => ⟨f.getId, f_sig.getId⟩
  | _ => unreachable!
