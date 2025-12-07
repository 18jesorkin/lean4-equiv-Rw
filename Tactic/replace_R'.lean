import Lean
import Tactic.signature
import Mathlib.Tactic

open Lean Elab Tactic Term Meta

def add_Req' (R : Name) (Equivalence_R : Name) : TacticM Name :=
  do
  let RType := ← inferType (Lean.mkConst R)

  let eq_type := ← forallTelescope RType fun alphas relation_A₁ => do
    let A₁            := ((relation_A₁).getAppArgs)[0]!
    let R_alphas      := ← mkAppOptM R             $ alphas.map some
    let EquivR_alphas := ← mkAppOptM Equivalence_R $ alphas.map some
    let lhs   := Lean.mkConst R
    let rhs   := ← mkLambdaFVars alphas $ ← mkAppOptM ``Setoid.r #[some A₁, some $ ← mkAppOptM ``Setoid.mk $ #[some A₁, some R_alphas, some  EquivR_alphas]]
    mkEq lhs rhs

  -- Elaborate automated tactic proof as an expression
  -- Ensuring there are no meta-variables (so kernel doesn't complain)
  let eq_pf := ← Term.elabTerm (← `(by rfl)) (some eq_type)
  Term.synthesizeSyntheticMVarsNoPostponing
  let eq_pf ← instantiateMVars eq_pf

  let Req := (R.appendAfter "_eq")
  withMainContext do
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.define Req eq_type eq_pf
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]
  return Req

elab "add_Req'" R:ident Equiv_R:ident : tactic => do let feq := ← add_Req' (R.getId) (Equiv_R.getId)

-- R             : ∀ α₁ ... αₙ , relation    (A₁)
-- Equivalence_R : ∀ α₁ ... αₙ , Equivalence (R α₁ ... αₙ)

-- Replace "R" everywhere with "fun α₁ ... αₙ => @Setoid.r A₁ (@Setoid.mk A₁ (R α₁...αₙ) (Equivalence_R α₁...αₙ))"
def replace_R' (R : Name) (Equivalence_R : Name) : TacticM Unit :=
  do
      -- Generalize on R
    let R_Ident    := mkIdent R
    let R'_Ident   := mkIdent (R.toString ++ "'").toName
    let eq_Ident  := mkIdent ("eq").toName
    evalTactic (← `(tactic | generalize $eq_Ident:ident : (@$R_Ident:ident) = $R'_Ident:ident at *))

    -- Rewrite "R_eq : R = R_eq : R = (λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧)"
    -- at "eq : R = R'"
    let R_eq       := ← add_Req' R Equivalence_R
    let R_eq_Ident := mkIdent R_eq
    evalTactic (← `(tactic | rewrite [($R_eq_Ident:ident)] at ($eq_Ident:ident)))
    evalTactic (← `(tactic | clear $R_eq_Ident))

    -- Substitute "eq : (λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧)  =  R'" everywhere
    evalTactic (← `(tactic | subst ($eq_Ident:ident)))

    -- Beta-reduce the goal
    evalTactic (← `(tactic | beta_reduce))


elab "replace_R'" R:ident Equiv_R:ident : tactic => do replace_R' (R.getId) (Equiv_R.getId)
