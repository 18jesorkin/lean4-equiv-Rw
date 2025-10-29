import Lean
import Mathlib

open Lean Elab Tactic Term Meta

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

@[app_unexpander Quotient.map₂]
def unexpandMap₂ : Lean.PrettyPrinter.Unexpander
  | `($_ $t:term ⋯) => `(⟦$t⟧)
  | `($_ $t:term $_:term) => `(⟦$t⟧)
  | _ => throw ()

@[app_unexpander Quotient.map]
def unexpandMap : Lean.PrettyPrinter.Unexpander
  | `($_ $t:term ⋯) => `(⟦$t⟧)
  | `($_ $t:term $_:term) => `(⟦$t⟧)
  | _ => throw ()

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

inductive LiftType
  | map
  | map₂
  | lift
  | lift₂

def LiftType.toName : LiftType → Lean.Name
  | map => ``Quotient.map_mk
  | map₂ => ``Quotient.map₂_mk
  | lift => ``Quotient.lift_mk
  | lift₂ => ``Quotient.lift₂_mk


def add_whatever (ty : LiftType) (map₂ : Name) (map₂_resp : Name) : TacticM Unit := do
  --Step1: Count number of parameters for map₂, m
  let map₂_Expr := (Expr.const map₂ [])
  let map₂_Type := ← inferType map₂_Expr
  let map₂_resp_Expr := (Expr.const map₂_resp [])
  let m := map₂_Type.getNumHeadForalls-2

  --Step2: Add constant map₂' to environment
  --   (map₂' := fun {x₁ : T₁} {x₂ : T₂} ⋯ {xₘ : Tₘ} => Quotient.map₂ (@map₂ x₁ ... xₘ) (@map₂_resp x₁ ... xₘ))
  let value : Expr := ← forallBoundedTelescope map₂_Type (some $ m) fun xs _ => do
      let QuotientApp := ← mkAppM ty.toName #[(mkAppN map₂_Expr xs), (mkAppN map₂_resp_Expr xs)]
      mkLambdaFVars xs QuotientApp
  let type := ← inferType value

  let env              := ← getEnv
  let restrictedPrefix := env.asyncPrefix?.casesOn' ("") (fun name => name.toString ++ ".")
  let decl := Declaration.defnDecl {
    name := (restrictedPrefix ++ map₂.toString ++ "'").toName
    levelParams := []
    value  := value
    type   := type
    hints  := default
    safety := .safe
  }
  addDecl decl

  --evalTactic (← `(tactic | let hi := 3))

elab "add" "map₂" map₂:ident map₂_resp:ident : tactic => do add_lift (LiftType.map₂) @map₂.getId @map₂_resp.getId
elab "add" "lift" map₂:ident map₂_resp:ident : tactic => do add_map₂ @map₂.getId @map₂_resp.getId

def R : Nat → Nat → Prop := fun n1 n2 => n1 = n2

instance R_Setoid : Setoid Nat :=
  {
    r     := R
    iseqv := sorry
              }


def add_resp : ∀ ⦃a₁ a₂ : ℕ⦄, a₁ ≈ a₂ → ∀ ⦃b₁ b₂ : ℕ⦄, b₁ ≈ b₂ → a₁.add b₁ ≈ a₂.add b₂
  := by sorry

lemma test : True :=
  by
  add_map₂ Nat.add add_resp
  --let Nat.add' := Quotient.map₂ Nat.add add_resp
  have : test.Nat.add' = test.Nat.add' := rfl
  #print test.Nat.add'
  --have : Nat.add' = Nat.add' := rfl
  exact trivial


/-
namespace Basket

abbrev Key := Name




inductive Value where
  | parent (key : Key)
  | premise (n : Name)
  deriving Inhabited

structure Entry where
  key : Key
  val : Value
  deriving Inhabited

structure Info where
  parents : HashSet Key
  prems   : HashSet Name

def Info.add (info : Info) : Value → Info
  | .parent p  => { info with parents := info.parents.insert p }
  | .premise n => { info with prems := info.prems.insert n }

instance : EmptyCollection Info where
  emptyCollection := { parents := ∅, prems := ∅ }

end Basket

open Basket in
abbrev Extension := SimpleScopedEnvExtension Entry (HashMap Key Info)

initialize extension : Extension ← registerSimpleScopedEnvExtension {
  initial := ∅
  addEntry infos entry := infos.alter entry.key (·.getD ∅ |>.add entry.val)
}

namespace Extension

-- NOTE: The `stx?` argument is a workaround for (seemingly) not having `try catch` in
--       `CommandElabM`, which we would need in the elaborator for the `egg_basket` command.
def getBasket (ext : Extension) (key : Basket.Key) (stx? : Option Syntax := none) :
    CoreM Basket.Info := do
  if let some basket := (ext.getState <| ← getEnv)[key]? then
    return basket
  else if let some stx := stx? then
    throwErrorAt stx "Unknown egg basket"
  else
    throwError "Unknown egg basket '{key}'"

partial def getAllBasketPremises (ext : Extension) (key : Basket.Key) : CoreM (Array Name) := do
  return (← go key).toArray.insertionSort Name.lt
where
  go (key : Basket.Key) : CoreM (HashSet Name) := do
    let info ← ext.getBasket key
    let mut prems := info.prems
    for parent in info.parents do
      prems := prems.union (← go parent)
    return prems

partial def basketContains (ext : Extension) (key : Basket.Key) (premise : Name) : CoreM Bool := do
  let info ← ext.getBasket key
  if info.prems.contains premise then return true
  for parent in info.parents do
    if ← ext.basketContains parent premise then return true
  return false

end Extension

initialize
  -- TODO: I'm guessing we should use some other function, which does not mention "builtin".
  registerBuiltinAttribute {
    name  := `egg
    descr := "equality saturation theorem"
    applicationTime := .afterCompilation
    add premise stx attrKind := do
      -- TODO: I feel like we would want `resolveGlobalConstNoOverload`, but when we pass an
      --       identifier of the form `_root_.<name>` the `_root_` does not appear in the `entry`.
      let premise ← unresolveNameGlobal premise
      -- TODO: Validate the entry.
      match stx with
      | `(Parser.Attr.simple|egg $key:ident) => addDecl default
                                                --extension.add ⟨key.getId, .premise premise⟩ attrKind
      | _                                    => throwError "'egg' attribute expectes a basket name"
  }

syntax egg_basket_thms := " with " ident,+

elab "egg_basket " key:ident " extends " parents:ident,+ prems?:(egg_basket_thms)? : command => do
  for parent in parents.getElems do
    extension.add { key := key.getId, val := .parent parent.getId }
  let some prems := prems? | return
  let `(egg_basket_thms| with $prems,*) := prems | return
  for premise in prems.getElems do
    extension.add { key := key.getId, val := .premise premise.getId }

private partial def basketMsg (key : Name) (stx? : Option Syntax := none) :
    Elab.Command.CommandElabM MessageData := do
  let info ← Elab.Command.liftCoreM do extension.getBasket key stx?
  let premises := info.prems.toList.mergeSort Name.lt |>.map MessageData.ofConstName
  let mut msg := .joinSep premises ", "
  for parent in info.parents do
    let parentHeader := m!"* extends {parent.toString}:"
    let parentBody := indentD (← basketMsg parent)
    msg := m!"{msg}\n{parentHeader}{parentBody}"
  return msg

elab "#egg_basket " key:ident : command => do
  logInfo (← basketMsg key.getId key.raw)
-/
