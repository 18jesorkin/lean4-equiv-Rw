import Lean
import Mathlib

open Lean Elab Tactic Term Meta

inductive Tag
  | map
  | map₂
  | lift
  | lift₂
deriving Inhabited

def Tag.toName : Tag → Lean.Name
  | map => ``Quotient.map_mk
  | map₂ => ``Quotient.map₂_mk
  | lift => ``Quotient.lift_mk
  | lift₂ => ``Quotient.lift₂_mk


declare_syntax_cat tag
syntax "map" : tag
syntax "map₂": tag
syntax "lift": tag
syntax "lift₂": tag
syntax entry    := "⟨" tag "," ident "," ident "⟩"
syntax resp_list := "[" entry,* "]"


def parse_entry : TSyntax `entry → (Tag × Name × Name)
  | `(entry| ⟨map, $func, $func_resp⟩) => ⟨.map, func.getId, func_resp.getId⟩
  | `(entry| ⟨map₂, $func, $func_resp⟩) => ⟨.map₂, func.getId, func_resp.getId⟩
  | `(entry| ⟨lift, $func, $func_resp⟩) => ⟨.lift, func.getId, func_resp.getId⟩
  | `(entry| ⟨lift₂, $func, $func_resp⟩) => ⟨.lift₂, func.getId, func_resp.getId⟩
  | _ => unreachable!
