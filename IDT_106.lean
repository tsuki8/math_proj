-- import Mathlib

-- open Nat
import Mathlib

import Lean

set_option autoImplicit false

open Nat
theorem aa(a b c : Nat): a + b + c =  c + a + b := by
 rw[add_comm]
 sorry

open Lean Elab Tactic

syntax (name := sorry_all) "sorry_all" : tactic

@[tactic sorry_all]
def sorryAllImpl : Tactic
| `(tactic| sorry_all) => do
  let allGoals <- getUnsolvedGoals
  for goal in allGoals do
    admitGoal goal
  return
| _ => throwUnsupportedSyntax

def xs {A B C : Type} : A = B -> C = A -> B = A := by
  intro x y
  apply Eq.trans
  sorry_all
