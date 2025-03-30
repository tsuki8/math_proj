import Lean
import Lean.Widget.UserWidget
import Lean.Data.Json

#eval Lean.versionString

open Lean Elab Tactic Meta Json


partial def exprToJson (e : Expr) : MetaM Json := do
  match e with
  | Expr.bvar i =>
    pure $ mkObj [("type", "bvar"), ("index", i)]

  | Expr.fvar f =>
    pure $ mkObj [("type", "fvar"), ("index", s!"{f.name}")]

  | Expr.mvar m =>
    pure $ mkObj [("type", "mvar"), ("index", s!"{m.name}")]

  | Expr.sort lvl =>
    pure $ mkObj [("type", "sort"), ("level", toString lvl)]

  | Expr.const name _ =>
    pure $ mkObj [("type", "const"), ("name", name.toString)]

  | Expr.app fn arg => do
    let fnJson ← exprToJson fn
    let argJson ← exprToJson arg
    pure $ mkObj [("type", "app"), ("function", fnJson), ("argument", argJson)]

  | Expr.lam name ty body _ => do
    let tyJson ← exprToJson ty
    let bodyJson ← exprToJson body
    pure $ mkObj [("type", "lambda"), ("name", name.toString), ("argType", tyJson), ("body", bodyJson)]

  | Expr.forallE name ty body _ => do
    let tyJson ← exprToJson ty
    let bodyJson ← exprToJson body
    pure $ mkObj [("type", "forall"), ("name", name.toString), ("argType", tyJson), ("body", bodyJson)]

  | Expr.lit (Literal.natVal n) =>
    pure $ mkObj [("type", "lit"), ("value", n)]

  | Expr.lit (Literal.strVal s) =>
    pure $ mkObj [("type", "lit"), ("value", s)]

  | Expr.mdata _ e =>
    exprToJson e

  | Expr.proj _ idx e => do
    let eJson ← exprToJson e
    pure $ mkObj [("type", "proj"), ("index", idx), ("structure", eJson)]

  | _ =>
    pure $ mkObj [("type", "unknown")]

def ViewAST : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | [] => throwError "No subgoals to prove"
  | goal::_ => do
      let goalType ← Lean.MVarId.getType goal

      let astJson ← exprToJson goalType

      logInfo m!"Goal AST JSON:\n{astJson.compress}"

elab "view_ast" : tactic => do
  ViewAST

example : 1 + 1 = 2 := by
  view_ast
  <;> simp
