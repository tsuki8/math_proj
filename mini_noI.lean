import Lean

open Lean Meta

-- 定义一个函数来打印表达式的 AST
def printExpr (e : Expr) : Meta Unit := do
  let e ← instantiateMVars e
  let fmt ← ppExpr e
  IO.println (toString fmt)

-- 示例 Lean 代码
def exampleCode : Expr :=
  `(λ (x : Nat) => x + 1)

-- 提取并打印 AST
#eval printExpr exampleCode
