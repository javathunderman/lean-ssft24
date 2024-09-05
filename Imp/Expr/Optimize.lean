import Imp.Expr.Basic
import Imp.Expr.Eval

namespace Imp.Expr

/--
Optimizes an expression by folding constants.
-/
def optimize : Expr → Expr
  | .const i => .const i
  | .var x => .var x
  | .un op e =>
    match optimize e with
    | .const i =>
      if let some i' := op.apply i then
        .const i'
      else .un op (.const i)
    | e' => .un op e'
  | .bin op e1 e2 =>
    match optimize e1, optimize e2 with
    | .const i, .const 0 =>
      if op = BinOp.minus then .const i
      else .bin op (.const i) (.const 0)
    | .const i, .const i' =>
      if let some v := op.apply i i' then .const v
      else .bin op (.const i) (.const i')
    | e1', e2' => .bin op e1' e2'

/--
Optimization doesn't change the meaning of any expression
-/
theorem optimize_ok (e : Expr) : e.eval σ = e.optimize.eval σ := by
  induction e <;> simp [optimize]
  case un op e ih =>
    split <;> simp [eval, *]
    cases op <;> simp [UnOp.apply, eval]
  case bin op e1 e2 ih1 ih2 =>
    split <;> simp [eval, *]
    cases op <;> simp [BinOp.apply, eval]
    split
    -- next heq => simp [eval, heq] -- another way to specifically name the hypothesis
    . simp [eval, *];
    . simp [eval, BinOp.apply];

/--
Optimization doesn't change the meaning of any expression
-/
theorem optimize_ok' (e : Expr) : e.eval σ = e.optimize.eval σ := by
  induction e using optimize.induct <;> simp [optimize, eval, *] <;> simp [BinOp.apply]
