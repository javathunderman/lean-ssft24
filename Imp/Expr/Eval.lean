import Imp.Expr.Basic
import Imp.Expr.Syntax

open Lean

namespace Imp

/-- Values stored in memory - 32-bit integers -/
abbrev Value := BitVec 32

/-- An environment maps variables names to their values (no pointers) -/
def Env := String → Value

namespace Env

/-- Set a value in an environment -/
def set (x : String) (v : Value) (σ : Env) : Env :=
  fun y => if x == y then v else σ y

/-- Look up a value in an environment -/
def get (x : String) (σ : Env) : Value :=
  σ x

/-- Initialize an environment, setting all uninitialized memory to `i` -/
def init (i : Value) : Env := fun _ => i

@[simp]
theorem get_init : (Env.init v).get x = v := by
  simp [Env.init, Env.get]
  -- constant function applied to a string, reduces to the value we wanted, we're done
  -- these proofs are trivial because simplification handles the whole thing (and thus are not that useful)

@[simp]
theorem get_set_same {σ : Env} : (σ.set x v).get x = v := by
  -- simp [get, set]
  simp [Env.init, Env.get, Env.set]

@[simp] -- why does this exist here?
-- when using this later on, this tells the prover to rewrite similar expressions based on this proof
-- to make it more concise?
theorem get_set_different {σ : Env} : x ≠ y → (σ.set x v).get y = σ.get y := by
  intro h -- introduce the hypothesis that h != y
  simp [Env.get, Env.set, *]

end Env

namespace Expr

/-- Helper that implements unary operators -/
def UnOp.apply : UnOp → Value → Option Value
  | .neg, x => some (- x)
  | .not, x => some (if x == 0 then 1 else 0)

/-- Helper that implements binary operators -/
def BinOp.apply : BinOp → Value → Value → Option Value
  | .plus, x, y => some (x + y)
  | .minus, x, y => some (x - y)
  | .times, x, y => some (x * y)
  | .lsh, x, y => some (x <<< y)
  | .rsh, x, y => some (x >>> y)
  | .band, x, y => some (x &&& y)
  | .bor, x, y => some (x ||| y)
  | .div, x, y => if y == 0 then none else some (x / y)
  | .and, x, y => some (if x == 0 then 0 else y)
  | .or, x, y => some (if x == 0 then y else x)
  | .eq, x, y => some (if x == y then 1 else 0)
  | .le, x, y => some (if x ≤ y then 1 else 0)
  | .lt, x, y => some (if x < y then 1 else 0)
  | .xor, x, y => some (x ^^^ y)

/--
Evaluates an expression, finding the value if it has one.

Expressions that divide by zero don't have values - the result is undefined.
-/
def eval (σ : Env) : Expr → Option Value
  | .const i => some i
  | .var x => σ.get x
  | .un op e => do
    let v ← e.eval σ -- sigma
    op.apply v
  | .bin op e1 e2 => do
    let v1 ← e1.eval σ
    let v2 ← e2.eval σ
    op.apply v1 v2

#eval (expr {19 + x / 3}).eval (Env.init 17)
#eval (expr {x ^^^ 2}).eval (Env.init 3)
