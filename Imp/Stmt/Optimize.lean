import Imp.Expr
import Imp.Stmt.Basic
import Imp.Stmt.Delab

namespace Imp.Stmt

/-- Optimize a statement -/
def optimize : Stmt → Stmt
  | imp {skip;} => imp {skip;} -- this is a macro that is going to expand into Statement.skip
                               -- valid to put in this position
  | imp {~s1 ~s2} =>
    match s1.optimize, s2.optimize with
    | imp {skip;}, s2' => s2'
    | s1', imp {skip;} => s1'
    | s1', s2' => imp {~s1' ~s2'}
  | imp {if (~c) {~s1} else {~s2}} =>
    let c' := c.optimize
    match c' with
    | .const 0 => s2.optimize
    | .const _ => s1.optimize
    | _ =>
      let s1' := s1.optimize
      let s2' := s2.optimize
      if s1' = s2' then
        s1'
      else imp {if (~c') {~s1.optimize} else {~s2.optimize}}
  | imp {while (~c) {~s}} =>
    let c' := c.optimize
    match c' with
    | .const 0 => imp {skip;}
    | _ => imp {while (~c') {~s.optimize}}
  | imp {~x := ~e;} =>
    imp {~x := ~e.optimize;}
