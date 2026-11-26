import Problem455TableValidate
import Problem455MathlibTM
import Problem455FoldWorld

/- Finite regressions for representation and boundary conventions. -/
open P455TableValidate P455MathlibCode P455FoldWorld Turing
example : valid []=false := by decide
example : valid [[0,1],[1,0]]=true := by decide
example : valid [[0,1],[0,1]]=false := by decide
example : safe [[7]]=[[0]] := by decide
example : safe [[0,1],[1,1]]=[[0,1],[1,1]] := by decide
example : [wire [], wire [false], wire [true], wire [false,false], wire [false,true]] = [1,2,3,4,5] := by decide
example : coord false 0=0 ∧ coord true 0=1 ∧ coord false 1 = -1 ∧ coord true 1=2 := by decide
example : (motion false true Dir.right).1=true ∧ (motion true true Dir.left).1=false := by decide
#eval (valid [[0,1],[1,0]],safe [[7]], wire [false,true])
