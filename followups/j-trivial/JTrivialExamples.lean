import RestrictedDecision

open JTrivialFollowup

-- The singleton, the two-element chain, and an identity adjoined to a
-- two-element nilpotent semigroup are J-trivial.
example : checkJ [[0]] = true := by decide
example : checkJ [[0,1],[1,1]] = true := by decide
example : checkJ [[0,1,2],[1,2,2],[2,2,2]] = true := by decide

-- The two-element group and a two-element left-zero semigroup with
-- an adjoined identity each have a nonsingleton J-class.
example : checkJ [[0,1],[1,0]] = false := by decide
example : checkJ [[0,1,2],[1,1,1],[2,2,2]] = false := by decide
