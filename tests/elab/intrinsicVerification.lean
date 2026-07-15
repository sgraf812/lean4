import Std.Internal.Do
import Std.Tactic.Do

/-! Tests for intrinsic verification syntax on `Std.Internal.Do` do-notation: the `for … invariant …`
loop clause and `require`/`ensures` `def` contracts. A `def` carrying contracts elaborates to the
definition plus an `@[spec]`-tagged `f.spec` Hoare-triple theorem proved by `vcgen … with finish`,
which end-to-end also exercises the `for … invariant` gadget. New cases go here. -/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false

/-! ## `for … invariant`, `ensures`: fully automatic, zero manual proof (corpus `findSmallest`) -/

def findSmallest (s : Array Nat) : Id (Option Nat)
    ensures r => match r with
      | none     => s.size = 0
      | some min => s.size > 0 ∧ (∃ i, i < s.size ∧ s[i]! = min)
                                ∧ (∀ j, j < s.size → min ≤ s[j]!)
  := do
  if s.size = 0 then
    return none
  else
    let mut minIndex := 0
    for i in [1:s.size]
        invariant xs => minIndex < s.size ∧ s[minIndex]! ≤ s[0]! ∧
                        ∀ j, j ∈ xs.prefix → s[minIndex]! ≤ s[j]!
      do
      if s[i]! < s[minIndex]! then
        minIndex := i
    return some s[minIndex]!

-- The contract synthesizes an `@[spec]`-tagged `findSmallest.spec` Hoare triple.
#guard_msgs (drop info) in
#check @findSmallest.spec

/-! ## `require` + `ensures` -/

def clampLow (n lo : Nat) : Id Nat
    require lo ≤ n
    ensures r => r = n
  := do return n

#guard_msgs (drop info) in
#check @clampLow.spec

/-! ## Nested loops: the inner `invariant` names the outer loop variable `i` by lexical scope -/

@[local grind] def isMajorityElement (lst : List Int) (x : Int) : Prop :=
  2 * (lst.count x) > lst.length

def findMajorityElement (lst : List Int) : Id Int := do
  let mut found := false
  let mut candidate : Int := -1
  for i in [0:lst.length]
      invariant xs =>
        (found = true  → candidate ∈ lst ∧ isMajorityElement lst candidate) ∧
        (found = false → ∀ k, k < xs.prefix.length → ¬isMajorityElement lst lst[k]!)
    do
    let elem := lst[i]!
    let mut count := 0
    for j in [0:lst.length]
        invariant ys => count = (lst.take ys.prefix.length).count lst[i]!
      do
      if lst[j]! = elem then
        count := count + 1
    if count > lst.length / 2 then
      found := true
      candidate := elem
  if found then return candidate else return -1
