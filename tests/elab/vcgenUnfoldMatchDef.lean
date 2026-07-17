import Std.Tactic.Do
import Std.Internal.Do

/-!
Test for `vcgen [f]` where `f` is defined by a root `match` on its arguments. With an opaque
discriminant the constructor equations cannot rewrite the call, so the unfold theorem `f.eq_def`
rewrites it to the `match` expression and `vcgen` splits it, mirroring `simp`'s unfolding of
non-recursive definitions. The wildcard-row equation of an overlapping `match` must not be used
as a spec: it matches any call and would strand its overlap hypothesis as an unprovable
verification condition.
-/

set_option mvcgen.warning false

def dep (n : Option Nat) : Id Nat :=
  match n with | some y => pure (y + 1) | none => pure 2

/-- Overlapping wildcard row: its equation is guarded by an overlap hypothesis. -/
def wild (n m : Option Nat) : Id Nat :=
  match n, m with
  | some y, some z => pure (y + z + 1)
  | _, _ => pure 1

/-- Recursive: no `eq_def` fallback, so an opaque discriminant still reports a missing spec
instead of unfolding indefinitely. -/
def recf (n : Nat) : Id Nat :=
  match n with | 0 => pure 1 | n + 1 => recf n

section
open Lean.Order Std.Internal.Do

example (n : Option Nat) : ⦃ True ⦄ dep n ⦃ fun r => r > 0 ⦄ := by
  vcgen [dep] with finish

-- A concrete discriminant is rewritten by the constructor equation directly.
example : ⦃ True ⦄ dep (some 5) ⦃ fun r => r = 6 ⦄ := by
  vcgen [dep] with finish

example (n m : Option Nat) : ⦃ True ⦄ wild n m ⦃ fun r => r > 0 ⦄ := by
  vcgen [wild] with finish

-- The global attribute goes through the same registration.
attribute [local spec] wild in
example (n m : Option Nat) : ⦃ True ⦄ wild n m ⦃ fun r => r > 0 ⦄ := by
  vcgen with finish

/--
error: Failed to apply rule SpecProof.global recf.eq_2 for
  recf n
target:
  ⊤ ⊑ wp (recf n) (LT.lt 0) ⊥
Pred:
  Prop
excessArgs: []
rule type:
  ∀ (Pre : Prop) (n_2 : Nat) (Q : Nat → Prop) (E : EPost⟨⟩), Pre ⊑ wp (recf n_2) Q E → Pre ⊑ wp (recf n_2.succ) Q E
-/
#guard_msgs (whitespace := lax) in
example (n : Nat) : ⦃ True ⦄ recf n ⦃ fun r => r > 0 ⦄ := by
  vcgen [recf] with finish

end
