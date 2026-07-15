/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.Triple.SpecLemmas
import Init.Data.Array.Bootstrap
import Init.Data.List.Monadic

/-!
# `forIn` loop-invariant gadget

`ForIn.forInWithInvariant` annotates a `forIn` loop with its invariant so that `vcgen` reads the
invariant from the program. The `@[spec]` specifications restate `Spec.forIn_list` for the
container in question.
-/

@[expose] public section

namespace Std.Internal.Do

open Lean.Order

universe u₁ u₂ v w
variable {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
  {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
variable [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

private theorem foldl_push_toList {γ : Type u₁} (xs : List γ) (acc : Array γ) :
    (xs.foldl (fun acc a => acc.push a) acc).toList = acc.toList ++ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih => rw [List.foldl_cons, ih, Array.toList_push]; simp

@[simp, grind =] theorem ForIn.toList_list {γ : Type u₁} (xs : List γ) : ForIn.toList xs = xs := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, List.forIn_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a) #[] xs).toList = xs
  rw [foldl_push_toList]; simp

@[simp, grind =] theorem ForIn.toList_range (r : Std.Legacy.Range) : ForIn.toList r = r.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a) #[]
    (List.range' r.start r.size r.step)).toList = r.toList
  rw [foldl_push_toList]; simp [Std.Legacy.Range.toList, Std.Legacy.Range.size]

set_option linter.unusedVariables false in
/-- A `forIn` loop annotated with its loop invariant, which `vcgen` reads from the `inv` argument.
It is definitionally `forIn xs init f`, so the annotation is erased at runtime. The invariant
ranges over the loop's iteration cursor, viewed through `ForIn.toList`. -/
@[inline] def ForIn.forInWithInvariant {ρ : Type w} [ForIn m ρ α] [ForIn Id ρ α] (xs : ρ) (init : β)
    (f : α → β → m (ForInStep β)) (inv : Invariant (ForIn.toList xs) β Pred) : m β :=
  forIn xs init f

@[spec]
theorem Spec.forInWithInvariant_list
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant (ForIn.toList xs) β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (h : ForIn.toList xs = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv ⟨pref, cur::suff, h.symm⟩ b)
        (fun r => match r with
          | .yield b' => inv ⟨pref ++ [cur], suff, by simp [h]⟩ b'
          | .done b' => inv ⟨ForIn.toList xs, [], by simp⟩ b')
        epost) :
    Triple
      (ForIn.forInWithInvariant xs init f inv)
      (inv ⟨[], ForIn.toList xs, rfl⟩ init)
      (fun b => inv ⟨ForIn.toList xs, [], by simp⟩ b)
      epost := by
  unfold ForIn.forInWithInvariant
  rw [show (forIn xs init f : m β) = forIn (ForIn.toList xs) init f by rw [ForIn.toList_list]]
  exact Spec.forIn_list inv step

@[spec]
theorem Spec.forInWithInvariant_range {β : Type u} {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {xs : Std.Legacy.Range} {init : β} {f : Nat → β → m (ForInStep β)}
    (inv : Invariant (ForIn.toList xs) β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (h : ForIn.toList xs = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv ⟨pref, cur::suff, h.symm⟩ b)
        (fun r => match r with
          | .yield b' => inv ⟨pref ++ [cur], suff, by simp [h]⟩ b'
          | .done b' => inv ⟨ForIn.toList xs, [], by simp⟩ b')
        epost) :
    Triple
      (ForIn.forInWithInvariant xs init f inv)
      (inv ⟨[], ForIn.toList xs, rfl⟩ init)
      (fun b => inv ⟨ForIn.toList xs, [], by simp⟩ b)
      epost := by
  unfold ForIn.forInWithInvariant
  rw [show (forIn xs init f : m β) = forIn (ForIn.toList xs) init f by
    rw [ForIn.toList_range]
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.toList, Std.Legacy.Range.size]]
  exact Spec.forIn_list inv step

end Std.Internal.Do
