/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Tactic.Do.Syntax
public import Std.Internal.Do
public import Lean.Elab.Util
import Lean.DocString.Extension
meta import Lean.Parser.Command
meta import Lean.Parser.Term
import Init.Syntax
import Init.Grind.Interactive

/-!
# `require`/`ensures` contracts on `def`

A definition carrying `require P` / `ensures b => Q` clauses expands to the plain definition plus a
`vcgen`-proven, `@[spec]`-tagged specification theorem `f.spec`.
-/

public section

open Lean Lean.Parser.Command Std.Internal.Do

namespace Lean.Elab.Tactic.Do

/-- The identifiers bound by an explicit `(…)` binder, used to apply the definition in its spec. -/
def contractBinderIdents (binder : Syntax) : Array Ident :=
  match binder with
  | `(Lean.Parser.Term.bracketedBinderF| ($ids* $[: $_]?)) =>
      ids.filterMap fun b => if b.raw.isIdent then some ⟨b.raw⟩ else none
  | _ =>
      if binder.isIdent then #[⟨binder⟩] else #[]

/-- Expand a `def` carrying `require`/`ensures` clauses into the plain `def` plus a spec theorem
`@[spec] theorem f.spec : ⦃P⦄ f args ⦃fun b => Q⦄ := by vcgen [f] with finish`. -/
@[builtin_macro Lean.Parser.Command.declaration]
def expandDefContract : Macro := fun stx => do
  let decl := stx[1]
  unless decl.isOfKind ``Lean.Parser.Command.definition do Macro.throwUnsupported
  -- `optDeclSig = binders(0) >> optType(1) >> optional requireClause(2) >> optional ensuresClause(3)`
  let sig := decl[2]
  let requireStx := sig[2]
  let ensuresStx := sig[3]
  if requireStx.isNone && ensuresStx.isNone then
    Macro.throwUnsupported
  -- Strip the contract clauses so the remaining `def` elaborates normally.
  let cleanSig := (sig.setArg 2 mkNullNode).setArg 3 mkNullNode
  let cleanDeclaration := stx.setArg 1 (decl.setArg 2 cleanSig)
  let fId : Ident := ⟨decl[1][0]⟩
  let specId := mkIdentFrom fId (fId.getId ++ `spec)
  let binders : TSyntaxArray [`ident, ``Lean.Parser.Term.hole, ``Lean.Parser.Term.bracketedBinder] :=
    sig[0].getArgs.map (⟨·⟩)
  let args := sig[0].getArgs.flatMap contractBinderIdents
  let pre : Term ← if requireStx.isNone then `(True) else
    match requireStx[0] with
    | `(requireClause| require $p) => pure p
    | _ => Macro.throwUnsupported
  let post : Term ← if ensuresStx.isNone then `(fun _ => True) else
    match ensuresStx[0] with
    | `(ensuresClause| ensures $bs* => $q) => `(fun $bs* => $q)
    | _ => Macro.throwUnsupported
  let thm ← `(command|
    @[spec] theorem $specId $binders* : ⦃ $pre ⦄ $fId $args* ⦃ $post ⦄ := by
      vcgen [$fId:ident] with finish)
  return mkNullNode #[cleanDeclaration, thm]

end Lean.Elab.Tactic.Do
