/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Tactic.Do.Syntax
public import Std.Internal.Do
meta import Lean.Parser.Command
meta import Lean.Parser.Term
import Init.Syntax
import Init.Grind.Interactive

/-!
# `require`/`ensures` contracts on `def`

A definition carrying `require P` / `ensures b => Q` clauses expands to the plain definition plus a
`vcgen`-proven, `@[spec]`-tagged specification theorem `f.spec`.
-/

open Lean Lean.Parser.Command Lean.Order

namespace Std.Internal.Do

/-- The identifiers bound by an explicit `(…)` binder, used to apply the definition in its spec. -/
private meta def contractBinderIdents (binder : Syntax) : Array Ident :=
  match binder with
  | `(Lean.Parser.Term.bracketedBinderF| ($ids* $[: $_]?)) =>
      ids.filterMap fun b => if b.raw.isIdent then some ⟨b.raw⟩ else none
  | _ =>
      if binder.isIdent then #[⟨binder⟩] else #[]

/-- Expand a `def` carrying `require`/`ensures` clauses into the plain `def` plus a spec theorem
`@[spec] theorem f.spec : ⦃P⦄ f args ⦃(fun b => Q); ⊥⦄ := by vcgen [f] with finish`. -/
@[macro Lean.Parser.Command.declaration]
public meta def expandDefContract : Macro := fun stx => do
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
  -- The precondition is a plain proposition, embedded into the assertion type by `⌜ … ⌝` inline
  -- (a standalone `⌜ … ⌝` quotation would resolve the `⌜` token ambiguously against `Std.Do`).
  let preP : Term ← if requireStx.isNone then `(True) else
    match requireStx[0] with
    | `(requireClause| require $p) => pure p
    | _ => Macro.throwUnsupported
  let post : Term ← if ensuresStx.isNone then `(fun _ => True) else
    match ensuresStx[0] with
    | `(ensuresClause| ensures $bs* => $q) => `(fun $bs* => $q)
    | _ => Macro.throwUnsupported
  -- The `⦃ … ; ⊥ ⦄` form (explicit exceptional post) exists only for the new-metatheory triple, not
  -- the legacy `Std.Do` one, so it disambiguates the shared `⦃` token to the intended notation.
  let thm ← `(command|
    @[spec] theorem $specId $binders* : ⦃ ⌜$preP⌝ ⦄ $fId $args* ⦃ $post ; ⊥ ⦄ := by
      vcgen [$fId:ident] with finish)
  return mkNullNode #[cleanDeclaration, thm]

end Std.Internal.Do
