/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Lean.Expr.Basic

/-!
#  Deprecation tool

Writing
```lean
deprecate to id₁ id₂ ... idₙ
theorem easy : True := .intro
```
where `id₁ id₂ ... idₙ` is a sequence of identifiers produces the `Try this` suggestion:
```lean
theorem easy : True := .intro
@[deprecated] alias d₁ := id₁
@[deprecated] alias d₂ := id₂
...
@[deprecated] alias dₙ := idₙ
```
where `d₁ d₂ ... dₙ` are the non-blacklisted declarations autogenerated by the initial command.

TODO:
* rename the old declarations with the new names
  (`easy` should become `id₁`);
* add a comment with today's date to the deprecations
  (e.g. `@[deprecated] alias d₁ := id₁ -- YYYY-MM-DD`);
* improve the formatting of the `Try this` suggestion
  (currently there are non-ideal indentations and line breaks).
-/

namespace Mathlib.Tactic.DeprecateMe

/-- Syntax for a sequence of commands. -/
syntax commandSeq := sepBy1IndentSemicolon(command)

open Lean Elab Term Command

/-- Produce the syntax for the command `@[deprecated] alias n := id`. -/
def mkDeprecationStx (id : TSyntax `ident) (n : Name) : CommandElabM (TSyntax `command) := do
  `(command| @[deprecated] alias $(mkIdent n) := $id)

/-- Returns the array of names that are in `new` but not in `old`. -/
def newNames (old new : Environment) : Array Name := Id.run do
  let mut diffs := #[]
  for (c, _) in new.constants.map₂.toList do
    unless old.constants.map₂.contains c do
      diffs := diffs.push c
  pure <| diffs

open Lean Elab Command Meta in
/--
Writing
```lean
deprecate to id₁ id₂ ... idₙ
theorem easy : True := .intro
```
where `id₁ id₂ ... idₙ` is a sequence of identifiers produces the `Try this` suggestion:
```lean
theorem easy : True := .intro
@[deprecated] alias d₁ := id₁
@[deprecated] alias d₂ := id₂
...
@[deprecated] alias dₙ := idₙ
```
where `d₁ d₂ ... dₙ` are the non-blacklisted declarations autogenerated by the initial command.
-/
elab "deprecate to" id:ident* ppLine cmd:command : command => do
  let oldEnv ← getEnv
  try
    elabCommand cmd
  finally
    let newEnv ← getEnv
    -- reversing the output of `allNew` heuristically orders declarations in a human-friendly way
    let allNew := (newNames oldEnv newEnv).reverse
    let skip ← allNew.filterM (·.isBlackListed)
    let news := allNew.filter (! · ∈ skip)
    let msg := match skip with
    | #[] => s!"* New constants:\n{news}"
    | _ => s!"* Using these new constants:\n{news}\n\n* Ignoring:\n{skip}"
    let stxs ← (id.zip news).mapM fun (id, n) => mkDeprecationStx id n
    let stxs := #[cmd] ++ stxs
    liftTermElabM do
    Std.Tactic.TryThis.addSuggestion (header := msg ++ "\n\nTry this:\n") (← getRef)
      (← `(commandSeq| $stxs*))

end Mathlib.Tactic.DeprecateMe
