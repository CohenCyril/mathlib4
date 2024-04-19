/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util
import Std.Data.List.Basic

/-!
#  The `have` vs `let` linter

The `have` vs `let` linter flags uses of `have` to introduce a hypothesis whose Type is not `Prop`.

TODO:
* Also lint `let` vs `have`.
* `haveI` may need to change to `let/letI`?
* `replace`, `classical!`, `classical`, `tauto` internally use `have`:
  should the linter act on them as well?
-/

open Lean Elab Command Meta

namespace Mathlib.Linter

/-- The `have` vs `let` linter emits a warning on `have`s introducing a hypothesis whose
Type is not `Prop` *if* the proof is incomplete. -/
register_option linter.haveLet : Bool := {
  defValue := true
  descr := "enable the `have` vs `let` linter"
}

namespace haveLet

/-- find the `have` syntax. -/
partial
def isHave? : Syntax → Bool
  | .node _ ``Lean.Parser.Tactic.tacticHave_ _ => true
  |_ => false

end haveLet

end Mathlib.Linter

namespace Mathlib.Linter.haveLet

/-- a monadic version of `Lean.Elab.InfoTree.foldInfo`.
Used to infer types inside a `CommandElabM`. -/
def InfoTree.foldInfoM {α m} [Monad m] (f : ContextInfo → Info → α → m α) (init : α) :
    InfoTree → m α :=
  InfoTree.foldInfo (fun ctx i ma => do f ctx i (← ma)) (pure init)

/-- given a `ContextInfo`, a `LocalContext` and an `Array` of `Expr`essions `es`,
`areProp_toFormat` creates a `MetaM` context, and returns an array of pairs consisting of
* a `Bool`ean, answering the question of whether the Type of `e` is a `Prop` or not, and
* the pretty-printed `Format` of `e`
for each `Expr`ession `e` in `es`.
Concretely, `areProp_toFormat` runs `inferType` in `CommandElabM`.
This is the kind of monadic lift that `nonPropHaves` uses to decide whether the Type of a `have`
is in `Prop` or not.
The output `Format` is just so that the linter displays a better message. -/
def areProp_toFormat (ctx : ContextInfo) (lc : LocalContext) (es : Array Expr) :
    CommandElabM (Array (Bool × Format)) := do
  ctx.runMetaM lc do
    es.mapM fun e => do
      let typ ← inferType (← instantiateMVars e)
      return (typ.isProp, ← ppExpr e)

/-- returns the `have` syntax whose corresponding hypothesis does not have Type `Prop` and
also a `Format`ted version of the corresponding Type. -/
partial
def nonPropHaves : InfoTree → CommandElabM (Array (Syntax × Format)) :=
  InfoTree.foldInfoM (init := #[]) fun ctx info args => return args ++ (← do
    let .ofTacticInfo i := info | return #[]
    let stx := i.stx
    let .original .. := stx.getHeadInfo | return #[]
    unless isHave? stx do return #[]
    let mctx := i.mctxAfter
    let mvdecls := (i.goalsAfter.map (mctx.decls.find? ·)).reduceOption
    let _ : Ord MetavarDecl := { compare := (compare ·.index ·.index) }
    -- we extract the `MetavarDecl` with largest index after a `have`, since this one
    -- holds information about the metavariable where `have` introduces the new hypothesis.
    let largestIdx := mvdecls.toArray.qsort (·.index > ·.index)
    -- the relevant `LocalContext`
    let lc := (largestIdx.getD 0 default).lctx
    -- we also accumulate all `fvarId`s from all local contexts before the use of `have`
    -- so that we can then isolate the `fvarId`s that are created by `have`
    let mvdeclsOld := (i.goalsBefore.map (mctx.decls.find? ·)).reduceOption
    let lctxOld := mvdeclsOld.map (·.lctx)
    let declsOld := (lctxOld.map (·.decls.toList.reduceOption)).join
    let fvAssOld := declsOld.map (·.fvarId)
    let oldDecls := lc.decls.toList.reduceOption.filter (! fvAssOld.contains ·.fvarId)
    -- now, we get the `MetaM` state up and running to find the types of each entry of `oldDecls`
    let fmts ← areProp_toFormat ctx lc (oldDecls.map (·.type)).toArray
    let (_propFmts, typeFmts) := (fmts.zip (oldDecls.map (·.userName)).toArray).partition (·.1.1)
    -- everything that is a Type triggers a warning on `have`
    return typeFmts.map fun ((_, fmt), na) => (stx, f!"{na} : {fmt}"))

/-- Gets the value of the `linter.haveLet` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.haveLet o

/-- The main implementation of the `have` vs `let` linter. -/
def haveLetLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterHash (← getOptions) && (← getInfoState).enabled do
    return
  unless (← MonadState.get).messages.isEmpty do
  let trees ← getInfoTrees
  for t in trees.toArray do
    for (s, fmt) in ← nonPropHaves t do
      Linter.logLint linter.haveLet s m!"'{fmt}' is a Type and not a Prop. \
        Consider using 'let' instead of 'have'."

initialize addLinter haveLetLinter
