/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Kyle Miller, Damiano Testa
-/
import Lean.Elab.Tactic.ElabTerm
import Lean.Meta.Tactic.Cleanup
import Lean.PrettyPrinter
import Batteries.Lean.Meta.Inaccessible

/-!
#  `extract_goal`: Format the current goal as a stand-alone example

Useful for testing tactics or creating
[minimal working examples](https://leanprover-community.github.io/mwe.html).

```lean
example (i j k : Nat) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k := by
  extract_goal

/-
theorem extracted_1 (i j k : Nat) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k := sorry
-/
```

* TODO: Add tactic code actions?
* Output may produce lines with more than 100 characters

### Caveat

Tl;dr: sometimes, using `set_option [your pp option] in extract_goal` may work where `extract_goal`
does not.

The extracted goal may depend on imports and `pp` options, since it relies on delaboration.
For this reason, the extracted goal may not be equivalent to the given goal.
However, the tactic responds to pretty printing options.
For example, calling `set_option pp.all true in extract_goal` in the examples below actually works.

```lean
-- `theorem int_eq_nat` is the output of the `extract_goal` from the example below
-- the type ascription is removed and the `↑` is replaced by `Int.ofNat`:
-- Lean infers the correct (false) statement
theorem int_eq_nat {z : Int} : ∃ n, Int.ofNat n = z := sorry

example {z : Int} : ∃ n : Nat, ↑n = z := by
  extract_goal  -- produces `int_eq_nat`
  apply int_eq_nat  -- works
```

However, importing `Batteries.Classes.Cast`, makes `extract_goal` produce a different theorem

```lean
import Batteries.Classes.Cast

-- `theorem extracted_1` is the output of the `extract_goal` from the example below
-- the type ascription is erased and the `↑` is untouched:
-- Lean infers a different statement, since it fills in `↑` with `id` and uses `n : Int`
theorem extracted_1 {z : Int} : ∃ n, ↑n = z := ⟨_, rfl⟩

example {z : Int} : ∃ n : Nat, ↑n = z := by
  extract_goal
  apply extracted_1
/-
tactic 'apply' failed, failed to unify
  ∃ n, n = ?z
with
  ∃ n, ↑n = z
z: Int
⊢ ∃ n, ↑n = z
-/
```

Similarly, the extracted goal may fail to type-check:
```lean
example (a : α) : ∃ f : α → α, f a = a := by
  extract_goal
  exact ⟨id, rfl⟩

theorem extracted_1.{u_1} {α : Sort u_1} (a : α) : ∃ f, f a = a := sorry
-- `f` is uninterpreted: `⊢ ∃ f, sorryAx α true = a`
```
and also
```lean
import Mathlib.Algebra.Polynomial.Basic

--  The `extract_goal` below produces this statement:
theorem extracted_1 : X = X := sorry
-- Yet, Lean is unable to figure out what is the coefficients Semiring for `X`
/-
typeclass instance problem is stuck, it is often due to metavariables
  Semiring ?m.28495
-/

example : (X : Nat[X]) = X := by
  extract_goal
```
-/

namespace Mathlib.Tactic.ExtractGoal

open Lean Elab Tactic Meta

/-- Have `extract_goal` extract the full local context. -/
syntax star := "*"

/-- Configuration for `extract_goal` for which variables from the context to include. -/
syntax config := star <|> (colGt ppSpace ident)*

/--
- `extract_goal` formats the current goal as a stand-alone theorem or definition after
  cleaning up the local context of irrelevant variables.
  A variable is *relevant* if (1) it occurs in the target type, (2) there is a relevant variable
  that depends on it, or (3) the type of the variable is a proposition that depends on a
  relevant variable.

  If the target is `False`, then for convenience `extract_goal` includes all variables.
- `extract_goal *` formats the current goal without cleaning up the local context.
- `extract_goal a b c ...` formats the current goal after removing everything that the given
  variables `a`, `b`, `c`, ... do not depend on.
- `extract_goal ... using name` uses the name `name` for the theorem or definition rather than
  the autogenerated name.

The tactic tries to produce an output that can be copy-pasted and just work,
but its success depends on whether the expressions are amenable
to being unambiguously pretty printed.

The tactic responds to pretty printing options.
For example, `set_option pp.all true in extract_goal` gives the `pp.all` form.
-/
syntax (name := extractGoal) "extract_goal" config (" using " ident)? : tactic

elab_rules : tactic
    let name ← if let some name := name?
                then pure name.getId
                else mkAuxName ((← getCurrNamespace) ++ `extracted) 1
    let msg ← withoutModifyingEnv <| withoutModifyingState do
      let g ← getMainGoal
      let g ← do match cfg with
        | `(config| *) => pure g
        | `(config| ) =>
          if (← g.getType >>= instantiateMVars).consumeMData.isConstOf ``False then
            -- In a contradiction proof, it is not very helpful to clear all hypotheses!
            pure g
          else
            g.cleanup
          -- Note: `getFVarIds` does `withMainContext`
          g.cleanup (toPreserve := (← getFVarIds fvars)) (indirectProps := false)
        | _ => throwUnsupportedSyntax
      let (g, _) ← g.renameInaccessibleFVars
      let (_, g) ← g.revert (clearAuxDeclsInsteadOfRevert := true) (← g.getDecl).lctx.getFVarIds
      let ty ← instantiateMVars (← g.getType)
      if ty.hasExprMVar then
        -- TODO: turn metavariables into new hypotheses?
        throwError "Extracted goal has metavariables: {ty}"
      let ty ← Term.levelMVarToParam ty
      let seenLevels := collectLevelParams {} ty
      let levels := (← Term.getLevelNames).filter
                      fun u => seenLevels.visitedLevel.contains (.param u)
      addAndCompile <| Declaration.axiomDecl
        { name := name
          levelParams := levels
          isUnsafe := false
          type := ty }
      let sig ← addMessageContext <| MessageData.signature name
      let cmd := if ← Meta.isProp ty then "theorem" else "def"
      pure m!"{cmd} {sig} := sorry"
    logInfo msg
