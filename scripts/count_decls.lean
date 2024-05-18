/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Damiano Testa
-/
import Mathlib --.Data.Nat.Defs

/-!
# `count_decls` -- a tally of declarations in `Mathlib`

This file is used by the `Periodic reports` script to generate a tally of declarations
in `Mathlib`, `Batteries` and core.

Source: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Metamathematics.3A.20Theorems.20by.20Domain.20Areas/near/374090639
-/

namespace PeriodicReports
open Lean Elab Meta

/-- A structure to tally declaration types:
* `thms` are theorems;
* `preds` are predicates;
* `types` are types;
* `data` is everything else.
-/
structure Tally where
  thms : Nat := 0
  preds : Nat := 0
  types : Nat := 0
  data : Nat := 0
  deriving Repr

structure TallyNames where
  thms  : HashSet Name := {}
  preds : HashSet Name := {}
  types : HashSet Name := {}
  data  : HashSet Name := {}

/-- `MathlibModIdxs env` returns the `ModuleIdx`s corresponding to `Mathlib` files
that are in the provided environment. -/
def MathlibModIdxs (env : Environment) : IO (HashSet Nat) := do
  let mut modIdx : HashSet Nat := .empty
  for imp in ← IO.FS.lines "Mathlib.lean" do
    if let some nm := env.getModuleIdx? (imp.drop 7).toName then
      modIdx := modIdx.insert nm
  return modIdx

variable (mods : HashSet Nat) (env : Environment) in
/-- Extend a `Tally` by the ConstantInfo `c`.  It is written to work with `Lean.SMap.foldM`. -/
def updateTallyNames (s : TallyNames) (n : Name) (c : ConstantInfo) :
    MetaM TallyNames := do
--  let mod := env.getModuleIdxFor? n
--  if !mods.contains (mod.getD default) then return s else
  if c.isUnsafe || (← n.isBlackListed) then return s else
  let typ := c.type
  if (← isProp typ) then
    return {s with thms := s.thms.insert  n}
  else
    let exp ← forallTelescopeReducing typ fun _ e => return e
    if exp.isType then
      return {s with types := s.types.insert n}
    else
    if exp.isSort then
      return {s with preds := s.preds.insert n}
    else
      return {s with data := s.data.insert n}

/-- extends a `Tally` all the ConstantInfos in the environment. -/
def mkTallyNames (s : TallyNames) : MetaM TallyNames := do
  let env ← getEnv
--  let maths ← MathlibModIdxs env
  let consts := env.constants
  consts.foldM (updateTallyNames /-maths env-/) s

/-- `count_decls` prints a tally of theorems, types, predicates and data in
`Mathlib`, `Batteries` and core. -/
elab "count_decls" : command => do
  let (s, _) ← Command.liftCoreM do Meta.MetaM.run do (mkTallyNames {})
  logInfo s!"Theorems\n{s.thms.toArray}\nData\n{s.data.toArray}\nPredicates\n{s.preds.toArray}\nTypes\n{s.types.toArray}"
  logInfo m!"{s.types.toArray}"
--  logInfo s!"Theorems {s.thms}\nData {s.data}\nPredicates {s.preds}\nTypes {s.types}"

count_decls

end PeriodicReports