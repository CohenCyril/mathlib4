/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Tactic.Linter.OldObtain

/-! Tests for the `oldObtain` linter. -/

-- These cases are fine.
theorem foo : True := by
  obtain := trivial
  obtain _h := trivial
  obtain : True := trivial
  obtain _h : True := trivial
  trivial

-- These cases are linted against.

set_option linter.oldObtain false in
/--
warning: Please remove stream-of-conciousness `obtain` syntax
note: this linter can be disabled with `set_option linter.oldObtain false`
-/
#guard_msgs in
set_option linter.oldObtain true in
theorem foo' : True := by
  obtain : True
  · trivial
  trivial

set_option linter.oldObtain false in
/--
warning: Please remove stream-of-conciousness `obtain` syntax
note: this linter can be disabled with `set_option linter.oldObtain false`
-/
#guard_msgs in
set_option linter.oldObtain true in
theorem foo'' : True := by
  obtain h : True
  · trivial
  trivial

-- Analogous tests for the `rsuffices` tactic.
-- These cases are fine.
theorem bar : 2 + 2 = 4 := by
  rsuffices := trivial
  rsuffices _h := trivial
  rsuffices : True := trivial
  rsuffices _h : True := trivial
  exact rfl

-- These are linted against.

set_option linter.oldObtain false in
/--
warning: Please remove stream-of-conciousness `rsuffices` syntax
note: this linter can be disabled with `set_option linter.oldObtain false`
-/
#guard_msgs in
set_option linter.oldObtain true in
theorem bar' : 2 + 2 = 4 := by
  rsuffices : True
  · trivial
  sorry

set_option linter.oldObtain false in
/--
warning: Please remove stream-of-conciousness `rsuffices` syntax
note: this linter can be disabled with `set_option linter.oldObtain false`
-/
#guard_msgs in
set_option linter.oldObtain true in
theorem bar'' : 2 + 2 = 4 := by
  rsuffices h : True
  · trivial
  sorry
