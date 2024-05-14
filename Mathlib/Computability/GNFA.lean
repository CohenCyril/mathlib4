/-
Copyright (c) 2022 Russell Emerine, 2024 Tom Kranz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Russell Emerine, Tom Kranz
-/
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.FinEnum.Option

#align_import computability.GNFA

/-!
# Generalized Nondeterministic Finite Automata

This file contains the definition of a Generalized Nondeterministic Finite Automaton, a state
machine which determines whether a string (implemented as a `List` over an arbitrary alphabet) is in
a regular set by evaluating the string over its net of regular expressions. We show
that GNFA's are equivalent to `NFA`'s, and that GNFA's are equivalent to smaller GNFA's with a state
"ripped" out. Through this mechanism, we show that `NFA`'s are equivalent to `RegularExpression`s.

## References

TODO: someone please tell me how to best cite this file?
* <https://courses.engr.illinois.edu/cs373/sp2013/Lectures/lec07.pdf>
-/


universe u v

/-- A GNFA is a set of `|σ| + 2` states and a transition function between two states. The transition
function takes the starting state (represented by `Option.none` in the first argument) or any
internal state (consistently represented by `Option.some`s) as the first state, and the accepting
state (represented by `Option.none` in the second argument) or any internal state as the second
state. There is a transition between *all* of these
combinations, in the form of a `RegularExpression`. When following a transition, some matching
prefix of the input string is taken. What would be a missing transition in ordinary automata can be
achieved by yielding a `RegularExpression` matching `∅`; canonically
`RegularExpression.zero`.
-/
-- Porting note: removed Fintype instance for σ as an argument
structure GNFA (α : Type u) (σ : Type v) where
  /-- Yields the regular expression (sub)strings have to match to transition from the first to the
  second argument state. `Option.none` in the first position signifies a transition originating in
  the start state, `Option.none` in the second position signifies a transition targetting the
  accept state. -/
  step : Option σ → Option σ → RegularExpression α

variable {α : Type u} {σ : Type v}

namespace GNFA

/-- The GNFA admitting only impassable transitions (and be it only from start to accept state)
will always be available. -/
instance : Inhabited (GNFA α σ) :=
  ⟨GNFA.mk fun _ _ ↦ 0⟩

/-- A `trace` of an internal state and a string of a GNFA represents the possibility of getting to
the state via transitions that match the elements of some partitioning of the string.
This can be interpreted as the `Set` of strings that reach a certain inner state;
i.e. its `Language`.
-/
inductive trace (M : GNFA α σ) : σ → Language α
  | start : ∀ {x} q, x ∈ (M.step none (some q)).matches' → M.trace q x
  | step : ∀ {x y z} p q,
    y ∈ M.trace p → z ∈ (M.step (some p) (some q)).matches' → x = y ++ z → M.trace q x

/--
An `accepts` of a string represents the possibility of getting to the accepting state of a GNFA via
transitions of the GNFA that match the elements of some partitioning of the string.
Since this is the definition of when a GNFA accepts
a string, this also is how the accepting language of a GNFA is described.
-/
inductive accepts (M : GNFA α σ) : Language α
  | start : ∀ {x}, x ∈ (M.step none none).matches' → M.accepts x
  | step : ∀ {x y z} q,
    y ∈ M.trace q → z ∈ (M.step (some q) none).matches' → x = y ++ z → M.accepts x

/-- "Rips" an internal state out of a GNFA, making it smaller by one without changing its accepting
language.

The idea is to patch the transitions between all the remaining pairs of states with an alternative
`RegularExpression` that describes all the words that could've passed from the source to the target
state via the ripped state.
The `RegularExpression.star` accounts for words requiring looping transitions on the ripped state.

This is implemented as always ripping the designated inner state `Option.none` from a state space
that is already an `Option` over the state space of the result GNFA.
-/
def rip (M : GNFA α (Option σ)) : GNFA α σ :=
  ⟨fun p q ↦
    -- if start state is queried, don't layer on another some
    let p := p.map some
    -- if accept state is queried, don't layer on another some
    let q := q.map some
    -- the ripped state is always the none element in the original state space
    let r : Option (Option σ) := some none
    M.step p q + M.step p r * (M.step r r).star * M.step r q⟩

/-- Given a GNFA that's about to have a state `rip`ped, any word that reaches any internal state
will also reach that state after ripping if the state was not the ripped one.
Otherwise, the string can be partitioned into three substrings:
One that reaches some other state, one that could've moved on to the ripped state
before ripping and one that could've travelled arbitrarily many loops on the ripped state.
-/
lemma rip_trace_aux (M : GNFA α (Option σ)) {w q} (hwt : w ∈ M.trace q) :
    (∃ p, q = some p ∧ w ∈ M.rip.trace p) ∨
    q = none ∧ ∃ (y z : _) (ws : List (List α)) (p : Option σ),
    (p.map (y ∈ M.rip.trace ·)).getD (y = []) ∧
    z ∈ (M.step (p.map some) (some none)).matches' ∧
    (∀ w ∈ ws, w ∈ (M.step (some none) (some none)).matches') ∧
    w = y ++ z ++ ws.join := by
  refine hwt.recOn ?_ ?_
  · rintro x (⟨⟩ | q) mat
    · exact .inr ⟨rfl, [], x, [], none, rfl, mat, List.forall_mem_nil _, by simp⟩
    · exact .inl ⟨q, rfl, trace.start q (.inl mat)⟩
  · rintro _ y z (⟨⟩ | p) (⟨⟩ | q) hyt mat rfl ih
    · rcases ih with ⟨_, ⟨⟩, _⟩ | ⟨_, y, z', xs, p, hyt', mat', loop, rfl⟩
      refine .inr ⟨rfl, y, z', xs ++ [z], p, hyt', mat', ?_, by simp⟩
      rw [xs.forall_mem_append, List.forall_mem_singleton]
      exact ⟨loop, mat⟩
    · refine .inl ⟨q, rfl, ?_⟩
      rcases ih with ⟨_, ⟨⟩, _⟩ | ⟨_, y, z', xs, ⟨⟩ | p, hyt', mat', loop, rfl⟩
      · simp at hyt; subst y
        refine trace.start q <| .inr ?_
        simp only [List.nil_append, List.append_assoc, Option.map_none', Option.map_some',
          RegularExpression.matches'_mul, RegularExpression.matches'_star]
        rw [← List.append_assoc]
        exact ⟨z' ++ xs.join, ⟨z', mat', xs.join, ⟨xs, rfl, loop⟩, rfl⟩, z, mat, rfl⟩
      · simp only [List.append_assoc]
        refine trace.step _ q hyt' (.inr ?_) rfl
        rw [← List.append_assoc]
        exact ⟨z' ++ xs.join, ⟨z', mat', xs.join, ⟨xs, rfl, loop⟩, rfl⟩, z, mat, rfl⟩
    · rcases ih with ⟨p', ⟨rfl⟩, hyt'⟩ | ⟨⟨⟩, _⟩
      exact .inr ⟨rfl, y, z, [], some p, hyt', mat, List.forall_mem_nil _, by simp⟩
    · rcases ih with ⟨p', ⟨rfl⟩, hyt'⟩ | ⟨⟨⟩, _⟩
      exact .inl ⟨q, rfl, trace.step p q hyt' (.inl mat) rfl⟩

/-- Ripping a state preserves the languages of all the remaining internal states. -/
theorem rip_trace_correct (M : GNFA α (Option σ)) {q : σ} :
    M.trace (some q) = M.rip.trace q := by
  ext
  constructor
  · intro hxt
    rcases M.rip_trace_aux hxt with ⟨_, ⟨rfl⟩, hxt'⟩ | ⟨⟨⟩, _⟩
    exact hxt'
  · intro hxt'
    refine hxt'.recOn ?_ ?_
    · rintro x q (hx | ⟨y, hy, z, hz, rfl⟩)
      · exact trace.start (some q) hx
      refine trace.step none (some q) ?_ hz rfl
      rcases hy with ⟨y, hy, z, ⟨xs, rfl, hxs⟩, rfl⟩
      induction xs using List.reverseRecOn
      · simp; exact trace.start none hy
      rename_i xs x ih
      rw [List.join_append, List.join_singleton]
      simp only [← List.append_assoc]
      refine trace.step none none (ih ?_) (hxs x (by simp)) rfl
      intro y mem
      exact hxs y (by simp[mem])
    · rintro x y z p q _ (hz | ⟨w, hw, x, hx, rfl⟩) rfl ih
      · exact trace.step (some p) (some q) ih hz rfl
      rw [← List.append_assoc]
      refine trace.step none (some q) ?_ hx rfl
      rcases hw with ⟨w, hw, x, hx, rfl⟩
      rw [← List.append_assoc]
      rcases hx with ⟨xs, rfl, loop⟩
      induction xs using List.reverseRecOn
      · exact trace.step (some p) none ih hw (by simp)
      rename_i xs x ih
      rw [List.join_append, List.join_singleton, ← List.append_assoc]
      refine trace.step none none (ih ?_) (loop x (by simp)) rfl
      intro y mem
      exact loop y (by simp[mem])

/-- Ripping a state preserves the language of a GNFA. -/
-- TODO: maybe mark as @simp
theorem rip_correct (M : GNFA α (Option σ)) : M.rip.accepts = M.accepts := by
  ext w
  constructor
  · rintro (hw | ⟨q, hyt, hz, rfl⟩)
    · rcases hw with hw | ⟨_, ⟨x, hx, _, ⟨ys, rfl, loop⟩, rfl⟩, z, hz, rfl⟩
      · exact accepts.start hw
      refine accepts.step _ ?_ hz rfl
      induction ys using List.reverseRecOn
      · exact trace.start none (by simpa)
      rename_i ys y ih
      rw [List.join_append, List.join_singleton]
      simp only [← List.append_assoc]
      refine trace.step none none (ih ?_) (loop y (by simp)) rfl
      intro y mem
      exact loop y (by simp[mem])
    · rcases hz with hz | ⟨_, ⟨x, hx, _, ⟨ys, rfl, loop⟩, rfl⟩, z, hz, rfl⟩
      · exact accepts.step (some q) (M.rip_trace_correct ▸ hyt) hz rfl
      rw [← List.append_assoc]
      refine accepts.step none ?_ hz rfl
      rw [← List.append_assoc]
      induction ys using List.reverseRecOn
      · simp; exact trace.step (some q) none (M.rip_trace_correct ▸ hyt) hx rfl
      rename_i ys y ih
      rw [List.join_append, List.join_singleton]
      rw [← List.append_assoc]
      simp only [List.mem_append] at loop
      refine trace.step none none (ih ?_) (loop y (by simp)) rfl
      intro y mem
      exact loop y (.inl mem)
  · rintro (hw | ⟨q, hyt, hz, rfl⟩)
    · exact accepts.start (.inl hw)
    rcases M.rip_trace_aux hyt with ⟨q, rfl, hyt'⟩ | ⟨rfl, y, z, xs, p, hyt', hz', loop, rfl⟩
    · exact accepts.step q hyt' (.inl hz) rfl
    rcases p with ⟨⟩ | p
    · subst y
      refine accepts.start <| .inr ?_
      exact ⟨_, ⟨_, hz', _, ⟨xs, rfl, loop⟩, rfl⟩, _, hz, rfl⟩
    · rw [List.append_assoc, List.append_assoc]
      refine accepts.step p hyt' (.inr ?_) rfl
      rw [← List.append_assoc]
      exact ⟨_, ⟨_, hz', _, ⟨xs, rfl, loop⟩, rfl⟩, _, hz, rfl⟩

/-- Maps a GNFA's states across an equivalence.
-/
def mapEquiv {σ τ} (M : GNFA α σ) (e : σ ≃ τ) : GNFA α τ :=
  ⟨fun p q ↦ M.step (p.map e.symm) (q.map e.symm)⟩

/-- Any string that reaches a state in one GNFA will also reach the equivalent state in the
equivalent GNFA -/
lemma mapEquiv_trace_aux {σ τ} (M : GNFA α σ) (e : σ ≃ τ) q :
    M.trace q ≤ (M.mapEquiv e).trace (e q) := by
  intro x hxt
  refine hxt.recOn ?_ ?_ <;>
    first
    | rintro _ _ _ p q _ mat rfl ih
      refine trace.step (e p) (e q) ih ?_ rfl
    | rintro _ _ mat
      refine trace.start _ ?_
  all_goals
  · unfold mapEquiv
    dsimp
    simp only [Equiv.symm_apply_apply]
    exact mat

/-- A GNFA's equivalent will retain any internal (equivalent) state's language. -/
theorem mapEquiv_trace {σ τ} (M : GNFA α σ) (e : σ ≃ τ) q :
    M.trace q = (M.mapEquiv e).trace (e q) := by
  ext
  refine ⟨(M.mapEquiv_trace_aux e q ·), ?_⟩
  intro hxt
  have := (M.mapEquiv e).mapEquiv_trace_aux e.symm (e q) hxt
  simp [Equiv.symm_apply_apply, mapEquiv] at this
  exact this

/-- Any string that reaches the accept state in one GNFA will also reach the accept state in the
equivalent GNFA -/
lemma mapEquiv_correct_aux {σ τ} (M : GNFA α σ) (e : σ ≃ τ) :
    M.accepts ≤ (M.mapEquiv e).accepts := by
  rintro w (hw | ⟨q, hyt, hz, rfl⟩)
  · exact accepts.start hw
  refine accepts.step (e q) (M.mapEquiv_trace e q ▸ hyt) ?_ rfl
  unfold mapEquiv
  simpa

/-- A GNFA's equivalent will retain the original's language. -/
theorem mapEquiv_correct {σ τ} (M : GNFA α σ) (e : σ ≃ τ) :
    M.accepts = (M.mapEquiv e).accepts := by
  ext
  refine ⟨(M.mapEquiv_correct_aux e ·), ?_⟩
  intro h
  have := (M.mapEquiv e).mapEquiv_correct_aux e.symm h
  simp [mapEquiv] at this
  exact this

/-- Any GNFA with a `FinEnum` state space has some `RegularExpression` that matches its language -/
def sigma_toRegularExpression [enum : FinEnum σ] (M : GNFA α σ) :
    (r : RegularExpression α) ×' M.accepts = r.matches' := by
  induction enum using FinEnum.recOnEmptyOption
  · rename_i _ _ e h
    rcases h (M.mapEquiv e.symm) with ⟨r, hr⟩
    exact ⟨r, hr ▸ M.mapEquiv_correct e.symm⟩
  · refine ⟨M.step none none, ?_⟩
    ext
    constructor
    · rintro (mat | ⟨⟨⟩, _, _, _⟩); exact mat
    · exact accepts.start
  · rename_i _ ih
    rcases ih M.rip with ⟨r, hr⟩
    exact ⟨r, M.rip_correct ▸ hr⟩

end GNFA

namespace NFA

variable (M : NFA α σ)
    [DecidablePred (· ∈ M.start)]
    [DecidablePred (· ∈ M.accept)]
    [∀ p a , DecidablePred (· ∈ M.step p a)]

/-- Convert a computably useful NFA to the corresponding GNFA.

TODO: would it be a good idea to make a separate "decidable NFA" structure?
-/
def toGNFA [alphabet : FinEnum α] : GNFA α σ :=
  ⟨fun p q ↦
    match (p, q) with
    | (none, none) => 0
    | (none, some q) => if q ∈ M.start then 1 else 0
    | (some p, none) => if p ∈ M.accept then 1 else 0
    | (some p, some q) =>
        (alphabet.toList).filter (q ∈ M.step p ·) |>.map RegularExpression.char |>.sum⟩

/-- The embedding of an NFA retains its language. -/
-- TODO: maybe mark as @simp
theorem toGNFA_correct [alphabet : FinEnum α] : M.accepts = M.toGNFA.accepts := by
  ext x
  constructor
  · rintro ⟨q, accept, eval⟩
    refine GNFA.accepts.step q ?_ (by simp [toGNFA, accept]) x.append_nil.symm
    clear accept
    induction x using List.reverseRecOn generalizing q
    · exact GNFA.trace.start q (by simp [toGNFA, M.eval_nil ▸ eval])
    rename_i as a ih
    rw [M.eval_append_singleton, M.mem_stepSet] at eval
    rcases eval with ⟨p, mem, step⟩
    refine GNFA.trace.step p q (ih p mem) ?_ rfl
    simp [toGNFA, Language.mem_sum, alphabet.mem_toList, List.mem_filter]
    exact ⟨a, step, rfl⟩
  · rintro (@⟨x, ⟨⟩⟩ | @⟨_, y, z, q, hyt, step, rfl⟩)
    rcases Decidable.em (q ∈ M.accept) with accept | accept <;> simp [toGNFA, accept] at step
    subst z
    refine ⟨q, accept, ?_⟩
    clear accept
    rw [List.append_nil]
    induction y using List.reverseRecOn generalizing q
    · rw [NFA.eval_nil]
      rcases hyt with ⟨_, step⟩ | @⟨_, x, y, z, p, hyt, step, eq⟩
      · simp only [toGNFA] at step
        rcases Decidable.em (q ∈ M.start) with start | start
        · exact start
        · simp [start] at step
      · rw [List.nil_eq_append] at eq
        rcases eq with ⟨rfl, rfl⟩
        simp [toGNFA, Language.mem_sum, List.mem_map] at step
        rcases step with ⟨_, _, _, ⟨⟩⟩
    · rename_i as a ih
      rw [M.eval_append_singleton]
      rcases hyt with ⟨_, step⟩ | @⟨x, y, z, p, _, hyt, step, eq⟩
      · rcases Decidable.em (q ∈ M.start) with start | start <;> simp [toGNFA, start] at step
      simp [toGNFA, Language.mem_sum, List.mem_filter] at step
      rcases step with ⟨r, step, rfl⟩
      rcases List.append_inj' eq rfl with ⟨rfl, ⟨rfl⟩⟩
      rw [M.mem_stepSet]
      exact ⟨p, ih p hyt, step⟩

/-- Any computably useful NFA with a `FinEnum` state space has some `RegularExpression` that matches
its language -/
def sigma_toRegularExpression [FinEnum α] [FinEnum σ] :
    (r : RegularExpression α) ×' M.accepts = r.matches' :=
  let ⟨r, hr⟩ := (M.toGNFA).sigma_toRegularExpression; ⟨r, hr ▸ M.toGNFA_correct⟩

/-- Compute a regular expression for a useful NFA that matches its language. -/
def toRegularExpression [FinEnum α] [FinEnum σ] : RegularExpression α :=
  M.sigma_toRegularExpression.fst

/-- The computed regular expression for a useful NFA indeed matches its language. -/
theorem toRegularExpression_correct [FinEnum α] [FinEnum σ] :
    M.accepts = M.toRegularExpression.matches' :=
  M.sigma_toRegularExpression.snd

/-- Non-constructively, enumerability of state space and alphabet are not needed for an NFA to
permit the possibility of having a regular expression that matches its language. -/
theorem exists_toRegularExpression [Fintype α] [Fintype σ] (M : NFA α σ) :
    ∃ r : RegularExpression α, M.accepts = r.matches' := by
  classical
  have := FinEnum.ofNodupList
    Fintype.elems.toList
    (fun x : α ↦ (Fintype.elems.mem_toList).mpr (Fintype.complete x))
    (Fintype.elems.nodup_toList)
  have : FinEnum σ := FinEnum.ofNodupList
    Fintype.elems.toList
    (fun x : σ ↦ (Fintype.elems.mem_toList).mpr (Fintype.complete x))
    (Fintype.elems.nodup_toList)
  have := M.sigma_toRegularExpression
  exact ⟨this.fst, this.snd⟩

end NFA

