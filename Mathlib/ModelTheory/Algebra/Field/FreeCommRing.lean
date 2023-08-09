/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Algebra.Ring.FreeCommRing
import Mathlib.ModelTheory.Algebra.Field.Basic

namespace FirstOrder

namespace Language

namespace field

noncomputable def termOfFreeCommRing (p : FreeCommRing α) : Language.field.Term α :=
  (ring.termOfFreeCommRing p).realize Term.var

variable {K : Type _} [CompatibleField K]

@[simp]
theorem realize_termOfFreeCommRing (p : FreeCommRing α) (v : α → K) :
    (termOfFreeCommRing p).realize v = FreeCommRing.lift v p := by
  conv_rhs => rw [← ring.realize_termOfFreeCommRing]
  rw [termOfFreeCommRing]
  induction ring.termOfFreeCommRing p with
  | var _ => simp
  | func f _ ih => cases f <;> simp_all [Term.realize]

end field

end Language

end FirstOrder
