/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Layout
import Mathlib.Tactic.FinCases

/-!
# Actual selected modular-addition placement excluding the active source bit

The dirty subset skips the current selected original source address and
uses only `n-2` of the other original source bits. All other live controls,
target systems, both clean helpers and the reduction flag are excluded by
the full original-port injection [G25, main.tex:271-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- An original source address strictly skipping the current active selector. -/
def dirtySourceIndex (selector : Fin width) (index : Fin (width - 2)) : Fin width :=
  ⟨if index.val < selector.val then index.val else index.val + 1, by
    have inside := index.isLt
    split_ifs <;> omega⟩

/-- No selected dirty address is the simultaneously active original source selector. -/
lemma dirtySourceIndex_ne (selector : Fin width) (index : Fin (width - 2)) :
    dirtySourceIndex selector index ≠ selector := by
  intro same
  have values := congrArg (fun value : Fin width => value.val) same
  dsimp only [dirtySourceIndex] at values
  split_ifs at values <;> omega

/-- The borrowed original dirty addresses are pairwise physically distinct. -/
lemma dirtySourceIndex_injective (selector : Fin width) :
    Function.Injective (dirtySourceIndex selector) := by
  intro first second same
  have values := congrArg (fun value : Fin width => value.val) same
  dsimp only [dirtySourceIndex] at values
  apply Fin.ext
  split_ifs at values <;> omega

private def reductionPort (selector : Fin width) :
    Addition.Gidney.Measured.Reduction.Port width → Port width
  | .inl active => if active = 0 then .inl () else .inr (.inl selector)
  | .inr (.inl target) => .inr (.inr (.inl target))
  | .inr (.inr (.inl dirty)) => .inr (.inl (dirtySourceIndex selector dirty))
  | .inr (.inr (.inr (.inl helper))) => .inr (.inr (.inr (.inl helper)))
  | .inr (.inr (.inr (.inr singleton))) => .inr (.inr (.inr (.inr singleton)))

private lemma reductionPort_injective (selector : Fin width) :
    Function.Injective (reductionPort selector) := by
  intro first second same
  rcases first with firstActive | firstTarget | firstDirty | firstHelper | firstFlag <;>
    rcases second with secondActive | secondTarget | secondDirty | secondHelper | secondFlag
  all_goals first | fin_cases firstActive | skip
  all_goals first | fin_cases secondActive | skip
  all_goals
    first
    | solve
      | simp_all [reductionPort, dirtySourceIndex_ne, (dirtySourceIndex_injective selector).eq_iff]
    | exact False.elim ((dirtySourceIndex_ne selector secondDirty)
        (by simpa [reductionPort] using same.symm))

/-- The actual modular-addition row uses the same original physical systems and no fresh qubits. -/
def reductionLayout (layout : Layout encoding width) (selector : Fin width) :
    Addition.Gidney.Measured.Reduction.Layout encoding width where
  bit := fun port => layout.bit (reductionPort selector port)
  distinct := layout.distinct.comp (reductionPort_injective selector)

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
