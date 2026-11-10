import LeanModels.Sv.Kernel.Core0E

/-!
# Array-backed E-core-0 executor

`Store` is a function in the authoritative E definitions.  Carrying the
function produced by each write through a long settling run duplicates its
term at every later read.  This file is an X-layer executor: it snapshots the
flat declaration cells into an `Array` after each micro-step, then presents
that array as a `Store` for the next step.  The fallback argument preserves
the values of non-flat `VarId`s, so rebasing is extensionally equal to the
original store without assuming a flatness invariant.

The executor is proved equal to `exec`; `exec_sound` is therefore still its
semantic bridge.  Fuel appears only in this test executor.
-/

namespace LeanModels.Sv.Kernel

set_option autoImplicit false

/-! ## Flat-cell snapshots -/

def arrayCells (s : Store) : Nat → Array Val
  | 0 => #[]
  | n + 1 => (arrayCells s n).push (s { decl := n })

def arrayStore (a : Array Val) (fallback : Store) (x : VarId) : Val :=
  match x.path with
  | [] => a[x.decl]?.getD (fallback x)
  | _ :: _ => fallback x

theorem arrayCells_size (s : Store) :
    ∀ n, (arrayCells s n).size = n
  | 0 => rfl
  | n + 1 => by simp [arrayCells, arrayCells_size s n]

theorem arrayCells_get (s : Store) :
    ∀ (n i : Nat), i < n → (arrayCells s n)[i]? = some (s { decl := i })
  | 0, _, hi => by omega
  | n + 1, i, hi => by
      rw [arrayCells]
      by_cases h : i = n
      · subst i
        have hs : (arrayCells s n).size = n := arrayCells_size s n
        calc
          ((arrayCells s n).push (s { decl := n }))[n]? =
              ((arrayCells s n).push (s { decl := n }))[(arrayCells s n).size]? := by rw [hs]
          _ = some (s { decl := n }) := Array.getElem?_push_size
      · have hi' : i < n := by omega
        rw [Array.getElem?_push]
        simpa [arrayCells_size s n, h] using arrayCells_get s n i hi'

theorem arrayStore_cells (s : Store) (n : Nat) :
    arrayStore (arrayCells s n) s = s := by
  funext x
  obtain ⟨path, decl⟩ := x
  cases path with
  | nil =>
      simp only [arrayStore]
      by_cases h : decl < n
      · rw [arrayCells_get s n decl h]
        rfl
      · have hs : (arrayCells s n).size ≤ decl := by
          simpa [arrayCells_size s n] using h
        rw [Array.getElem?_eq_none hs]
        rfl
  | cons seg rest => rfl

def rebase (E : Elab) (c : Config) : Config :=
  { c with store := arrayStore (arrayCells c.store E.decls.size) c.store }

theorem rebase_eq (E : Elab) (c : Config) : rebase E c = c := by
  unfold rebase
  rw [arrayStore_cells]

/-! ## The array-backed executor -/

def execArray (E : Elab) (ch : Choice) : Nat → Config → ExecResult
  | 0, c => .outOfBudget c
  | n + 1, c =>
      match step E ch (rebase E c) with
      | .next c' => execArray E ch n (rebase E c')
      | .slotClosed c' => .closed c'
      | .refused r => .refused r

theorem execArray_eq (E : Elab) (ch : Choice) :
    ∀ (n : Nat) (c : Config), execArray E ch n c = exec E ch n c
  | 0, _ => rfl
  | n + 1, c => by
      simp only [execArray, exec]
      rw [rebase_eq E c]
      cases h : step E ch c with
      | next c' =>
          change execArray E ch n (rebase E c') = exec E ch n c'
          rw [rebase_eq E c', execArray_eq E ch n c']
      | slotClosed c' => change ExecResult.closed c' = ExecResult.closed c'; rfl
      | refused r => change ExecResult.refused r = ExecResult.refused r; rfl

theorem execArray_sound {E : Elab} {ch : Choice} {n : Nat} {c c' : Config}
    (h : execArray E ch n c = .closed c') : SlotCloses E ch c c' := by
  apply exec_sound
  rw [execArray_eq E ch n c] at h
  exact h

end LeanModels.Sv.Kernel
