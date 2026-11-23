import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_284_aux

open PEqualNP.CircuitLowerBounds

-- The circuit of the statement, as a definition.
def C0 : Circuit := ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 11]⟩], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit)

lemma mono0 : PEqualNP.MetaComplexity.Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨by simp [Set.mem_insert_iff, Set.mem_singleton_iff], by decide⟩

set_option maxHeartbeats 4000000 in
lemma spec_a : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    ((List.ofFn (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool)).count true ≤ 2 → (C0.eval (List.ofFn (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool)) = true ↔ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) v = true))) := by
  intro b0 b1 b2 b3 b4 b5
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

set_option maxHeartbeats 4000000 in
lemma spec_b : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    (¬ (C0.eval (List.ofFn (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool)) = true ↔ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) v = true)) ↔ ((![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) 3 = true ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) 4 = true ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) 5 = true ∧ ¬ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) v = true))) := by
  intro b0 b1 b2 b3 b4 b5
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

lemma spec_closed : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    (((List.ofFn (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool)).count true ≤ 2 → (C0.eval (List.ofFn (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool)) = true ↔ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) v = true)))) ∧ ((¬ (C0.eval (List.ofFn (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool)) = true ↔ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) v = true)) ↔ ((![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) 3 = true ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) 4 = true ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) 5 = true ∧ ¬ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) v = true)))) :=
  fun b0 b1 b2 b3 b4 b5 => ⟨spec_a b0 b1 b2 b3 b4 b5, spec_b b0 b1 b2 b3 b4 b5⟩

lemma eval_spec : ∀ x : Fin 6 → Bool,
    ((List.ofFn x).count true ≤ 2 → (C0.eval (List.ofFn x) = true ↔ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) ∧ (¬ (C0.eval (List.ofFn x) = true ↔ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ↔ (x 3 = true ∧ x 4 = true ∧ x 5 = true ∧ ¬ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  intro x
  have h : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  exact spec_closed _ _ _ _ _ _

end PEqualNP.Outside.L_meta_284_aux

theorem PEqualNP.Outside.L_meta_284 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 11]⟩], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 7 ∧ ∀ x : Fin 6 → Bool, ((List.ofFn x).count true ≤ 2 → (C.eval (List.ofFn x) = true ↔ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) ∧ (¬ (C.eval (List.ofFn x) = true ↔ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ↔ (x 3 = true ∧ x 4 = true ∧ x 5 = true ∧ ¬ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  intro C hC
  subst hC
  exact ⟨PEqualNP.Outside.L_meta_284_aux.mono0, rfl,
    PEqualNP.Outside.L_meta_284_aux.eval_spec⟩
