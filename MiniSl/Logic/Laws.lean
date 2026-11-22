import MiniSl.Logic.Proofs

universe u v
variable {α : Type u} {β : Type v}

namespace MiniSl.Logic

open Prog

@[simp] theorem emp_emp : emp ∅ :=
  Proofs.emp_emp

theorem frame_rule : ∀ (p : Prog α) P P' Q, ⦃ P ⦄ p ⦃ Q ⦄ → ⦃ P ∗ P' ⦄ p ⦃ fun x => Q x ∗ P' ⦄ :=
  Proofs.frame_rule

theorem sep_comm : ∀ P₁ P₂, P₁ ∗ P₂ = P₂ ∗ P₁ :=
  Proofs.sep_comm

theorem pure_spec : ∀ x : α, ⦃ emp ⦄ pure x ⦃ fun _ => emp ⦄ :=
  Proofs.pure_spec

theorem alloc_spec : ∀ s, ⦃ emp ⦄ alloc s ⦃ fun l => Contiguous l (List.replicate s 0) ⦄ :=
  Proofs.alloc_spec

end MiniSl.Logic
