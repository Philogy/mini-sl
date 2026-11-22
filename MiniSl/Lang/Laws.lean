import MiniSl.Lang.Proofs

namespace MiniSl.Heap

theorem union_maintains_h₁ : ∀ (h₁ h₂ : Heap) l x, h₁.get? l = some x → (h₁ ∪ h₂).get? l = some x :=
  Proofs.union_maintains_h₁

theorem set_get_is_value : ∀ (h : Heap) l v, (h.set l v).get? l = some v :=
  Proofs.set_get_is_value

theorem set_preserves_unset : ∀ (h : Heap) l l' v, l ≠ l' → (h.set l v).get? l' = h.get? l' :=
  Proofs.set_preserves_unset

theorem union_assoc : ∀ h₁ h₂ h₃ : Heap, (h₁ ∪ h₂) ∪ h₃ = h₁ ∪ (h₂ ∪ h₃) :=
  Proofs.union_assoc

theorem disjoint_both_is_disjoint_union
  : ∀ {h₁ h₂ h' : Heap}, h'.Disjoint h₁ ∧ h'.Disjoint h₂ ↔ h'.Disjoint (h₁ ∪ h₂) :=
  Proofs.disjoint_both_is_disjoint_union

theorem always_exists_valid_alloc : ∀ h ls size, h.Finite ls → Nonempty (Alloc h size) :=
  Proofs.always_exists_valid_alloc

@[simp] theorem emp_disjoint : ∀ h, Disjoint h ∅ :=
  Proofs.emp_disjoint

@[simp] theorem disjoint_symm : ∀ {h₁ h₂}, Disjoint h₁ h₂ → Disjoint h₂ h₁ :=
  Proofs.disjoint_symm

@[simp] theorem disjoint_union_comm : ∀ {h₁ h₂ : Heap}, Disjoint h₁ h₂ →  h₁ ∪ h₂ = h₂ ∪ h₁ :=
  Proofs.disjoint_union_comm

@[simp] theorem emp_union : ∀ h : Heap, ∅ ∪ h = h :=
  Proofs.emp_union

@[simp] theorem union_emp : ∀ h : Heap, h ∪ ∅ = h :=
  Proofs.union_emp

end MiniSl.Heap
