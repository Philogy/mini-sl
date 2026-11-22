import MiniSl.Lang

namespace MiniSl.Heap

theorem union_maintains_h₁ : ∀ (h₁ h₂ : Heap) l x, h₁.get? l = some x → (h₁ ∪ h₂).get? l = some x := by
  simp_all [get?, Union.union, union]

theorem set_get_is_value : ∀ (h : Heap) l v, (h.set l v).get? l = some v := by simp [set, get?]

theorem set_preserves_unset : ∀ (h : Heap) l l' v, l ≠ l' → (h.set l v).get? l' = h.get? l' := by
  simp [get?, set]
  grind

theorem union_assoc : ∀ h₁ h₂ h₃ : Heap, (h₁ ∪ h₂) ∪ h₃ = h₁ ∪ (h₂ ∪ h₃) := by
  intro h₁ h₂ h₃
  apply funext
  intro l
  simp [Union.union]
  unfold union
  cases h₁ l <;> simp

theorem disjoint_both_is_disjoint_union
  : ∀ {h₁ h₂ h' : Heap}, h'.Disjoint h₁ ∧ h'.Disjoint h₂ ↔ h'.Disjoint (h₁ ∪ h₂) := by
  intro h₁ h₂ h'
  simp_all [Disjoint, get?, Union.union]
  unfold union
  constructor <;> grind

theorem always_exists_valid_alloc : ∀ h ls size, h.Finite ls → Nonempty (Alloc h size) := by
  intro h ls size h_fin
  have h_unset : ∀ (ls : List (Loc × Value)) (h₀ : Heap) l, (∀ p ∈ ls, p.1 < l) →
      (ls.foldl (fun hᵢ (l, v) => hᵢ.set l v) h₀).get? l = h₀.get? l := by
    intro ls
    induction ls <;> grind [set_preserves_unset]
  have h_bound : ∀ p ∈ ls, p.1 ≤ (ls.map (·.1)).sum := by
    clear h_fin
    induction ls <;> grind
  refine ⟨⟨(ls.map (·.1)).sum + 1, fun i hi => ?_⟩⟩
  rw [← h_fin, h_unset ls ∅ i fun p hp => by grind [h_bound p hp, hi.1]]
  rfl

@[simp] theorem emp_disjoint : ∀ h, Disjoint h ∅ :=
  fun _ l => .inr (by simp [EmptyCollection.emptyCollection, get?])

@[simp] theorem disjoint_symm : ∀ {h₁ h₂}, Disjoint h₁ h₂ → Disjoint h₂ h₁ := by grind [Disjoint]

@[simp] theorem disjoint_union_comm : ∀ {h₁ h₂ : Heap}, Disjoint h₁ h₂ →  h₁ ∪ h₂ = h₂ ∪ h₁ := by
  intro h₁ h₂ hdisj
  funext l
  cases hdisj l <;> simp_all [get?, Union.union, union]

@[simp] theorem emp_union : ∀ h : Heap, ∅ ∪ h = h := by
  intro h
  funext l
  simp [Union.union, union, EmptyCollection.emptyCollection]

@[simp] theorem union_emp : ∀ h : Heap, h ∪ ∅ = h := by
  intro h
  rw [disjoint_union_comm (emp_disjoint h), emp_union]

namespace MiniSl.Heap
