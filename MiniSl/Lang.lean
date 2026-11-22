namespace MiniSl

abbrev Value := Nat
abbrev Loc := Nat
abbrev Size := Nat

def Heap := Loc → Option Value

instance : EmptyCollection Heap := ⟨fun _ => none⟩

namespace Heap

def get? (l : Loc) : Heap → Option Value :=
  fun h => h l

def set (l : Loc) (value : Value) : Heap → Heap :=
  fun h l' => if l = l' then some value else h l'

def init (start : Loc) (size : Size) : Heap → Heap :=
  List.range size
    |>.map (· + start)
    |>.foldl (fun h l => h.set l 0)

def union (h₁ h₂ : Heap) : Heap := fun l => h₁ l <|> h₂ l

instance : Union Heap where
  union := union

def Disjoint (h₁ h₂ : Heap) : Prop := ∀ l, (h₁.get? l = none) ∨ (h₂.get? l = none)

theorem union_maintains_h₁ : ∀ (h₁ h₂ : Heap) l x, h₁.get? l = some x → (h₁ ∪ h₂).get? l = some x := by
  simp_all [get?, Union.union, union]

theorem set_get_is_value : ∀ (h : Heap) l v, (h.set l v).get? l = some v := by simp [set, get?]

theorem set_preserves_unset : ∀ (h : Heap) l l' v, l ≠ l' → (h.set l v).get? l' = h.get? l' := by
  simp [get?, set]
  grind

def Finite (h : Heap) (ls : List (Loc × Value)) : Prop := ls.foldl (fun hᵢ (l, v) => hᵢ.set l v) ∅ = h

def ValidAlloc (h : Heap) (start : Loc) (size : Size) : Prop := ∀ i ∈ [start:start+size], h.get? i = none

def Alloc (h : Heap) (size : Size) := { l // h.ValidAlloc l size }

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

end Heap

structure Fault

universe u v

variable {α β : Type u}

inductive Res (α : Type u) where
  | fault
  | silent (value : α) (h' : Heap)
  | alloc (size : Size) (h' : Heap) (k : { l // h'.ValidAlloc l size } → Res α)

def Prog (α : Type u) :=  Heap → Res α

def Prog.run : Prog α → Heap → Res α
  | p, h => p h

def Res.bind : Res α → (α → Prog β) → Res β
  | .fault, _ => .fault
  | .silent a h', f => (f a).run h'
  | .alloc s h' k, f => .alloc s h' fun r => (k r).bind f

def Prog.bind : Prog α → (α → Prog β) → Prog β
  | p, f => fun h => (p h).bind f

instance : Monad Prog where
  pure a := fun h => .silent a h
  bind := Prog.bind

def alloc (size : Size) : Prog Loc :=
  fun h => .alloc size h (fun l => .silent l (h.init l size))

def load (l : Loc) : Prog Value := fun h =>
  match h.get? l with
  | some v => .silent v h
  | none => .fault

def store (l : Loc) (v : Value) : Prog Unit :=
  fun h =>
    if (h.get? l).isSome then
      .silent () (h.set l v)
    else
      .fault

end MiniSl
