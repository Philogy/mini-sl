namespace MiniSl

abbrev Value := Nat
abbrev Loc := Nat
abbrev Size := Nat

def Heap := List (Loc × Value)

instance : EmptyCollection Heap := ⟨[]⟩

namespace Heap

def get? (l : Loc) : Heap → Option Value :=
  fun h => h.findSome?
    (fun (l', v) => if l = l' then some v else none)

def set (l : Loc) (value : Value) : Heap → Heap :=
  fun h => (l, value) :: h.filter (fun (l', _) => l' ≠ l)

def init (start : Loc) (size : Size) : Heap → Heap :=
  List.range size
    |>.map (· + start)
    |>.foldl (fun h l => h.set l 0)

theorem set_get_is_value : ∀ (h : Heap) l v, (h.set l v).get? l = some v := by simp [set, get?]

theorem set_preserves_unset : ∀ (h : Heap) l l' v, l ≠ l' → (h.set l v).get? l' = h.get? l' := by
  intro h l l' v hl_ne
  simp [get?, set, Ne.symm hl_ne]
  induction h with
  | nil => rfl
  | cons x t ih => by_cases hx : x.1 = l <;> simp_all [List.findSome?_cons, Ne.symm hl_ne]

def ValidAlloc (h : Heap) (start : Loc) (size : Size) : Prop := ∀ i ∈ [start:start+size], h.get? i = none

def Alloc (h : Heap) (size : Size) := { l // h.ValidAlloc l size }

theorem always_exists_valid_alloc : ∀ h size, Nonempty (Alloc h size) :=
  fun h size => .intro ⟨h.foldl (fun b (l, _) => max b (l + 1)) 0, by
    have key : ∀ (t : List (Nat × Nat)) (b : Nat), b ≤ t.foldl (fun b x => max b (x.1 + 1)) b ∧
        ∀ x ∈ t, x.1 < t.foldl (fun b x => max b (x.1 + 1)) b := by
      intro t
      induction t with
      | nil => simp
      | cons y t ih =>
        intro b
        obtain ⟨h1, h2⟩ := ih (max b (y.1 + 1))
        simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
        exact ⟨by omega, by omega, h2⟩
    intro i hi
    apply List.findSome?_eq_none_iff.2
    intro x hx
    have := (key h 0).2 x hx
    simp [Membership.mem] at hi
    simp only [Loc, Value, Size] at *
    simp
    omega
  ⟩


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
