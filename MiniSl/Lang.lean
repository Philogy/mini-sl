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


def Finite (h : Heap) (ls : List (Loc × Value)) : Prop := ls.foldl (fun hᵢ (l, v) => hᵢ.set l v) ∅ = h

def ValidAlloc (h : Heap) (start : Loc) (size : Size) : Prop := ∀ i ∈ [start:start+size], h.get? i = none

def Alloc (h : Heap) (size : Size) := { l // h.ValidAlloc l size }


end Heap

structure Fault

universe u v

variable {α β : Type u}

inductive Prog.Res (α : Type u) where
  | fault
  | silent (value : α) (h' : Heap)
  | alloc (size : Size) (h' : Heap) (k : { l // h'.ValidAlloc l size } → Res α)

def Prog (α : Type u) :=  Heap → Prog.Res α

namespace Prog

def run : Prog α → Heap → Res α
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

end Prog

end MiniSl
