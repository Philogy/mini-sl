import MiniSl.Lang

universe u

variable {α : Type u} 

namespace MiniSl

inductive Res.NoFault : Res α → Prop
  | silent {a h} : NoFault (.silent a h)
  | valid_alloc {s h k} : (∀ l, (k l).NoFault)  → NoFault (.alloc s h k)

def Prog.NoFault (p : Prog α) : Prop := (p.run ∅).NoFault

inductive Res.Deterministic : Res α → α → Prop
  | silent {r h} : Deterministic (.silent r h) r
  | any_alloc {s h k r} : (∀ l, (k l).Deterministic r) → Deterministic (.alloc s h k) r

def Prog.Deterministic (p : Prog α) : α → Prop := (p.run ∅).Deterministic

def Prog.Safe (p : Prog α) : Prop := p.NoFault ∧ ∃ r, p.Deterministic r

end MiniSl
