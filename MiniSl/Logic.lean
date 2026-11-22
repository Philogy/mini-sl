import MiniSl.Lang
import MiniSl.Lang.Laws
import MiniSl.Safety

universe u v
variable {α : Type u} {β : Type v}

namespace MiniSl

/-- Separation Logic Heap Predicate -/
def SPred := Heap → Prop

/-- Separation Logic Triple -/
def triple (P : SPred) (f : Prog α) (Q : α → SPred) : Prop :=
  ∀ h hf, P h → h.Disjoint hf →
    let run := f.run (h ∪ hf)
    run.NoFault ∧ ∀ x hg', (x, hg') ∈ run → ∃ h', h'.Disjoint hf ∧ hg' = h' ∪ hf ∧ Q x h'
notation:50 "⦃ " P " ⦄ " e " ⦃ " Q " ⦄" => triple P e Q

def sep (P₁ P₂ : SPred) : SPred := fun h => ∃ h₁ h₂, h₁.Disjoint h₂ ∧ h₁ ∪ h₂ = h ∧ P₁ h₁ ∧ P₂ h₂
infixl:52 " ∗ " => sep

def emp : SPred := fun h => h = ∅

def SPure (p : Prop) : SPred := fun _ => p
notation:50 "⌈" p "⌉" => SPure p

def PointsTo (l : Loc) (v : Value) : SPred := fun h => h.get? l = some v
infix:54 " ↦ " => PointsTo

def Contiguous (l : Loc) : List Value → SPred
  | [] => ⌈True⌉
  | x :: tail => l ↦ x ∗ Contiguous (l + 1) tail


end MiniSl
