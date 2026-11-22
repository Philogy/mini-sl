import MiniSl.Lang

universe u

variable {α : Type u} 

namespace MiniSl.Prog

def Res.HasOutcome : Res α → α → Heap → Prop
  | .silent a h, a', h' => a = a' ∧ h = h'
  | .fault, _, _ => False
  | .alloc _ _ k, a', h' => ∃ l, (k l).HasOutcome a' h'

instance : Membership (α × Heap) (Res α) where
  mem
  | r, (a', h') => r.HasOutcome a' h'


def Res.NoFault : Res α → Prop
  | silent _ _ => True
  | .fault => False
  | .alloc _ _ k => ∀ l, (k l).NoFault

def Res.Deterministic (r : Res α) (x : α) : Prop := ∀ x' h, r.HasOutcome x' h → x = x'

end MiniSl.Prog
