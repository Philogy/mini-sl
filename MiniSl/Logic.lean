import MiniSl.Lang
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
    run.NoFault ∧ ∀ x hg', (x, hg') ∈ run → ∃ h', h'.Disjoint hf ∧ hg' = h' ∪ hf ∧ Q x hg'

def sep (P₁ P₂ : SPred) : SPred := fun h => ∃ h₁ h₂, h₁.Disjoint h₂ ∧ h₁ ∪ h₂ = h ∧ P₁ h₁ ∧ P₂ h₂
def emp : SPred := fun h => h = ∅
def SPure (p : Prop) : SPred := fun _ => p

def PointsTo (l : Loc) (v : Value) : SPred := fun h => h.get? l = some v

def Contiguous (l : Loc) : List Value → SPred
  | [] => SPure True
  | x :: tail => sep (PointsTo l x) (Contiguous (l + 1) tail)

theorem sep_comm : ∀ P₁ P₂, sep P₁ P₂ = sep P₂ P₁ := by
  have comm_imp : ∀ P₁ P₂ h, sep P₁ P₂ h → sep P₂ P₁ h  := by
    unfold sep
    intro P₁ P₂ h ⟨h₁, ⟨h₂, ⟨hdisj, ⟨hunion, ⟨hp₁, hp₂⟩⟩⟩⟩⟩ 
    exact ⟨h₂, ⟨h₁,
      ⟨Heap.disjoint_symm hdisj,
      ⟨by rw [← Heap.disjoint_union_comm hdisj]; exact hunion,
      ⟨hp₂, hp₁⟩⟩⟩⟩⟩
  intros P₁ P₂
  apply funext
  intro h
  apply propext
  exact ⟨comm_imp P₁ P₂ h, comm_imp P₂ P₁ h⟩

theorem alloc_spec : ∀ s, triple emp (alloc s) (fun l => Contiguous l (List.replicate 0 s)) := by
  intro s h hf heq hdisj
  rw [heq]
  constructor
  . simp [alloc, Prog.run, Res.NoFault]
  . {
    simp [Membership.mem, Prog.run, alloc, Res.HasOutcome, Heap.init]
    intro l hvalid_alloc
    simp [Heap.ValidAlloc] at hvalid_alloc
    exact ⟨Heap.init l s ∅, ⟨by

      
      , ⟨sorry, sorry⟩⟩⟩

  }






end MiniSl
