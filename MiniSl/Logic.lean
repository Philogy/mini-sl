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
  have comm_imp : ∀ P₁ P₂ h, sep P₁ P₂ h → sep P₂ P₁ h :=
    fun _ _ _ ⟨h₁, h₂, hdisj, hunion, hp₁, hp₂⟩ =>
      ⟨h₂, h₁, Heap.disjoint_symm hdisj, Heap.disjoint_union_comm hdisj ▸ hunion, hp₂, hp₁⟩
  intro P₁ P₂
  funext h
  exact propext ⟨comm_imp P₁ P₂ h, comm_imp P₂ P₁ h⟩

theorem alloc_spec : ∀ s, triple emp (alloc s) (fun l => Contiguous l (List.replicate s 0)) := by
  intro s h hf heq hdisj
  cases heq
  have set_get : ∀ (ls : List Loc) (h₀ : Heap) i,
      ls.foldl (fun h l => h.set l 0) h₀ i = if i ∈ ls then some 0 else h₀ i := by
    intro ls; induction ls <;> simp_all [Heap.set] <;> grind
  have contig : ∀ n (l : Loc) (H : Heap), (∀ i < n, H (l + i) = some 0) →
      Contiguous l (List.replicate n 0) H := by
    intro n
    induction n with
    | zero => intros; trivial
    | succ n ih =>
      intro l H hH
      refine ⟨(∅ : Heap).set l 0, fun j => if j = l then none else H j, fun j => ?_,
        funext fun j => ?_, Heap.set_get_is_value _ _ _, ih _ _ fun i hi => ?_⟩
      · simp only [Heap.get?, Heap.set, EmptyCollection.emptyCollection]; grind
      · have := hH 0; simp only [Heap.set, Union.union, Heap.union, EmptyCollection.emptyCollection]; grind
      · have := hH (i + 1); grind
  refine ⟨by simp [alloc, Prog.run, Res.NoFault], ?_⟩
  rintro x hg' ⟨⟨l, hl⟩, rfl, rfl⟩
  refine ⟨Heap.init l s ∅, fun i => ?_, funext fun i => ?_, contig _ _ _ fun i hi => ?_⟩
  all_goals simp only [Heap.get?, Heap.init, set_get, Union.union, Heap.union]
  · split
    · have := hl i
      simp only [Membership.mem] at this
      simp_all [Heap.emp_union, Heap.get?]
      grind
    · exact .inl rfl
  · split <;> rfl
  · simp; grind

end MiniSl
