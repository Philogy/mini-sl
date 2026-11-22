import MiniSl.Lang.Laws
import MiniSl.Logic

universe u v
variable {α : Type u} {β : Type v}

namespace MiniSl.Logic.Proofs

open Prog

theorem emp_emp : emp ∅ := rfl

theorem frame_rule : ∀ (p : Prog α) P P' Q, ⦃ P ⦄ p ⦃ Q ⦄ → ⦃ P ∗ P' ⦄ p ⦃ fun x => Q x ∗ P' ⦄ := by
  intro p P P' Q htrip h hf hpre hdisjoint
  simp
  have ⟨hi, ⟨hi', ⟨hi_disj, ⟨hi_eq, ⟨hhi, hhi'⟩⟩⟩⟩⟩ := hpre
  rewrite [← hi_eq] at hdisjoint
  have ⟨hf_disj_hi, hf_disj_hi'⟩ := Heap.disjoint_both_is_disjoint_union.mpr (Heap.disjoint_symm hdisjoint)
  have ⟨hno_fault, hpost⟩ := htrip hi (hi' ∪ hf) hhi (by grind [Heap.disjoint_both_is_disjoint_union, Heap.disjoint_symm])
  constructor <;> rw [← hi_eq, Heap.union_assoc]
  . exact hno_fault
  . {
    intro x hg' hrun
    have ⟨h', ⟨hpost_disj, ⟨hg'_eq, hpost⟩⟩⟩ := hpost x hg' hrun
    refine ⟨h' ∪ hi', ⟨?_, ⟨?_, ?_⟩⟩⟩ 
    . apply Heap.disjoint_symm
      apply Heap.disjoint_both_is_disjoint_union.mp
      constructor
      . apply Heap.disjoint_symm
        exact (Heap.disjoint_both_is_disjoint_union.mpr hpost_disj).right
      . exact (Heap.disjoint_both_is_disjoint_union.mpr <| Heap.disjoint_symm hdisjoint).right
    . rewrite [Heap.union_assoc _ _ _]
      exact hg'_eq
    . simp [sep]
      refine ⟨h', ⟨hi', ⟨?_, ⟨by rfl, ⟨hpost, hhi'⟩⟩⟩⟩⟩
      . exact (Heap.disjoint_both_is_disjoint_union.mpr hpost_disj).left
  }

theorem sep_comm : ∀ P₁ P₂, P₁ ∗ P₂ = P₂ ∗ P₁ := by
  have comm_imp : ∀ P₁ P₂ h, sep P₁ P₂ h → sep P₂ P₁ h :=
    fun _ _ _ ⟨h₁, h₂, hdisj, hunion, hp₁, hp₂⟩ =>
      ⟨h₂, h₁, Heap.disjoint_symm hdisj, Heap.disjoint_union_comm hdisj ▸ hunion, hp₂, hp₁⟩
  intro P₁ P₂
  funext h
  exact propext ⟨comm_imp P₁ P₂ h, comm_imp P₂ P₁ h⟩

theorem sep_assoc : ∀ P₁ P₂ P₃, (P₁ ∗ P₂) ∗ P₃ = P₁ ∗ (P₂ ∗ P₃) := by
  intro P₁ P₂ P₃
  funext h
  apply propext
  constructor
  · rintro ⟨_, h₃, hd₁₂₃, rfl, ⟨h₁, h₂, hd₁₂, rfl, hp₁, hp₂⟩, hp₃⟩
    have ⟨hd₃₁, hd₃₂⟩ := Heap.disjoint_both_is_disjoint_union.mpr (Heap.disjoint_symm hd₁₂₃)
    exact ⟨h₁, h₂ ∪ h₃, Heap.disjoint_both_is_disjoint_union.mp ⟨hd₁₂, Heap.disjoint_symm hd₃₁⟩,
      (Heap.union_assoc _ _ _).symm, hp₁, h₂, h₃, Heap.disjoint_symm hd₃₂, rfl, hp₂, hp₃⟩
  · rintro ⟨h₁, _, hd₁₂₃, rfl, hp₁, ⟨h₂, h₃, hd₂₃, rfl, hp₂, hp₃⟩⟩
    have ⟨hd₁₂, hd₁₃⟩ := Heap.disjoint_both_is_disjoint_union.mpr hd₁₂₃
    exact ⟨h₁ ∪ h₂, h₃, Heap.disjoint_symm (Heap.disjoint_both_is_disjoint_union.mp
      ⟨Heap.disjoint_symm hd₁₃, Heap.disjoint_symm hd₂₃⟩),
      Heap.union_assoc _ _ _, ⟨h₁, h₂, hd₁₂, rfl, hp₁, hp₂⟩, hp₃⟩

theorem pure_spec : ∀ x : α, ⦃ emp ⦄ pure x ⦃ fun _ => emp ⦄ := by
  intro x h hf hemp _
  simp_all
  constructor
  . simp_all [pure, Prog.run, Res.NoFault]
  . intro x' hg' hrun
    exact ⟨∅, by
      simp [Heap.disjoint_symm <| Heap.emp_disjoint _]
      simp_all [pure, Prog.run, emp, Membership.mem, Res.HasOutcome]
    ⟩

theorem alloc_spec : ∀ s, ⦃ emp ⦄ alloc s ⦃ fun l => Contiguous l (List.replicate s 0) ⦄ := by
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
      simp_all [Heap.get?]
      grind
    · exact .inl rfl
  · split <;> rfl
  · simp; grind

end MiniSl.Logic.Proofs
