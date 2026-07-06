module

public import Strips.VarSet
import Mathlib.Data.Finset.Dedup

public section

namespace STRIPS

/-!
# Basic definitions for the STRIPS formalism

We define some basic definitions of the STRIPS formalism for automated planning. More specifically,
this file implements:
* Basic definitions of states, actions, planning tasks, etc.,
* Definition of paths in the search space and various lemmas to work with them,
* Definition of reachability, plans and unsolvability,
* Progression and regression, and various lemmas to work with them.
-/

/-! ## States and sets of states -/

/-- A state is a set of variables, containing all variables that are true. -/
abbrev State n := Set (Fin n)

abbrev States n := Set (State n)

/-! ## Actions and sets of actions -/

/-- Actions in the STRIPS formalism -/
structure Action n where
  /-- The name of the action. -/
  name : String
  /-- The preconditions of the action. -/
  pre : VarSet n
  /-- The adding effects of the action. -/
  add : VarSet n
  /-- The deleting effects of the action. -/
  del : VarSet n
  /-- The cost of the action. -/
  cost : ℕ
  deriving Repr, DecidableEq

abbrev Actions n := Set (Action n)

/-! ## Applicability and successor states -/

/-- An action is applicable in a state if all its preconditions are true in the state. -/
abbrev Applicable {n} (s : State n) (a : Action n) : Prop := SetLike.coe a.pre ⊆ s

/--
If an action `a` is applicable in a state `s`,
then `s[a] := (s \ a.del) ∪ a.add` is the successor of `s`.
-/
abbrev Successor {n} (a : Action n) (s s' : State n) : Prop :=
  Applicable s a ∧ s' = (s \ a.del) ∪ a.add

/-! ## STRIPS planning problems -/
/--
A planning problem in the STRIPS formalism. The variables of the planning task are all elements of
`Fin n`. Note that most fields have two version:
* an primed version which uses a representation that is efficient at run-time, and
* an unprimed version which is more suited for theoretical results
-/
structure PlanningTask n where
  /-- The names of the variables. -/
  varNames : Vector String n
  /-- The actions of the planning problem. See `STRIPS.actions` for the version using `Actions`. -/
  actions' : List (Action n)
  /-- The initial state of the planning problem. See `STRIPS.init` for the version using `State`. -/
  init' : VarSet n
  /--
  The goal of the planning problem, indicating which variables need to be true in a goal state.
  See also `GoalState` and `STRIPS.goal_states` in `Validator.PlanningTask.Basic`.
  -/
  goal' : VarSet n
  deriving Repr

namespace PlanningTask

def actions {n} (pt : PlanningTask n) : Actions n :=
  List.toFinset pt.actions'

lemma mem_actions' {n} {pt : PlanningTask n} {a} : a ∈ pt.actions' ↔ a ∈ pt.actions := by
  simp only [actions, List.coe_toFinset, Set.mem_setOf_eq]

def init {n} (pt : PlanningTask n) : State n :=
  SetLike.coe pt.init'

lemma mem_init' {n} {pt : PlanningTask n} {i} : i ∈ pt.init' ↔ i ∈ pt.init := by
  simp only [init, SetLike.mem_coe]

@[expose]
def GoalState {n} (pt : PlanningTask n) (s : State n) : Prop :=
  SetLike.coe pt.goal' ⊆ s

/-- The set of all goal states of the given planning problem. -/
def goal_states {n} (pt : PlanningTask n) : States n :=
  { s | pt.GoalState s }

lemma mem_goal_states {n} {pt : PlanningTask n} {s} : s ∈ pt.goal_states ↔ GoalState pt s := by
  simp only [goal_states, Set.mem_setOf_eq]

/-! ### Path -/

/--
Given a STRIPS planning task `pt`, `Path s1 s2` is a path form the state `s1` to the state `s2`
in the state space of `pt`.
-/
inductive Path {n} (pt : PlanningTask n) : State n → State n → Type
  /-- The empty path consisting of a single node `s`. -/
  | empty s : Path pt s s
  /--
  The path consisting of the node `s`, and the path `π`, where `s[a]` is the first node of `π`.
  -/
  | cons a {s1} s2 {s3}
    (ha : a ∈ pt.actions) (succ : Successor a s1 s2) (π : Path pt s2 s3) : Path pt s1 s3

namespace Path

/-! ### snoc -/
/--
In `Path.cons`, paths are expanded by adding states at the front of the path
(leaving the last state unchanged). `Path.snoc` allows to extend the path at the back,
leaving the first state unchanged. The name snoc comes from reading cons in reverse order.
-/
def snoc {n} {pt : PlanningTask n} a {s1} s2 {s3} (ha : a ∈ pt.actions)
    (π : Path pt s1 s2) (succ : Successor a s2 s3) : Path pt s1 s3 :=
  match π with
  | empty s => cons a s3 ha succ (empty s3)
  | cons a' s4 ha' succ' π' =>
      let π'' := snoc a s2 ha π' succ
      cons a' s4 ha' succ' π''

/-- The length of a path. -/
def length {n} {pt : PlanningTask n} {s s'} : Path pt s s' → ℕ
  | empty _ => 0
  | cons _ _ _ _ π => π.length + 1

@[simp]
lemma length_snoc {n} {pt : PlanningTask n} {a s1 s2 s3}
    {ha : a ∈ pt.actions} {π : Path pt s1 s2} {succ : Successor a s2 s3} :
    length (snoc a s2 ha π succ) = π.length + 1 := by
  induction π with
  | empty s => simp[snoc, length]
  | cons a' s2 ha' succ' π ih => simp [snoc, length, ih]

/--
Convert `Path.cons`, where we have access to the first action and the second state of the path,
to `Path.snoc`, where we have access to the last action and the second to last state of the path.
-/
lemma cons_to_snoc {n} {pt : PlanningTask n} {a : Action n} {s1 s2 s3 : State n}
    (ha : a ∈ pt.actions) (succ : Successor a s1 s2) (π : Path pt s2 s3) :
    ∃ s2' a', ∃ (ha' : a' ∈ pt.actions) (π' : Path pt s1 s2') (succ' : Successor a' s2' s3),
    cons a s2 ha succ π = snoc a' s2' ha' π' succ' ∧ π.length = π'.length := by
  cases heq : π with
  | empty s2' =>
    use s1, a, ha, empty s1, succ
    simp [snoc, length]
  | @cons a' s1 s2' s2 ha' succ' π' =>
    -- For termination
    have : π'.length < π.length := by
      subst heq
      simp [length]
    obtain ⟨s2'', a'', ha'', π'', succ'', heq, heq'⟩ := cons_to_snoc ha' succ' π'
    use s2'', a'', ha'', cons a s2 ha succ π'', succ''
    simp only [length, Nat.add_right_cancel_iff]
    rw [heq, heq']
    simp [snoc]

/--
Allows to perform cases with `Path.empty` and `Path.snoc` instead of `Path.empty` and `Path.cons`.
-/
lemma snocCases {n : ℕ} {pt : PlanningTask n}
    {motive : (s s' : State n) → Path pt s s' → Prop}
    {s s' : State n} (π : Path pt s s')
    (empty : (s : State n) → motive s s (Path.empty s))
    (snoc : (a : Action n) → {s1 : State n} → (s2 : State n) → {s3 : State n} →
      (ha : a ∈ pt.actions) → (π' : Path pt s1 s2) → (succ : Successor a s2 s3) →
        motive s1 s3 (snoc a s2 ha π' succ)) :
    motive s s' π :=
  match π with
  | .empty s => empty s
  | cons a s2 ha succ π =>
    have ⟨s2', a', ha', π', succ', heq_cons, heq_length⟩ := cons_to_snoc ha succ π
    by
    rw [heq_cons]
    apply snoc

/-! ### Mem -/

/-- A state `s` is a member of a path `π` if `π` traverses through `s`. -/
def Mem {n} {pt : PlanningTask n} {s1 s2} (s : State n) : (π : Path pt s1 s2) → Prop
  | empty s' => s = s'
  | cons _ _ _ _ π => s = s1 ∨ Mem s π

instance {n} {pt : PlanningTask n} {s1 s2} : Membership (State n) (Path pt s1 s2) where
  mem π s := Path.Mem s π

@[simp]
def mem_eq {n : ℕ} {pt : PlanningTask n} {s1 s2 : State n} (π : Path pt s1 s2) (s : State n) :
    Mem s π = (s ∈ π) := (rfl)

@[simp]
lemma mem_empty {n} {pt : PlanningTask n} {s s' : State n} : s ∈ @Path.empty _ pt s' ↔ s = s' := by
  rw [← mem_eq]; rfl

@[simp]
lemma mem_cons {n : ℕ} {pt : PlanningTask n} {a s1 s2 s3} {ha : a ∈ pt.actions}
    {succ : Successor a s1 s2} {π : Path pt s2 s3} {s} :
    s ∈ cons a s2 ha succ π ↔ s = s1 ∨ s ∈ π := by
  rw [← mem_eq]; rfl

@[simp]
lemma mem_snoc {n : ℕ} {pt : PlanningTask n} {a s1 s2 s3} {ha : a ∈ pt.actions}
    {π : Path pt s1 s2} {succ : Successor a s2 s3} {s} :
    s ∈ snoc a s2 ha π succ ↔ s = s3 ∨ s ∈ π := by
  induction π with
  | empty s1 =>
    simp only [snoc, mem_cons, mem_empty]
    tauto
  | @cons a' s1 s2 s2' ha' succ' π ih =>
    simp only [snoc, mem_cons]
    rw [ih]
    tauto

lemma first_mem {n} {pt : PlanningTask n} {s1 s2} (π : Path pt s1 s2) : s1 ∈ π := by
  cases π
  all_goals simp

lemma last_mem {n} {pt : PlanningTask n} {s1 s2} (π : Path pt s1 s2) : s2 ∈ π := by
  induction π with
  | empty s => simp
  | @cons a s1 s2 s3 ha succ π ih =>
    simp [mem_cons, ih]

/-! ### append -/

/--
Given a path form a `s1` to `s2` and a path from `s2` to `s3`, we obtain a path from `s1` to `s3`.
-/
def append {n} {pt : PlanningTask n} {s1 s2 s3} : Path pt s1 s2 → Path pt s2 s3 → Path pt s1 s3
  | empty s, π => π
  | cons a s2' ha succ π', π => cons a s2' ha succ (append π' π)

instance {n} {pt : PlanningTask n} {s1 s2 s3} :
  HAppend (Path pt s1 s2) (Path pt s2 s3) (Path pt s1 s3) where
  hAppend := append

@[simp]
lemma append_eq {n} {pt} {s1 s2 s3 : State n} (π₁ : Path pt s1 s2) (π₂ : Path pt s2 s3) :
    π₁.append π₂ = π₁ ++ π₂ := (rfl)

lemma mem_append {n} {pt : PlanningTask n} {s1 s2 s3} (π₁ : Path pt s1 s2) (π₂ : Path pt s2 s3) :
    ∀ s, s ∈ (π₁ ++ π₂) ↔ s ∈ π₁ ∨ s ∈ π₂ := by
  induction π₁ with
  | empty =>
    simp only [← append_eq, append, mem_empty, iff_or_self, forall_eq, first_mem]
  | cons =>
    simp_all only [← append_eq, append, mem_cons]
    tauto

/-! ### split -/

/--
If a state `s` lies on a path `π` from `s1` to `s2`, then there is a path from the `s1` to `s` and
a path from `s` to `s2`. -/
lemma split {n} {pt : PlanningTask n} {s1 s2 s} (π : Path pt s1 s2) (h : s ∈ π) :
    Nonempty (Path pt s1 s × Path pt s s2) := by
  cases π with
  | empty s =>
    simp only [mem_empty] at h
    subst h
    use Path.empty s, Path.empty s
  | cons a s3 ha succ π =>
    simp only [mem_cons] at h
    rcases h with rfl | h
    · use Path.empty s, cons a s3 ha succ π
    · obtain ⟨π₁, π₂⟩ := split π h
      use cons a s3 ha succ π₁, π₂

end Path

/-! ## Reachablility, Plans and Unsolvability -/

/--
A state `s'` is reachable from `s` if there is a path from `s` to `s'`.
This is the `Prop` version of `Path`.
-/
abbrev Reachable {n} (pt : PlanningTask n) (s s' : State n) : Prop :=
  Nonempty (Path pt s s')

lemma reachable_self {n pt} : ∀ s : State n, Reachable pt s s := by
  intro s
  simp only [Reachable]
  constructor
  exact Path.empty s

/-- A plan for a state `s` for a planning task `pt` is a path from `s` to a goal state of pt. -/
structure Plan {n} (pt : PlanningTask n) (s : State n) where
  /-- The goal state in `pt`. -/
  last : State n
  /-- The path from `s` to the goal state. -/
  path : Path pt s last
  /-- The proof that `last` is a goal state. -/
  goal : pt.GoalState last

/-- A state is unsolvable if there is no plan for that state. -/
abbrev UnsolvableState {n} (pt : PlanningTask n) (s : State n):=
  IsEmpty (Plan pt s)

/-- A planning task is unsolvable if the initial state is unsolvable. -/
abbrev Unsolvable {n} (pt : PlanningTask n) :=
  UnsolvableState pt pt.init


/-! ## progression and regression -/

/-- The progression of a set of states `S` by an action `a`. -/
def progression' {n} (_ : PlanningTask n) (S : States n) (a : Action n) : States n :=
  { s | ∃ s' ∈ S, Successor a s' s }

/-- The progression of a set of states `S` by a set of actions `A`. -/
def progression {n} (pt : PlanningTask n) (S : States n) (A : Actions n) : States n :=
  { s | ∃ a ∈ A, s ∈ progression' pt S a }

/-- The regression of a set of states `S` by an action `a`. -/
def regression' {n} (_ : PlanningTask n) (S : States n) (a : Action n) : States n :=
  { s | ∃ s' ∈ S, Successor a s s' }

/-- The regression of a set of states `S` by a set of actions `A`. -/
def regression {n} (pt : PlanningTask n) (S : States n) (A : Actions n) : States n :=
  { s | ∃ a ∈ A, s ∈ regression' pt S a }

lemma mem_progression' {n} {pt : PlanningTask n} {a S} :
    ∀ s : State n, s ∈ pt.progression' S a ↔ ∃ s' ∈ S, Successor a s' s := by
  simp only [progression', Set.mem_setOf_eq, implies_true]

lemma mem_progression {n} {pt : PlanningTask n} {A S} :
    ∀ s : State n, s ∈ pt.progression S A ↔ ∃ a ∈ A, ∃ s' ∈ S, Successor a s' s := by
  simp [progression, mem_progression']

lemma mem_progression_of_successor {n} {pt : PlanningTask n} {S s s' A a}
    (hs : s ∈ S) (ha : a ∈ A) (h : Successor a s s') : s' ∈ pt.progression S A := by
  rw [mem_progression]
  use a, ha, s

lemma progression_union_states {n} {pt : PlanningTask n} {S1 S2 A} :
    pt.progression (S1 ∪ S2) A = pt.progression S1 A ∪ pt.progression S2 A := by
  grind only [mem_progression, Set.mem_union]

lemma progression_union_actions {n} {pt : PlanningTask n} {S A1 A2} :
    pt.progression S (A1 ∪ A2) = pt.progression S A1 ∪ pt.progression S A2 := by
  ext s
  simp [mem_progression]
  grind

lemma progression_monotone_states {n} {pt : PlanningTask n} {A} :
    Monotone (pt.progression · A) := by
  intro S1 S2 hS s hs
  simp_all only [Set.le_eq_subset, mem_progression]
  obtain ⟨a, ha, s', hs', succ⟩ := hs
  use a, ha, s', hS hs'

lemma progression_monotone_actions {n} {pt : PlanningTask n} {S} : Monotone (pt.progression S) := by
  intro A1 A2 hA s hs
  simp_all only [Set.le_eq_subset, mem_progression]
  obtain ⟨a, ha, s', hs', succ⟩ := hs
  use a, hA ha, s'

lemma mem_regression' {n} {pt : PlanningTask n} {a S} :
    ∀ s : State n, s ∈ pt.regression' S a ↔ ∃ s' ∈ S, Successor a s s' := by
  simp only [regression', Set.mem_setOf_eq, implies_true]

lemma mem_regression {n} {pt : PlanningTask n} {S A} :
    ∀ s : State n, s ∈ pt.regression S A ↔ ∃ a ∈ A, ∃ s' ∈ S, Successor a s s' := by
  simp [regression, mem_regression']

lemma mem_regression_of_successor {n} {pt : PlanningTask n} {S s s' A a}
    (hs : s ∈ S) (ha : a ∈ A) (h : Successor a s' s) : s' ∈ pt.regression S A := by
  rw [mem_regression]
  use a, ha, s

lemma sub_progression_iff_sub_regression {n} {pt : PlanningTask n} {S S' A} :
    pt.progression S A ⊆ S' ↔ pt.regression S'ᶜ A ⊆ Sᶜ := by
  constructor
  · intro h1 s hs_regr
    obtain ⟨a, ha, s', hs', succ⟩ := (mem_regression s).1 hs_regr
    simp only [Set.mem_compl_iff] at ⊢ hs'
    by_contra hs1
    apply hs'
    apply h1
    rw [mem_progression]
    use a, ha, s
  · intro h1 s' hs'_progr
    obtain ⟨a, ha, s, hs, succ⟩ := (mem_progression s').1 hs'_progr
    by_contra hs'
    apply Set.mem_compl at hs'
    have hs_regr : s ∈ pt.regression S'ᶜ A := by
      rw [mem_regression]
      use a, ha, s'
    have : s ∈ Sᶜ := h1 hs_regr
    simp_all

end STRIPS.PlanningTask
