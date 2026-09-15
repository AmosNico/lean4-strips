module

public import Mathlib.Data.SetLike.Basic
import Batteries.Data.BitVec.Lemmas

public section

namespace STRIPS

/-!
# Sets of Variables

This file implements set of variables with the aim to be both easy to work with and effient at
runtime.
-/

/-! ## Sets of variables -/

/-- A set of variables of type `Fin n`, where `n` is the number of variables -/
structure VarSet (n : ℕ) where
  /-- The bitvector internally representing the set of variables. -/
  toBitVec : BitVec n
deriving DecidableEq

namespace VarSet

instance {n} : SetLike (VarSet n) (Fin n) where
  coe V := { i | V.toBitVec[i] }

  coe_injective := by
    rintro ⟨V⟩ ⟨V'⟩
    simp only [Fin.getElem_fin, Set.ext_iff, Set.mem_ofPred, Bool.coe_iff_coe, Fin.forall_iff,
      mk.injEq, BitVec.eq_of_getElem_eq_iff, imp_self]

lemma mem_iff {n i} {V : VarSet n} : i ∈ V ↔ V.toBitVec[i] := by
  unfold SetLike.instMembership
  simp only [SetLike.coe, Set.mem_ofPred]

instance {n} {i : Fin n} {V : VarSet n} : Decidable (i ∈ V) :=
  decidable_of_iff' V.toBitVec[i] mem_iff

@[reducible]
instance {n} : HasSubset (VarSet n) where
  Subset V V' := ∀ i ∈ V, i ∈ V'

instance {n} {V V' : VarSet n} : Decidable (V ⊆ V') :=
  inferInstanceAs <| Decidable <| ∀ i ∈ V, i ∈ V'

@[ext, grind ext]
lemma ext {n} {V V' : VarSet n} : (∀ i, i ∈ V ↔ i ∈ V') → V = V' :=
  SetLike.ext

lemma subset_iff {n} {V V' : VarSet n} : V ⊆ V' ↔ ∀ i ∈ V, i ∈ V' := by
  rfl

instance {n} : EmptyCollection (VarSet n) where
  emptyCollection := ⟨BitVec.zero n⟩

@[simp]
lemma mem_empty {n i} : i ∉ (∅ : VarSet n) := by
  unfold instEmptyCollection
  simp [mem_iff]

/-- Return the `VarSet` containing all variables in `V` and the variable `i`. -/
def insert {n} (i : Fin n) (V : VarSet n) : VarSet n :=
  ⟨V.toBitVec ||| BitVec.twoPow n i⟩

@[simp]
lemma mem_insert {n} {V : VarSet n} {i j} : j ∈ V.insert i ↔ j ∈ V ∨ j = i := by
  simp [insert, mem_iff]
  grind

/-- Return the `VarSet` containing all variables in `V` except the variable `i`. -/
def erase {n} (i : Fin n) (V : VarSet n) : VarSet n :=
  ⟨V.toBitVec &&& ~~~BitVec.twoPow n i⟩

@[simp]
lemma mem_erase {n} {V : VarSet n} {i j} : j ∈ V.erase i ↔ j ∈ V ∧ j ≠ i := by
  simp [erase, mem_iff]
  grind

/-- Return the `VarSet` containing all variables. -/
def all {n} : VarSet n := ⟨BitVec.allOnes n⟩

@[simp]
lemma mem_all {n} {i : Fin n} : i ∈ all := by
  simp only [all, mem_iff, Fin.getElem_fin, BitVec.getElem_allOnes]

/-- Return the `VarSet` containing all variables `i` for which `f i` is true. -/
def ofFn {n} (f : Fin n → Bool) : VarSet n :=
  ⟨BitVec.ofFnLE f⟩

@[simp]
lemma mem_ofFn {n} {f : Fin n → Bool} {i} : i ∈ ofFn f ↔ f i := by
  simp only [ofFn, mem_iff, Fin.getElem_fin, BitVec.getElem_ofFnLE, Fin.eta]

instance {n} : Union (VarSet n) where
  union V V' := ⟨V.toBitVec ||| V'.toBitVec⟩

@[simp]
lemma mem_union {n} {V V' : VarSet n} {i} : i ∈ V ∪  V' ↔ i ∈ V ∨ i ∈ V' := by
  unfold instUnion
  simp [mem_iff]

@[simp]
lemma empty_union {n} {V : VarSet n} : ∅ ∪ V = V := by
  simp only [SetLike.ext_iff, mem_union, mem_empty, false_or, implies_true]

@[simp]
lemma union_empty {n} {V : VarSet n} : V ∪ ∅ = V := by
  simp only [SetLike.ext_iff, mem_union, mem_empty, or_false, implies_true]

instance {n} : Inter (VarSet n) where
  inter V V' := ⟨V.toBitVec &&& V'.toBitVec⟩

@[simp]
lemma mem_inter {n} {V V' : VarSet n} {i} : i ∈ V ∩ V' ↔ i ∈ V ∧ i ∈ V' := by
  unfold instInter
  simp [mem_iff]

@[simp]
lemma empty_inter {n} {V : VarSet n} : ∅ ∩ V = ∅ := by
  simp only [SetLike.ext_iff, mem_inter, mem_empty, false_and, implies_true]

@[simp]
lemma inter_eq_empty_iff {n} {V V' : VarSet n} : V ∩ V' = ∅ ↔ ∀ i ∈ V, i ∉ V' := by
  simp only [SetLike.ext_iff, mem_inter, mem_empty, iff_false, not_and]

instance {n} : Compl (VarSet n) where
  compl V := ⟨~~~V.toBitVec⟩

@[simp]
lemma mem_compl {n} {V : VarSet n} {i} : i ∈ Vᶜ ↔ i ∉ V := by
  unfold instCompl
  simp [mem_iff]

instance {n} : SDiff (VarSet n) where
  sdiff V V' := ⟨V.toBitVec &&& ~~~V'.toBitVec⟩

@[simp]
lemma mem_diff {n} {V V' : VarSet n} {i} : i ∈ V \ V' ↔ i ∈ V ∧ i ∉ V' := by
  unfold instSDiff
  simp [mem_iff]

/-
The smallest variable in `V` which is larger then or equal to `i`.
Returns `none` if there is no such variable in `V`.
-/
/- TODO : replace by `Std.Iterator` instance
def next? {n} (V : VarSet n) (i : Fin n) : Option (Fin n) :=
  if h : i ∈ V then
    i
  else
    if h : i + 1 = n then
      none
    else
      V.next? ⟨i + 1, by omega⟩
termination_by n - i-/

/--
Returns the smallest variable in `V` larger then or equal to `i`.
Returns `none` if there is no such variable.
-/
-- TODO : replace by `Std.Iterator` instance
def next? {n} (V : VarSet n) (i : ℕ) : Option (Fin n) :=
  if h : i < n then
    if ⟨i, h⟩ ∈ V then
      some ⟨i, h⟩
    else
      V.next? (i + 1)
  else
    none

@[simp, grind .]
lemma next?_mem {n} {V : VarSet n} {i j} : V.next? i = some j → j ∈ V := by
  fun_induction next? <;> grind only

lemma le_of_next? {n} {V : VarSet n} {i j} : V.next? i = some j → i ≤ j := by
  fun_induction next? <;> grind only [= Lean.Grind.toInt_fin]

private def foldlAux {α n} (f : α → Fin n → α) (start : ℕ) (init : α) (V : VarSet n) : α :=
  match h : V.next? start with
  | none => init
  | some j =>
    have := le_of_next? h
    foldlAux f (j.val + 1) (f init j) V
termination_by n - start

private lemma foldlAux_induction {α n} {V : VarSet n} {motive : ℕ → α → Prop} {f start init}
    (hinit : motive start init)
    (hnext : ∀ j a i, V.next? j = some i → motive j a → motive (i + 1) (f a i))
    (hend : ∀ j a, V.next? j = none → motive j a → motive n a) :
    motive n (foldlAux f start init V) := by
  fun_induction foldlAux with
  | case1 start init h => exact hend start init h hinit
  | case2 start init j h1 h2 ih => exact ih (hnext _ _ _ h1 hinit)

def foldl {α n} (f : α → Fin n → α) (init : α) (V : VarSet n) : α :=
  match n with
  | 0 => init
  | _ + 1 => foldlAux f 0 init V

lemma foldl_induction {α n} {V : VarSet n} {motive : ℕ → α → Prop} {f : α → Fin n → α} {init : α}
    (hinit : motive 0 init)
    (hnext : ∀ j a i, V.next? j = some i → motive j a → motive (i + 1) (f a i))
    (hend : ∀ j a, V.next? j = none → motive j a → motive n a) :
    motive n (foldl f init V) :=
  match n with
  | 0 => hinit
  | _ + 1 => foldlAux_induction hinit hnext hend

/--
The smallest variable larger than `i` which is a member of `V`.
Returns `none` if no member of `V` is larger then `i`.
-/
-- TODO : replace by `Std.Iterator` instance
def next? {n} (V : VarSet n) (i : Fin n) : Option (Fin n) :=
  if h : i + 1 < n then
    let j : Fin n := ⟨i + 1, h⟩
    if j ∈ V then some j else V.next? j
  else
    none

@[simp, grind .]
lemma next?_mem {n} {V : VarSet n} {i j : Fin n} : V.next? i = j → j ∈ V := by
  fun_induction next? <;> grind only

@[simp, grind .]
lemma monotone_next? {n} {V : VarSet n} {i j : Fin n} : V.next? i = j → i < j := by
  fun_induction next? <;> grind only [= Lean.Grind.toInt_fin]

private def foldlAux {α n} (f : α → Fin n → α) (start : Fin n) (init : α) (V : VarSet n) : α :=
  match h : V.next? start with
  | none => init
  | some j =>
    have := monotone_next? h
    foldlAux f j (f init j) V
termination_by n - start

private lemma foldlAux_induction {α n} {V : VarSet n} {motive : ℕ → α → Prop} {f start init}
    (hinit : motive start.val init)
    (hnext : ∀ j a i, V.next? j = some i → motive (j + 1) a →  motive (i + 1) (f a i))
    (hend : ∀ j a, V.next? j = none → motive j a → motive n a) :
    motive n (foldlAux f start init V) := by
  fun_induction foldlAux with
  | case1 start init h => exact hend start init h hinit
  | case2 start init j h1 h2 ih =>
    apply ih

    simp only [foldl]
    cases n with
    | zero => exact hinit
    | succ n =>
      simp only
      sorry
    simp only [foldl]
    rcases V with ⟨V⟩
    induction V using BitVec.cons_induction with
    | nil =>
      simp only [BitVec.ofNat_eq_ofNat, Fin.foldl_zero]
      exact hinit
    | @cons n' b V ih =>
      simp only [mem_iff, Fin.getElem_fin, Fin.foldl_succ_last, Fin.val_last,
        Fin.val_castSucc] at *
      have h1 : ∀ i : Fin n', i.val ≠ n' := by omega
      split
      · simp only [BitVec.getElem_cons, h1, ↓reduceDIte]

        constructor
        · grind
        · rw [← or_assoc]
          apply Or.imp_left
          rintro ⟨i, h2, rfl⟩
          split at h2
          · grind
          · apply Or.inr
            use ⟨i.val, by omega⟩
            simp [h2]
      · simp only [BitVec.getElem_cons, h1, ↓reduceDIte, ih]
        constructor
        · grind
        · apply Or.imp_left
          rintro ⟨i, h2, rfl⟩
          split at h2
          · grind
          · use ⟨i.val, by omega⟩
            simp [h2]
      sorry

def foldl {α n} (f : α → Fin n → α) (init : α) (V : VarSet n) : α :=
  match n with
  | 0 => init
  | _ + 1 => foldl_aux f 0 init V

lemma foldl_induction {α n} {V : VarSet n} {motive : ℕ → α → Prop} {f : α → Fin n → α} {init : α}
    (hinit : motive 0 init)
    (hnext : ∀ j a i, motive j.val a → V.next? j = some i → motive (i + 1) (f a i))
    (hend : ∀ j a, motive j.val a → V.next? j = none → motive n a) :
    motive n (foldl f init V) := by
  simp only [foldl]
  cases n with
  | zero => exact hinit
  | succ n =>
    simp only
    sorry
  simp only [foldl]
  rcases V with ⟨V⟩
  induction V using BitVec.cons_induction with
  | nil =>
    simp only [BitVec.ofNat_eq_ofNat, Fin.foldl_zero]
    exact hinit
  | @cons n' b V ih =>
    simp only [mem_iff, Fin.getElem_fin, Fin.foldl_succ_last, Fin.val_last,
      Fin.val_castSucc] at *
    have h1 : ∀ i : Fin n', i.val ≠ n' := by omega
    split
    · simp only [BitVec.getElem_cons, h1, ↓reduceDIte]

      constructor
      · grind
      · rw [← or_assoc]
        apply Or.imp_left
        rintro ⟨i, h2, rfl⟩
        split at h2
        · grind
        · apply Or.inr
          use ⟨i.val, by omega⟩
          simp [h2]
    · simp only [BitVec.getElem_cons, h1, ↓reduceDIte, ih]
      constructor
      · grind
      · apply Or.imp_left
        rintro ⟨i, h2, rfl⟩
        split at h2
        · grind
        · use ⟨i.val, by omega⟩
          simp [h2]
    sorry

lemma foldl_induction {α n} {V : VarSet n} {motive : ℕ → α → Prop} {f : α → Fin n → α} {init : α}
    (hinit : motive 0 init)
    (hnext : ∀ j a i, motive j.val a → V.next? j = some i → motive (i + 1) (f a i)) :
    motive n (foldl f init V) := by
  simp only [foldl]
  rcases V with ⟨V⟩
  induction V using BitVec.cons_induction with
  | nil =>
    simp only [BitVec.ofNat_eq_ofNat, Fin.foldl_zero]
    exact hinit
  | @cons n' b V ih =>
    simp only [mem_iff, Fin.getElem_fin, Fin.foldl_succ_last, Fin.val_last,
      Fin.val_castSucc] at *
    have h1 : ∀ i : Fin n', i.val ≠ n' := by omega
    split
    · simp only [BitVec.getElem_cons, h1, ↓reduceDIte]

      constructor
      · grind
      · rw [← or_assoc]
        apply Or.imp_left
        rintro ⟨i, h2, rfl⟩
        split at h2
        · grind
        · apply Or.inr
          use ⟨i.val, by omega⟩
          simp [h2]
    · simp only [BitVec.getElem_cons, h1, ↓reduceDIte, ih]
      constructor
      · grind
      · apply Or.imp_left
        rintro ⟨i, h2, rfl⟩
        split at h2
        · grind
        · use ⟨i.val, by omega⟩
          simp [h2]
    sorry

/--
Folds a function over all variables in `V` with starting value `init`. The variables are combined
in increasing order.
-/
def foldl {α n} (f : α → Fin n → α) (init : α) (V : VarSet n) : α :=
  Fin.foldl n (fun a i ↦ if i ∈ V then f a i else a) init

lemma foldl_induction {α n} {V : VarSet n} {motive : ℕ → α → Prop} {f : α → Fin n → α} {init : α}
    (hinit : motive 0 init)
    (hmem : ∀ j a i (hi : i ∈ V) (hj : j ≤ i), motive j a → motive (i + 1) (f a i)) :
    motive n (foldl f init V) := by
  simp only [foldl]
  rcases V with ⟨V⟩
  induction V using BitVec.cons_induction with
  | nil =>
    simp only [BitVec.ofNat_eq_ofNat, Fin.foldl_zero]
    exact hinit
  | @cons n' b V ih =>
    simp only [mem_iff, Fin.getElem_fin, Fin.foldl_succ_last, Fin.val_last,
      Fin.val_castSucc] at *
    have h1 : ∀ i : Fin n', i.val ≠ n' := by omega
    split
    · simp only [BitVec.getElem_cons, h1, ↓reduceDIte]

      constructor
      · grind
      · rw [← or_assoc]
        apply Or.imp_left
        rintro ⟨i, h2, rfl⟩
        split at h2
        · grind
        · apply Or.inr
          use ⟨i.val, by omega⟩
          simp [h2]
    · simp only [BitVec.getElem_cons, h1, ↓reduceDIte, ih]
      constructor
      · grind
      · apply Or.imp_left
        rintro ⟨i, h2, rfl⟩
        split at h2
        · grind
        · use ⟨i.val, by omega⟩
          simp [h2]
    sorry

lemma foldl_induction {α n} {V : VarSet n} {motive : ℕ → α → Prop} {f : α → Fin n → α} {init : α}
    (hinit : motive 0 init)
    (hmem : ∀ j a i (hi : i ∈ V) (hj : j ≤ i), motive j a → motive (i + 1) (f a i)) :
    motive n (foldl f init V) := by
  simp only [foldl]
  rcases V with ⟨V⟩
  induction V using BitVec.cons_induction with
  | nil =>
    simp only [BitVec.ofNat_eq_ofNat, Fin.foldl_zero]
    exact hinit
  | @cons n' b V ih =>
    simp only [mem_iff, Fin.getElem_fin, Fin.foldl_succ_last, Fin.val_last,
      Fin.val_castSucc] at *
    have h1 : ∀ i : Fin n', i.val ≠ n' := by omega
    split
    · simp only [BitVec.getElem_cons, h1, ↓reduceDIte]

      constructor
      · grind
      · rw [← or_assoc]
        apply Or.imp_left
        rintro ⟨i, h2, rfl⟩
        split at h2
        · grind
        · apply Or.inr
          use ⟨i.val, by omega⟩
          simp [h2]
    · simp only [BitVec.getElem_cons, h1, ↓reduceDIte, ih]
      constructor
      · grind
      · apply Or.imp_left
        rintro ⟨i, h2, rfl⟩
        split at h2
        · grind
        · use ⟨i.val, by omega⟩
          simp [h2]
    sorry

lemma foldl_cons {α n} {V : VarSet n} {f : Fin n → α} {a as} :
    a ∈ V.foldl (fun a i ↦ f i :: a) as ↔ (∃ i ∈ V, a = f i) ∨ a ∈ as := by
  simp only [foldl]
  rcases V with ⟨V⟩
  induction V using BitVec.cons_induction with
  | nil => simp
  | @cons n' b V ih =>
    simp only [mem_iff, Fin.getElem_fin, Fin.foldl_succ_last, Fin.val_last,
      Fin.val_castSucc] at *
    have h1 : ∀ i : Fin n', i.val ≠ n' := by omega
    split
    · simp only [BitVec.getElem_cons, h1, ↓reduceDIte, List.mem_cons, ih]
      constructor
      · grind
      · rw [← or_assoc]
        apply Or.imp_left
        rintro ⟨i, h2, rfl⟩
        split at h2
        · grind
        · apply Or.inr
          use ⟨i.val, by omega⟩
          simp [h2]
    · simp only [BitVec.getElem_cons, h1, ↓reduceDIte, ih]
      constructor
      · grind
      · apply Or.imp_left
        rintro ⟨i, h2, rfl⟩
        split at h2
        · grind
        · use ⟨i.val, by omega⟩
          simp [h2]

/-- Return the `VarSet` containing the variables `f i` for every variable `i` in `V`. -/
-- TODO : can this be done more efficiently?
def map {n m} (V : VarSet n) (f : Fin n → Fin m) : VarSet m :=
  V.foldl (fun V' i ↦ V'.insert (f i)) ∅
  -- Fin.foldl n (fun V' i ↦ if i ∈ V then V'.insert (f i) else V') empty

lemma mem_map {n m} {V : VarSet n} {f : Fin n → Fin m} {i} :  i ∈ V.map f ↔ (∃ j ∈ V, i = f j) := by
  simp only [map, foldl, insert]
  rcases V with ⟨V⟩
  induction V using BitVec.cons_induction with
  | nil => simp
  | @cons n' b V ih =>
    simp only [mem_iff, Fin.getElem_fin, Fin.foldl_succ_last, Fin.val_last,
      Fin.val_castSucc] at *
    have h1 : ∀ i : Fin n', i.val ≠ n' := by omega
    split
    · simp only [BitVec.getElem_cons, h1, ↓reduceDIte, BitVec.getElem_or, BitVec.getElem_twoPow,
      Bool.or_eq_true, ih, decide_eq_true_eq]
      constructor
      · grind
      · rintro ⟨i, h2, rfl⟩
        split at h2
        · grind
        · apply Or.inl
          use ⟨i.val, by omega⟩
          simp [h2]
    · simp only [BitVec.getElem_cons, h1, ↓reduceDIte, ih]
      constructor
      · grind
      · rintro ⟨i, h2, rfl⟩
        split at h2
        · grind
        · use ⟨i.val, by omega⟩
          simp [h2]

/-- Return the `VarSet` containing all variables in the given list. -/
def ofList {n} (l : List (Fin n)) : VarSet n :=
  l.foldr insert ∅

@[simp]
lemma ofList_nil {n} : @ofList n [] = ∅ := by
  simp only [ofList, List.foldr_nil]

@[simp]
lemma ofList_cons {n} {l : List (Fin n)} {i} : ofList (i :: l) = (ofList l).insert i := by
  simp only [ofList, List.foldr_cons]

@[simp]
lemma mem_ofList {n} {l : List (Fin n)} {i} : i ∈ ofList l ↔ i ∈ l := by
  induction l with
  | nil => simp only [ofList_nil, mem_empty, List.not_mem_nil]
  | cons j l ih => grind only [ofList_cons, mem_insert, List.mem_cons]

/-- The list containing all variables in the given `VarSet`, in no particular order. -/
def toList {n} (V : VarSet n) : List (Fin n) :=
  V.foldl (Function.swap List.cons) []

@[simp]
lemma mem_toList {n} {V : VarSet n} : ∀ i, i ∈ V.toList ↔ i ∈ V := by
  simp only [toList, foldl_cons, exists_eq_right', List.not_mem_nil, or_false, implies_true]

lemma toList_nodup {n} {V : VarSet n} : V.toList.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  apply List.Pairwise.imp Fin.ne_of_gt



@[simp]
lemma ofList_cons {n} {l : List (Fin n)} {i} : ofList (i :: l) = (ofList l).insert i := by
  simp only [ofList, List.foldr_cons]

@[simp]
lemma mem_ofList {n} {l : List (Fin n)} {i} : i ∈ ofList l ↔ i ∈ l := by
  induction l with
  | nil => simp only [ofList_nil, mem_empty, List.not_mem_nil]
  | cons j l ih => grind only [ofList_cons, mem_insert, List.mem_cons]

instance {n} : Std.ToFormat (VarSet n) where
  format V :=
    let enum := V.foldl (fun f i ↦ if f.isEmpty then toString i else f!"{f}, {i}") .nil
    Std.Format.bracketFill "{" enum "}"

instance {n} : ToString (VarSet n) where
  toString V := (Std.ToFormat.format V).pretty

end STRIPS.VarSet
