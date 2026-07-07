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
    simp only [Fin.getElem_fin, Set.ext_iff, Set.mem_setOf_eq, Bool.coe_iff_coe, Fin.forall_iff,
      mk.injEq, BitVec.eq_of_getElem_eq_iff, imp_self]

lemma mem_iff {n i} {V : VarSet n} : i ∈ V ↔ V.toBitVec[i] := by
  unfold SetLike.instMembership
  simp only [SetLike.coe, Set.mem_setOf_eq]

instance {n} {i : Fin n} {V : VarSet n} : Decidable (i ∈ V) := by
  rw [mem_iff]
  infer_instance

@[reducible]
instance {n} : HasSubset (VarSet n) where
  Subset V V' := ∀ i ∈ V, i ∈ V'

lemma subset_def {V V' : VarSet n} : V ⊆ V' ↔ ∀ i ∈ V, i ∈ V' := by
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
lemma mem_insert {n} {V : VarSet n} {i j} : j ∈ (V.insert i) ↔ j ∈ V ∨ j = i := by
  simp [insert, mem_iff]
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

/-- Return the `VarSet` containing all variables in the given list. -/
def ofList {n} (l : List (Fin n)) : VarSet n :=
  l.foldr insert ∅

@[simp]
lemma mem_ofList {n} {l : List (Fin n)} {i} : i ∈ ofList l ↔ i ∈ l := by
  simp only [ofList]
  induction l with
  | nil => simp only [List.foldr_nil, mem_empty, List.not_mem_nil]
  | cons j l ih =>
    grind only [List.mem_cons, = List.foldr_cons, mem_insert]

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

/--
Folds a function over all variables in `V` with starting value `init`. The variables are combined
in increasing order.
-/
def foldl {α n} (f : α → Fin n → α) (init : α) (V : VarSet n) : α :=
  Fin.foldl n (fun a i ↦ if i ∈ V then f a i else a) init

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

instance {n} : Std.ToFormat (VarSet n) where
  format V :=
    let enum := V.foldl (fun f i ↦ if f.isEmpty then toString i else f!"{f}, {i}") .nil
    Std.Format.bracketFill "{" enum "}"

instance {n} : ToString (VarSet n) where
  toString V := (Std.ToFormat.format V).pretty

end STRIPS.VarSet
