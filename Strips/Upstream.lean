import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.List.Sort

lemma Array.lt_of_getElem?_eq_some {α a} {xs : Array α} {i : ℕ}
  (h : xs[i]? = some a) : i < xs.size := by
  apply Array.getElem_of_getElem? at h
  rcases h
  assumption

@[simp]
lemma Fintype.elems_eq_univ {α} [h : Fintype α] : h.elems = Finset.univ :=
  by
    ext a
    simp [Fintype.complete]

def Vector.elems {α} [h : Fintype α] [DecidableEq α] : (n : ℕ) → Finset (Vector α n)
| 0 => {#v[]}
| n + 1 => Finset.biUnion (elems n) fun v ↦ h.elems.image v.push

instance {α} [Fintype α] [DecidableEq α] {n} : Fintype (Vector α n) where

  elems := Vector.elems n

  complete :=
    by
      induction n with
      | zero => simp [Vector.elems]
      | succ n ih =>
        simp only [Vector.elems, Fintype.elems_eq_univ, Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_univ, true_and, Vector.forall_cons_iff]
        intro a v
        use v, ih v, a

/-- Variant of `Vector.mem_iff_getElem` using `Fin`. -/
lemma Vector.mem_iff_getElem' {α n} {a : α} {xs : Vector α n} :
  a ∈ xs ↔ ∃ i : Fin n, xs[i] = a :=
  by
    simp only [mem_iff_getElem, Fin.getElem_fin]
    constructor
    · rintro ⟨i, hi, h1⟩
      use ⟨i, hi⟩
    · grind only [usr Fin.isLt]

def List.productWith {α β γ} (f : α → β → γ) (as : List α) (bs : List β) : List γ :=
  List.map (fun (a, b) ↦ f a b) <| List.product as bs

def List.mulr {α β} (f : α → β → β) (init : β) : List (List α) → List β :=
  List.foldr (List.productWith f) [init]

def List.multiply {α} : List (List (List α)) → List (List α) :=
  List.mulr (· ++ ·) []

@[simp]
lemma List.multiply_nil {α} :
  multiply (α := α) [] = [[]] :=
  by
    simp [multiply, mulr]

@[simp]
lemma List.multiply_cons {α} {asss} {ass : List (List α)} :
  multiply (ass :: asss) = ass.flatMap (fun as ↦ (multiply asss).map (as ++ ·)) :=
  by
    simp [multiply, mulr, productWith, List.product.eq_1, List.map_flatMap]
    congr

lemma List.map_toFinset {α β} [DecidableEq α] [DecidableEq β] {f : α → β} {xs : List α} :
  (xs.map f).toFinset = xs.toFinset.image f := by
  ext b
  simp

lemma List.length_flatten_short {α} (ass : List (List α)) (h : ∀ as ∈ ass, as.length < 2) :
   ass.flatten.length ≤ ass.length :=
  by
    induction ass with
    | nil => simp
    | cons as ass ih => grind

@[simp]
lemma Set.inter_compl_subset_union_compl {α} {s1 s2 s3 s4 : Set α} :
  s1 ∩ s2ᶜ ⊆ s3 ∪ s4ᶜ ↔ s1 ∩ s4 ⊆ s3 ∪ s2 := by
  simp [Set.subset_def]
  grind

@[induction_eliminator, elab_as_elim]
theorem BitVec.cons_induction {motive : (w : Nat) → BitVec w → Prop} (nil : motive 0 .nil)
    (cons : ∀ {w : Nat} (b : Bool) (bv : BitVec w), motive w bv → motive (w + 1) (.cons b bv)) :
    ∀ {w : Nat} (x : BitVec w), motive w x := by
  intros w x
  induction w
  case zero =>
    simp only [BitVec.eq_nil x, nil]
  case succ wl ih =>
    rw [← cons_msb_setWidth x]
    apply cons
    apply ih
