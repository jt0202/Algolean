import Mathlib.Order.Defs.LinearOrder
import Algolean.QueryModel
/-!
  An implementation of heaps.
-/

variable {α β : Type} [LinearOrder β]

inductive Strategy
| max
| min

def heapCompare (s : Strategy) (x y : β) : Bool :=
  match s with
  | .max => y ≤ x
  | .min => x ≤ y

@[simp, grind =]
lemma heapCompare_refl {s : Strategy} {x : β} :
    heapCompare s x x = true := by
  simp [heapCompare]
  cases s <;> rfl

def isHeapAt (l : List (α × β)) (i : ℕ) (hi : i < l.length) (s : Strategy) : Bool :=
  if h₁ : 2*i+1 < l.length then
    if h₂ : 2*i+2 < l.length then
      heapCompare s l[i].2 l[2*i+1].2 ∧ heapCompare s l[i].2 l[2*i+2].2
    else heapCompare s l[i].2 l[2*i+1].2
  else true

def isHeap (l : List (α × β)) (s : Strategy) := ∀ (i : ℕ) (hi : i < l.length), isHeapAt l i hi s

def heapifyUp (l : List (α × β)) (s : Strategy) (i : ℕ) (hi : i < l.length) : List (α × β) :=
  if i = 0
  then l
  else
    let parent := (i-1)/2
    have hp : parent < l.length := by grind
    if heapCompare s l[i].2 l[parent].2
    then l
    else heapifyUp (l.swap i parent) s parent (by simp[hp])

private def swapTarget (l : List (α × β)) (s : Strategy) (i : ℕ) (hi : i < l.length) : ℕ :=
  let child1 := 2*i+1
  let child2 := 2*i+2
  if h₁ : child1 < l.length then
    if h₂ : child2 < l.length then
      if heapCompare s l[child1].2 l[child2].2 then
        if heapCompare s l[i].2 l[child1].2 then
          child1
        else
          i
      else
        if heapCompare s l[i].2 l[child2].2 then
          child2
        else
          i
    else
      if heapCompare s l[i].2 l[child1].2 then
        child1
      else
        i
  else
    i

lemma swapTarget_semantics (l : List (α × β)) (s : Strategy) (i j : ℕ) (hi : i < l.length) :
  j = swapTarget l s i hi → ∃ (h : j < l.length), (j = i ∨ j = 2*i+1 ∨ j=2*i+2) ∧
    heapCompare s l[j].2 l[i].2 ∧
      ∀ (h₁ : 2*i+1 < l.length), heapCompare s l[j].2 l[2*i+1].2 ∧
        ∀ (h₁ : 2*i+2 < l.length), heapCompare s l[j].2 l[2*i+2].2 := by
  cases s with
  | min =>
    simp [swapTarget, heapCompare]
    split_ifs


def heapifyDown (l : List (α × β)) (s : Strategy) (i : ℕ) (hi : i < l.length) : List (α × β) :=
  let (eq := hj) j := swapTarget l s i hi
  if i = j
  then l
  else
    heapifyDown (l.swap i j) s j (by apply swapTarget_semantics at hj; grind[swapTarget_semantics])
termination_by l.length - i
decreasing_by
  apply swapTarget_semantics at hj;
  grind

def insert (l : List (α × β)) (s : Strategy) (a : α) (b : β) : List (α × β) :=
  heapifyUp (l.concat (a,b)) s l.length (by simp)

def peek (l : List (α × β)) : Option (α × β) := l[0]?

def get (l : List (α × β)) (s : Strategy) : Option (α × β) × List (α × β) :=
  let top := peek l
  if hl: 1 < l.length
  then
    ⟨top, heapifyDown (l.swap 0 (l.length - 1)|>.eraseIdx (l.length - 1)) s 0 (by grind)⟩
  else
    ⟨top, []⟩

def update (l : List (α × β)) (s : Strategy) (i : ℕ) (hi : i < l.length) (b : β) : List (α × β) :=
  if heapCompare s l[i].2 b
  then heapifyDown (l.modify i (fun _ => (l[i].1, b))) s i (by simp[hi])
  else heapifyUp (l.modify i (fun _ => (l[i].1, b))) s i (by simp[hi])

variable {l : List (α × β)} {s : Strategy} {i : ℕ} (hi : i < l.length)

@[simp, grind =]
lemma length_heapifyDown : (heapifyDown l s i hi).length = l.length := by
  induction h : l.length - i using Nat.strongRecOn generalizing l i with
  | ind n ih =>
    unfold heapifyDown
    simp
    split_ifs
    · rfl
    · have : (l.swap i (swapTarget l s i hi)).length = l.length := by
        simp
      rw [← this]
      apply ih


@[simp, grind =]
lemma length_heapifyUp : (heapifyUp l s i hi).length = l.length := by
  induction i using Nat.strongRecOn generalizing l with
  | ind n ih =>
    unfold heapifyUp
    simp
    split_ifs
    all_goals grind
