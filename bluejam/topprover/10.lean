/-
Require Import List.

Fixpoint prefix_sum sum l :=
  match l with
  | nil => sum :: nil
  | head :: tail => sum :: prefix_sum (sum + head) tail
  end.

Fixpoint plus_list l1 l2 :=
  match (l1, l2) with
  | (nil, _) => nil
  | (_, nil) => nil
  | (h1 :: t1, h2 :: t2) => (h1 + h2) :: plus_list t1 t2
  end.

Definition task :=
  forall l1 l2,
    prefix_sum 0 (plus_list l1 l2) =
    plus_list (prefix_sum 0 l1) (prefix_sum 0 l2).
-/

def prefix_sum : nat → list nat → list nat
| sum list.nil := sum :: list.nil
| sum (head :: tail) := sum :: prefix_sum (sum + head) tail

def plus_list : list nat → list nat → list nat
| list.nil _ := list.nil
| _ list.nil := list.nil
| (h1 :: t1) (h2 :: t2) := (h1 + h2) :: plus_list t1 t2

lemma nil_plus_list : ∀ l : list nat, plus_list list.nil l = list.nil :=
by intro l; induction l; simp [plus_list]

lemma plus_list_comm : ∀ l1 l2 :list nat, plus_list l1 l2 = plus_list l2 l1 :=
begin
    intro l1, induction l1,
        intro l2, induction l2; simp [plus_list],
    intro l2, induction l2,
        simp [plus_list],
    simp [plus_list, l1_ih],
end

lemma plus_list_nil (l : list nat) : plus_list l list.nil = list.nil :=
by simp [plus_list_comm l, nil_plus_list]

lemma plus_list_prefix_sum : ∀ h1 h2 : nat, ∀ l1 l2 :list nat, plus_list (prefix_sum h1 l1) (prefix_sum h2 l2)
    = prefix_sum (h1 + h2) (plus_list l1 l2) :=
begin
    intros,
    revert l2 h1 h2,
    induction l1,
        simp [prefix_sum, nil_plus_list],
        intro l2, induction l2,
            simp [prefix_sum],
            simp [plus_list],
            intros, trivial,
        simp [prefix_sum],
        simp [plus_list],
        simp [nil_plus_list],
        intros, trivial,
    intro l2, induction l2,
        simp [prefix_sum, nil_plus_list, plus_list_nil],
        simp [plus_list, plus_list_nil],
        intros, trivial,
    intros,
    simp [prefix_sum],
    simp [plus_list, prefix_sum],
    simp [l1_ih],
end

example : ∀ l1 l2 : list nat, prefix_sum 0 (plus_list l1 l2) = plus_list (prefix_sum 0 l1) (prefix_sum 0 l2) :=
begin
    simp [plus_list_prefix_sum],
    intros, trivial,
end
