namespace hidden7

universes u v

inductive list (α : Type u)
| nil {} : list
| cons : α → list → list

namespace list
variable {α : Type}

notation h :: t := cons h t

def append (s t : list α) : list α :=
list.rec t (λ x l u, x::u) s

notation s ++ t := append s t

theorem nil_append (t : list α) : nil ++ t = t := rfl
theorem cons_append (x : α) (s t : list α) :
    x :: s ++ t = x :: (s ++ t) := rfl

notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

section
    open nat
    #check [1, 2, 3, 4, 5]
    #check ([1,2,3,4,5] : list int)
end

-- exercise

theorem append_nil (t : list α) : t ++ nil = t :=
list.rec_on t
    (show (@nil α) ++ nil = nil, from rfl)
    (
        assume h,
        assume l,
        assume ih: l ++ nil = l,
        calc (h :: l) ++ nil = h :: (l ++ nil) : cons_append h l nil
        ... = h :: l : by rw ih
    )

theorem append_assoc (r s t : list α) : (r ++ s) ++ t = r ++ (s ++ t) :=
list.rec_on r
    (
        calc (nil ++ s) ++ t = s ++ t : by rw nil_append
        ... = nil ++ (s ++ t) : by rw nil_append
    )
    (
        assume h,
        assume l,
        assume ih: (l ++ s) ++ t = l ++ (s ++ t),
        calc (h :: l) ++ s ++ t = h :: (l ++ s) ++ t : by rw cons_append
        ... = h :: (l ++ s ++ t) : by rw cons_append
        ... = h :: (l ++ (s ++ t)) : by rw ih
        ... = (h :: l) ++ (s ++ t) : by rw cons_append
    )

def length : Π {α : Type u}, list α → ℕ :=
λ t l, list.rec_on l 0 (λ h x n, n + 1)

theorem append_length (s t : list α) : length (s ++ t) = length s + length t :=
list.rec_on s
    (
        show length (nil ++ t) = length nil + length t, from
        calc length (nil ++ t) = length t : by rw nil_append
        ... = 0 + length t : by rw zero_add
        ... = length nil + length t : rfl
    )
    (
        assume h,
        assume l,
        assume ih: length (l ++ t) = length l + length t,
        show length (h :: l ++ t) = length (h :: l) + length t, from
        calc length ((h :: l) ++ t) = length (h :: (l ++ t)) : by rw cons_append
        ... = length (l ++ t) + 1 : rfl
        ... = length l + length t + 1 : by rw ih
        ... = length l + 1 + length t : by simp
        ... = length (h :: l) + length t : by rw length
    )

def reverse (s : list α) : list α :=
list.rec_on s nil (λ h l t, t ++ [h])

example (h : α) (s : list α) : reverse (h :: s) = (reverse s) ++ [h] :=
rfl

example (t: list α) : length (reverse t) = length t :=
list.rec_on t
    (show length (reverse nil) = length nil, from rfl)
    (
        assume h,
        assume l : list α,
        assume ih : length (reverse l) = length l,
        show length (reverse (h :: l)) = length (h :: l), from
        calc length (reverse (h :: l))
            = length (reverse l ++ [h]) : rfl
        ... = length (reverse l) + length [h] : by rw append_length
        ... = length l + length [h] : by rw ih
    )

theorem reverse_append (s t : list α) : reverse (s ++ t) = reverse t ++ reverse s :=
list.rec_on s
    (
        show reverse (nil ++ t) = reverse t ++ reverse nil, from
        calc reverse (nil ++ t) = reverse t : by rw nil_append
        ... = reverse t ++ nil : by rw append_nil
        ... = reverse t ++ reverse nil : rfl
    )
    (
        assume h,
        assume l,
        assume ih : reverse (l ++ t) = reverse t ++ reverse l,
        show reverse ((h :: l) ++ t) = reverse t ++ reverse (h :: l), from
        calc reverse ((h :: l) ++ t)
            = reverse (h :: (l ++ t)) : by rw cons_append
        ... = reverse (l ++ t) ++ [h] : rfl
        ... = reverse t ++ reverse l ++ [h] : by rw ih
        ... = reverse t ++ (reverse l ++ [h]) : by rw append_assoc
        ... = reverse t ++ reverse (h :: l) : rfl
    )

example (t : list α) : reverse (reverse t) = t :=
list.rec_on t
    (show reverse (reverse nil) = nil, from rfl)
    (
        assume h,
        assume l : list α,
        assume ih : reverse (reverse l) = l,
        show reverse (reverse (h :: l)) = h :: l, from
        calc reverse (reverse (h :: l))
            = reverse (reverse l ++ [h]) : rfl
        ... = reverse [h] ++ reverse (reverse l) : by rw reverse_append
        ... = [h] ++ reverse (reverse l) : rfl
        ... = [h] ++ l : by rw ih
        ... = h :: l : by rw [append]
    )

end list

end hidden
