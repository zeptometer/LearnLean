open classical


variables p q r s : Prop


-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
   iff.intro
       (assume h: p ∧ q, show q ∧ p, from and.intro h.right h.left)
       (assume h: q ∧ p, show p ∧ q, from and.intro h.right h.left)
     


lemma swap_or: p ∨ q → q ∨ p :=
   assume hpq: p ∨ q,
   show q ∨ p, from or.elim hpq
       (assume hp: p, or.intro_right q hp)
       (assume hq: q, or.intro_left p hq)


example : p ∨ q ↔ q ∨ p :=
  iff.intro
      (assume h: p ∨ q, show q ∨ p, from swap_or p q h)
      (assume h: q ∨ p, show p ∨ q, from swap_or q p h)


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro
       (
           assume h: (p ∧ q) ∧ r,
           have hpq: (p ∧ q), from h.left,
           have hqr: (q ∧ r), from and.intro hpq.right h.right,
           and.intro hpq.left hqr
       )
       (
           assume h: p ∧ (q ∧ r),
           have hqr: (q ∧ r), from h.right,
           and.intro (and.intro h.left hqr.left) hqr.right
       )




-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
   have hlr: p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r), from (
       assume h: p ∧ (q ∨ r),
       or.elim
           h.right
           (
               assume hq: q,
               have hpq: p ∧ q, from and.intro h.left hq,
               or.intro_left (p ∧ r) hpq
           )
           (
               assume hr: r,
               have hpr: p ∧ r, from and.intro h.left hr,
               or.intro_right (p ∧ q) hpr
           )
   ),
   have hrl: (p ∧ q) ∨ (p ∧ r) →  p ∧ (q ∨ r), from (
       assume h: (p ∧ q) ∨ (p ∧ r),
       or.elim
           h
           (
               assume hpq: p ∧ q,
               have hqr: q ∨ r, from or.intro_left r hpq.right,
               and.intro hpq.left hqr
           )
           (
               assume hpr: p ∧ r,
               have hqr: q ∨ r, from or.intro_right q hpr.right,
               and.intro hpr.left hqr
           )
   ),
   iff.intro hlr hrl


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
   iff.intro
       (
           assume h: p ∨ (q ∧ r),
           or.elim
               h
               (
                   assume hp:p,
                   have hpq: p ∨ q, from or.intro_left q hp,
                   have hpr: p ∨ r, from or.intro_left r hp,
                   and.intro hpq hpr
               )
               (
                   assume hqr: q ∧ r,
                   have hpq: p ∨ q, from or.intro_right p hqr.left,
                   have hpr: p ∨ r, from or.intro_right p hqr.right,
                   and.intro hpq hpr
               )
       )
       (
           assume h: (p ∨ q) ∧ (p ∨ r),
           have hpq: p ∨ q, from h.left,
           have hpr: p ∨ r, from h.right,
           or.elim hpq
               (assume hp: p, or.intro_left (q ∧ r) hp)
               (
                   assume hq: q,
                   or.elim hpr
                       (assume hp: p, or.intro_left (q ∧ r) hp)
                       (
                           assume hr: r,
                           have hqr: q ∧ r, from and.intro hq hr,
                           or.intro_right p hqr
                       )
               )
       )




-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
   have hlr: (p → (q → r)) →  (p ∧ q → r), from (  
             assume h: p → q → r,
       assume hpq: p ∧ q,
       (h hpq.left) hpq.right
   ),
   have hrl: (p ∧ q → r) → (p → (q → r)), from (
       assume h: (p ∧ q → r),
       assume hp: p,
       assume hq: q,
       h (and.intro hp hq)
   ),
   iff.intro hlr hrl


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
   have hlr: ((p ∨ q) → r) → (p → r) ∧ (q → r), from (
       assume h: ((p ∨ q) → r),
       have hpr: (p → r), from (
           assume hp: p,
           have hpq: p ∨ q, from or.intro_left q hp,
           h hpq
       ),
       have hqr: (q → r), from (
           assume hq: q,
           have hpq: p ∨ q, from or.intro_right p hq,
           h hpq
       ),
       and.intro hpr hqr
   ),
   have hrl: (p → r) ∧ (q → r) → ((p ∨ q) → r), from (
       assume hp: (p → r) ∧ (q → r),
       assume hpq: p ∨ q,
       or.elim hpq hp.left hp.right
   ),
   iff.intro hlr hrl


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
   iff.intro
       (
           assume h: ¬ (p ∨ q),
           have hnp: ¬ p, from (assume hp: p, absurd (or.intro_left q hp) h),
           have hnq: ¬ q, from (assume hq: q, absurd (or.intro_right p hq) h),
           and.intro hnp hnq
       )
       (
           assume h: ¬ p ∧ ¬ q,
           assume hpq: p ∨ q,
           or.elim hpq
               (assume hp: p, absurd hp h.left)
               (assume hq: q, absurd hq h.right)
       )


example : ¬p ∨ ¬q → ¬(p ∧ q) :=
   assume h: ¬ p ∨ ¬ q,
   assume hpq: p ∧ q,
   or.elim h
       (assume hnp: ¬ p, absurd hpq.left hnp)
       (assume hnq: ¬ q, absurd hpq.right hnq)


example : ¬(p ∧ ¬p) := assume h: p ∧ ¬ p, absurd h.left h.right
example : p ∧ ¬q → ¬(p → q) :=
   assume h: p ∧ ¬ q,
   assume hpq: p → q,
   absurd (hpq h.left) h.right


example : ¬p → (p → q) :=
   assume hnp: ¬ p,
   assume hp: p,
   absurd hp hnp


example : (¬p ∨ q) → (p → q) :=
   assume h: ¬ p ∨ q,
   or.elim h
       (assume hnp: ¬ p, assume hp: p, absurd hp hnp)
       (assume hq: q, assume hp: p, hq)
example : p ∨ false ↔ p := iff.intro
   (
       assume h: p ∨ false,
       or.elim h
           (assume hp: p, hp)
           (false.elim)
   )
   (assume p, or.intro_left false p)


example : p ∧ false ↔ false := iff.intro
   (assume h: p ∧ false, h.right)
   (false.elim)


example : ¬(p ↔ ¬p) :=
   assume h: (p ↔ ¬ p),
   have hnp: ¬ p, from (
       assume hp: p,
       absurd hp (h.mp hp)
   ),
   have hp: p, from h.mpr hnp,
   absurd hp (h.mp hp)
example : (p → q) → (¬q → ¬p) :=
   assume h: p → q,
   assume hnq: ¬ q,
   assume hp: p,
   absurd (h hp) hnq
