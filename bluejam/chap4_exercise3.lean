variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
  have ¬ shaves barber barber, from (
    assume barber_shaves_self: shaves barber barber,
    have ¬ shaves barber barber, from (h barber).mp barber_shaves_self,
    absurd barber_shaves_self ‹ ¬ shaves barber barber ›
  ),
  have shaves barber barber, from (h barber).mpr ‹ ¬ shaves barber barber ›,
  absurd this ‹ ¬  shaves barber barber ›
