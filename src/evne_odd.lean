import data.nat.basic

inductive is_odd : ℕ → Prop
 |   one : is_odd 1
 |   step{n} : is_odd n → is_odd (n+2)

 inductive is_even : ℕ → Prop
 |   one : is_even 0
 |   step{n} : is_even n → is_even (n+2)
