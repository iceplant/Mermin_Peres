-- import init.data.nat.basic
-- import init.algebra.ring
-- import init.algebra.norm_num 
import init 
import tactic
import data.nat.parity
import data.finset
import data.fintype
import algebra.big_operators
set_option class.instance_max_depth 15000000


#eval 2

open_locale classical


--open_local matrix

--Alice only sees r and Bob only sees c. The strategy isn't (r,c) → (...) but two maps, r→(r1 r2 r3) and c → (c1 c2 c3)
--I'm using 0 and 1 instead of Green and Red as the two options to fill squares. This makes checking parity of strategies easier

--fin 3 (type = {1,2,3})
--eventually we will be interested in relative probabilities

------------METHOD 1: enumerate all the constraints as concisely as possible and reduce to show we get a contraditcion----------------------------------
--try namespace outside of def but enclosing it
def checkStrategyrc (r c : ℕ) (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : Prop :=
        --functionalize this with lists. 
        let r1 := (strategy.1 r).1, 
        r2 := (strategy.1 r).2.1, 
        r3 := (strategy.1 r).2.2,
        c1 := (strategy.2 c).1,
        c2 := (strategy.2 c).2.1,
        c3 := (strategy.2 c).2.2

        in nat.even(r1 + r2 + r3) ∧ (¬ nat.even(c1 + c2 + c3)) ∧ 
        ((r = 1 ∧ c = 1 ∧ r1 = c1) ∨ (r = 1 ∧ c = 2 ∧ r2 = c1) ∨ (r = 1 ∧ c = 3 ∧ r3 = c1)
        ∨(r = 2 ∧ c = 1 ∧ r1 = c2) ∨ (r = 2 ∧ c = 2 ∧ r2 = c2) ∨ (r = 2 ∧ c = 3 ∧ r3 = c2)
        ∨(r = 3 ∧ c = 1 ∧ r1 = c3) ∨ (r = 3 ∧ c = 2 ∧ r2 = c3) ∨ (r = 3 ∧ c = 3 ∧ r3 = c3))

--checks all three conditions are met for the strategy
def checkStrategy (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : Prop := 
    (checkStrategyrc 1 1 strategy) ∧ (checkStrategyrc 1 2 strategy) ∧ (checkStrategyrc 1 3 strategy) ∧
    (checkStrategyrc 2 1 strategy) ∧ (checkStrategyrc 2 2 strategy) ∧ (checkStrategyrc 2 3 strategy) ∧
    (checkStrategyrc 3 1 strategy) ∧ (checkStrategyrc 3 2 strategy) ∧ (checkStrategyrc 3 3 strategy)

--someone on Zulip said to try putting this not directly after the import statements. This seems to have helped

--given a strategy, we can't have it satisfy all the conditions

theorem odd_add_odd {m n} : ¬ nat.even m → ¬ nat.even n → nat.even (m + n) := sorry
theorem odd_add_even {m n} : ¬ nat.even m → nat.even n → ¬ nat.even (m + n) := sorry
theorem even_add_even {m n} : nat.even m → nat.even n → nat.even (m + n) := sorry

theorem noStrategy2 (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : ¬ (checkStrategy (strategy)) :=
begin
intro s,
rw checkStrategy at s,
repeat {rw checkStrategyrc at s},
revert s,
rw (show 1 = 2 ↔ false, by norm_num),
rw (show 2 = 1 ↔ false, by norm_num),
rw (show 3 = 1 ↔ false, by norm_num),
rw (show 1 = 3 ↔ false, by norm_num),
rw (show 3 = 2 ↔ false, by norm_num),
rw (show 2 = 3 ↔ false, by norm_num),
repeat {simp only [false_and, false_or, and_false, or_false]},
rw (show 1=1 ↔ true, by norm_num),
rw (show 2=2 ↔ true, by norm_num),
rw (show 3=3 ↔ true, by norm_num),
simp only [true_and, and_true, true_or, or_true],
intro s,
rcases s with ⟨⟨s1, t1, u1⟩, ⟨s2, t2, u2⟩, ⟨s3, t3, u3⟩,
               ⟨s4, t4, u4⟩, ⟨s5, t5, u5⟩, ⟨s6, t6, u6⟩,
               ⟨s7, t7, u7⟩, ⟨s8, t8, u8⟩, ⟨s9, t9, u9⟩⟩,
 -- fails
rw u1 at *,
rw u2 at *,
rw u3 at *,
rw u4 at *,
rw u5 at *,
rw u6 at *,
rw u7 at *,
rw u8 at *,
rw u9 at *,
apply odd_add_even t1 (odd_add_odd t2 t3),
convert even_add_even s1 (even_add_even s4 s7) using 1,
ring,

--seems like norm_num, finish, or safe could be useful here

--every case here has a false equality and-ed with something else. How do I replace them with false and reduce?
--how do I tell it that we only care about the cases where r,c ∈ {1,2,3} and then do cases on those?
end





--------------General case: mxn where m and n are odd
def checkStrategyMN {m n : nat} (strategyA : fin m → fin n → nat) (strategyB: fin n → fin m → nat) : Prop := 
(∀ r : fin m, (∀ c : fin n, ((finset.univ.sum (strategyA r)).even) ∧ (¬ (finset.univ.sum (strategyB c)).even) ∧ ((strategyA r c) = (strategyB c r))))


-- (∀ r : fin m, (finset.univ.sum (strategyA r)).even) ∧ (∀ c : fin n, ¬ (finset.univ.sum (strategyB c)).even) ∧ 
-- (∀ r : m, ∀ c : n, ((strategyA r c) = (strategyB c r)))

theorem noStrategyMN {m n : nat} (strategyA : fin m → fin n → nat) (strategyB: fin n → fin m → nat) : ((¬ m.even) ∧ (¬ n.even)) → ¬ (checkStrategyMN strategyA strategyB) :=
begin
rw checkStrategyMN,
intro h,
push_neg,
--??????????????????????
end






----Method 2: show sampling---

#check [[1,2],[1,2,3,4],[1,2,3,4,0],[]]

def board {m n : nat} (strategyA : fin m → fin n → nat) (strategyB: fin n → fin m → nat) : fin m → fin n → nat := strategyA --woah man...these representations are THE SAME!!!! (function that returns a vector and a matrix)

def consistent {m n : nat} (strategyA : fin m → fin n → nat) (strategyB: fin n → fin m → nat) : Prop 
:= ∀ (r : fin m) (c : fin n), (strategyA r c) = (strategyB c r)

def sampleA {m n : nat} (board : fin m → fin n → nat) : fin m → fin n → nat := board

def sampleB {m n : nat} (board : fin m → fin n → nat) : fin n → fin m → nat := λ (n : fin n) (m : fin m), board m n  
#check sampleA
#check sampleB

lemma board_equiv_strategy {m n : nat} (strategyA : fin m → fin n → nat) (strategyB: fin n → fin m → nat) : 
(consistent strategyA strategyB) → (strategyA = ((sampleA (board strategyA strategyB))) ∧ (strategyB = (sampleB (board strategyA strategyB))))
:=
begin
intro h,
split,
rw sampleA,
rw board,
rw board,
rw sampleB,
rw consistent at h,
rw h, --Logically this should work and seems pretty simple. How do I tell lean to do this???????????
end

def each_row_sum_even {m n : nat} (board : fin m → fin n → nat) : Prop := ∀ (r : fin m), (finset.univ.sum (sampleA board r)).even 

def each_col_sum_odd {m n : nat} (board : fin m → fin n → nat) : Prop := ∀ (c : fin n), ¬(finset.univ.sum (sampleB board c)).even

def even_strategy {m n : nat} (strategyA : fin m → fin n → nat) : Prop := (∀ r : fin m, ((finset.univ.sum (strategyA r)).even))

def odd_strategy {m n : nat} (strategyB : fin n → fin m → nat) : Prop := (∀ (c : fin n), ¬ (finset.univ.sum (strategyB c)).even)

lemma even_strategy_implies_even_rows {m n : nat} (strategyA : fin m → fin n → nat) (strategyB : fin n → fin m → nat) 
: ((consistent strategyA strategyB) ∧ even_strategy strategyA) → each_row_sum_even (board strategyA strategyB) 
:=
begin
rw even_strategy,
rw each_row_sum_even,
rw sampleA,
rw board,
intro h,
have h := h.right,
exact h,
end

--In order to talk about a board we need to assume the two strategies are consistent. Or else we need to define the board differently to allowfor this
lemma odd_strategy_implies_odd_cols {m n : nat} (strategyA : fin m → fin n → nat) (strategyB : fin n → fin m → nat) 
: ((consistent strategyA strategyB) ∧ odd_strategy strategyB) → each_col_sum_odd (board strategyA strategyB) 
:=
begin
intro h,
cases h with h1 h2,
have h3 := board_equiv_strategy strategyA strategyB h1,
cases h3 with h4 h5,
rw each_col_sum_odd,
rw ← h5,
rw odd_strategy at h2,
exact h2,
end

--switch to mathlib matrix implementation
--Posted on Zulip about this-------------------
--Does this actually sum rows???????? We don't need a column one because we have our sampling function sampleB which is like a transpose
def matrix_sum {m n : ℕ} (M : fin m → fin n → ℕ ) : ℕ :=  
finset.univ.sum $ λ i, finset.univ.sum $ M i

def row_sum {m n : nat} (board : fin m → fin n → nat) : nat := matrix_sum (sampleA board)

def col_sum {m n : nat} (board : fin m → fin n → nat) : nat := matrix_sum (sampleB board)

lemma row_sum_eq_col_sum {m n : nat} (board : fin m → fin n → nat) : row_sum board = col_sum board
:= 
begin
rw row_sum,
rw col_sum,
rw matrix_sum,
rw matrix_sum,
rw sampleB,
rw sampleA,
simp,
end

theorem noStrategyMN2 {m n : nat} (strategyA : fin m → fin n → nat) (strategyB: fin n → fin m → nat) : 
¬ ((consistent strategyA strategyB) ∧  (even_strategy strategyA) ∧ (odd_strategy strategyB))
:=
begin
intro h,
cases h with c y,
cases y with even odd,
have x := even_strategy_implies_even_rows strategyA strategyB (c ∧ even),
have y := odd_strategy_implies_odd_cols strategyA strategyB odd,
end



------------------------tests-----------------
theorem myTheorem : ¬ (∀ x : nat, x = 2) :=
begin
intro h,
specialize h 0,
end


------Ideas----
--use mathlib matrix representation
