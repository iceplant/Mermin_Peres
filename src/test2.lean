import data.nat.basic
import data.nat.parity
-- open_locale classical
decidable theory

-- --Do I want these to be bools or Props?
def myIsEven := nat.even
def myIsOdd (n : ℕ) := ¬ (myIsEven n)

#reduce myIsEven 2
--#eval myIsEven 2

--Alice only sees r and Bob only sees c. The strategy isn't (r,c) → (...) but two maps, r→(r1 r2 r3) and c → (c1 c2 c3)
--I'm using 0 and 1 instead of Green and Red as the two options to fill squares. This makes checking parity of strategies easier

------------METHOD 1: enumerate all the constraints as concisely as possible and reduce to show we get a contraditcion----------------------------------
def checkStrategyrc (r c : ℕ) (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : bool :=
        let r1 := (strategy.1 r).1, 
        r2 := (strategy.1 r).2.1, 
        r3 := (strategy.1 r).2.2,
        c1 := (strategy.2 c).1,
        c2 := (strategy.2 c).2.1,
        c3 := (strategy.2 c).2.2

        in myIsEven(r1 + r2 + r3) ∧ myIsOdd(c1 + c2 + c3) ∧ 
        ((r = 1 ∧ c = 1 ∧ r1 = c1) ∨ (r = 1 ∧ c = 2 ∧ r2 = c1) ∨ (r = 1 ∧ c = 3 ∧ r3 = c1)
        ∨(r = 2 ∧ c = 1 ∧ r1 = c2) ∨ (r = 2 ∧ c = 2 ∧ r2 = c2) ∨ (r = 2 ∧ c = 3 ∧ r3 = c2)
        ∨(r = 3 ∧ c = 1 ∧ r1 = c3) ∨ (r = 3 ∧ c = 2 ∧ r2 = c3) ∨ (r = 3 ∧ c = 3 ∧ r3 = c3))

--checks all three conditions are met for the strategy
def checkStrategy (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : bool := 
    (checkStrategyrc 1 1 strategy) ∧ (checkStrategyrc 1 2 strategy) ∧ (checkStrategyrc 1 3 strategy) ∧
    (checkStrategyrc 2 1 strategy) ∧ (checkStrategyrc 2 2 strategy) ∧ (checkStrategyrc 2 3 strategy) ∧
    (checkStrategyrc 3 1 strategy) ∧ (checkStrategyrc 3 2 strategy) ∧ (checkStrategyrc 3 3 strategy)

--given a strategy, we can't have it satisfy all the conditions
theorem noStrategy2 (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) (r c : ℕ) : ¬ (checkStrategy (strategy)) :=
begin
intro s,
rw checkStrategy at s,
repeat {rw checkStrategyrc at s},
simp at s,
--every case here has a false equality and-ed with something else. How do I replace them with false and reduce?
--how do I tell it that we only care about the cases where r,c ∈ {1,2,3} and then do cases on those?
end