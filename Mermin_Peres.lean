import init.data.nat.basic
set_option class.instance_max_depth 15000000

def myIsEven (n : ℕ) : bool := n = (n/2)*2
def myIsOdd (n : ℕ) : bool := ¬ (n = (n/2)*2)

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


-------------------------METHOD 2: More intermediate lemmas using parity of sum---------------------------------------------

--checks even/odd conditions are met for a strategy on a specific rc value pair
def isStrategyrc (r c : ℕ) (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : bool :=
    let r1 := (strategy.1 r).1, 
        r2 := (strategy.1 r).2.1, 
        r3 := (strategy.1 r).2.2,
        c1 := (strategy.2 c).1,
        c2 := (strategy.2 c).2.1,
        c3 := (strategy.2 c).2.2
        in myIsEven(r1 + r2 + r3) ∧ myIsOdd(c1 + c2 + c3)

--checks that the even/odd criteria are met for all values of r,c ∈ {1,2,3}
def isStrategy (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : bool := 
    (isStrategyrc 1 1 strategy) ∧ (isStrategyrc  1 2 strategy) ∧ (isStrategyrc  1 3 strategy) ∧
    (isStrategyrc  2 1 strategy) ∧ (isStrategyrc  2 2 strategy) ∧ (isStrategyrc  2 3 strategy) ∧
    (isStrategyrc  3 1 strategy) ∧ (isStrategyrc  3 2 strategy) ∧ (isStrategyrc  3 3 strategy)

--checks that the r and c strategies return the same values for every (r,c) in {1,2,3}×{1,2,3}
def rcAlign (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : bool := 
    ((strategy.1 1).1 = (strategy.2 1).1) ∧ ((strategy.1 2).1 = (strategy.2 2).1) ∧ ((strategy.1 3).1 = (strategy.2 3).1) ∧ 
    ((strategy.1 1).2.1 = (strategy.2 1).2.1) ∧ ((strategy.1 2).2.1 = (strategy.2 2).2.1) ∧ ((strategy.1 3).2.1 = (strategy.2 3).2.1) ∧ 
    ((strategy.1 1).2.2 = (strategy.2 1).2.2) ∧ ((strategy.1 2).2.2 = (strategy.2 2).2.2) ∧ ((strategy.1 3).2.2 = (strategy.2 3).2.2)


--test strategy that just puts 0 everywhere
def rStrat0 (r : ℕ) : (ℕ × ℕ × ℕ) := (0,0,0)
def cStrat0 (c : ℕ) : (ℕ × ℕ × ℕ) := (0,0,0)
def strat0 := (rStrat0, cStrat0)

--finds the sum of values from Alice's strategy
def rSum (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : ℕ :=
    let rStrat := strategy.1 in (rStrat 1).1 + (rStrat 1).2.1 + (rStrat 1).2.2 +
                                (rStrat 2).1 + (rStrat 2).2.1 + (rStrat 2).2.2 +
                                (rStrat 3).1 + (rStrat 3).2.1 + (rStrat 3).2.2

--finds the sum of values from Bob's strategy
def cSum (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : ℕ :=
    let cStrat := strategy.2 in (cStrat 1).1 + (cStrat 1).2.1 + (cStrat 1).2.2 +
                                (cStrat 2).1 + (cStrat 2).2.1 + (cStrat 2).2.2 +
                                (cStrat 3).1 + (cStrat 3).2.1 + (cStrat 3).2.2

--since each row of Alice's must be even, this asserts that the sum must be even
lemma rSumEven (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : isStrategy(strategy) → myIsEven(rSum(strategy)) :=
    begin
    rw rSum,
    rw myIsEven,
    intro isStrat,
    rw isStrategy at isStrat,
    simp,
    sorry,
    end

--since each column of bob's must be odd, and there are an odd number of columns, the sum must be odd
lemma cSumOdd (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : isStrategy(strategy) → myIsOdd(cSum(strategy)) :=
    begin
    rw cSum,
    rw myIsOdd,
    intro isStrat,
    rw isStrategy at isStrat,
    simp,
    sorry,
    end

--the sums of Alice's and Bob's strategies must be equal or else there would be an element they disagree on
lemma rSum_eq_cSum (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : (isStrategy(strategy) ∧ rcAlign(strategy)) → (rSum(strategy) = cSum(strategy)) :=
begin
intro isStrat,
rw rSum,
rw cSum,
simp,
sorry,
end

--given an even and an odd number, they cannot be equal
lemma even_neq_odd (a b : ℕ) : myIsEven(a) ∧ myIsOdd(b) → a ≠ b :=
begin
intro h1,
cases h1 with ha hb,
intro heq,
rw myIsEven at ha,
rw myIsOdd at hb,
rw ← heq at hb,
sorry,
apply hb,
end

--given a strategy, Alice's and Bob's strategies must sum to the same thing, but one sum is even and the other is odd, so this is impossible
theorem noStrategy (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) (r c : ℕ) : ¬ (isStrategy(strategy) ∧ rcAlign(strategy)):=
begin
intro h,
cases h with hisStrat hrcAlign,
have hrSumEven := rSumEven(strategy) hisStrat,
have hcSumOdd := cSumOdd(strategy) hisStrat,
have hrSum_eq_cSum := rSum_eq_cSum(strategy)(hisStrat ∧ rcAlign),
have hrSum_neq_cSum := even_neq_odd (rSum strategy) (cSum strategy) (hrSumEven ∧ hcSumOdd),
apply hrSum_neq_cSum,
exact hrSum_eq_cSum,
end


--METHOD 3: enumerate every possible strategy and show that they all fail -----------------------------


--DISCUSSION-------------------------------------------------------

--goal: figure out how to iterate over the square in a more concise way, especially if we want to generalize beyond n=3
    --this would make all of my strategy checks much more readable and concise
    --defining local variables in a better way than using "let" statements would also be nice
    --idea: define a type for numbers in the set {1,2,3,...,n} so that we can can do cases. Is this necessary though?

--goal: define a Type for functions that take in two variables in the set {1,2,3} and output a vector of size 6 of bools
    --can get away with doing this without a Type, but it might make things easier? Maybe this is a more OOP strategy and that's not what we want here
    --would it be helpful to enumerate every possible strategy, then apply every possible strategy and show they all fail? I've been trying to show necessary conditions for strategies lead to contradictions

--Errors: 
    --line 125 in even_neq_odd, how do I fix the to_bool thing so I can use the statement?
    --and statement in noStrategy
    --substituting false for 1 = 2, 1 = 3, etc in noStrategy2 and then reducing. 
    