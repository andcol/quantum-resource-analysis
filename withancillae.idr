module Main

import Data.Vect

--Datatype for the representation of computations requiring ancilla qubits

data WithAncillae : Nat -> Type -> Type where
    WA : a -> WithAncillae n a

--Useful shorthands:
InPlace : Type -> Type
InPlace t = WithAncillae 0 t -- Computations requiring no ancillae
WithAncilla : Type -> Type
WithAncilla t = WithAncillae 1 t -- Computations requiring a single ancilla

-- Tried to define a graded monad typeclass with generic Effect annotations,
-- but for some reason this never seem to compile correctly, so the following
-- blocks have been commented out.

--interface Effect (t : Type) where -- Effect typeclass (basically a repetition of Monoid)
--    none : () -> t
--    join : t -> t -> t

--interface Effect g => GradedMonad g (m : g -> Type -> Type) | m where -- Graded monad typeclass
--    return : a -> m none a
--    (>>=) : m e a -> (a -> m f b) -> m (join e f) b
--    (>>) : m e a -> m f b -> m (join e f) b
--    --m >> m' = m >>= \x -> m'

--implementation Effect Nat where
--    empty = 0
--    join = max

--implementation GradedMonad Nat WithAncillae where
--    return x = WA x
--    (WA x) >>= f = let (WA y) = f x in WA y
--    (WA x) >> (WA y) = (WA y)


-- Resorted to hard-wired implementation of the graded monad operations specifically for WithAncillae

return : a -> WithAncillae 0 a
return x = WA x

(>>=) : WithAncillae n a -> (a -> WithAncillae m b) -> WithAncillae (n+m) b
(WA x) >>= f = let (WA y) = f x in WA y


--QUANTUM STUFF (kind of)

--data types (qubit and bit labels)

data Qubit = Q String
data Bit = B String

--operations

qinit : InPlace Qubit
qinit = return $ Q "placeholder"

qinitMany : (n:Nat) -> InPlace (Vect n Qubit)
qinitMany Z = return []
qinitMany (S n) = do
    q <- qinit
    rq <- qinitMany n
    return (q::rq)

-- When discarding a qubit (which is not output and is therefore assumed to be an ancilla)
-- we keep track of one ancilla in the monad signature
discard : Bit -> WithAncillae 1 ()
discard b = WA ()

discardMany : Vect n Bit -> WithAncillae n ()
discardMany [] = return ()
discardMany (b::br) = do
    discard b
    discardMany br


-- Since we are just interested in the type level aspect of resource analysis, the following operations
-- do absolutely nothing in terms of quantum computation or circuit building, they are just here
-- as typed placeholders for realistic operations

hadamard : Qubit -> InPlace Qubit
hadamard q = return q

cnot : Qubit -> Qubit -> InPlace (Qubit,Qubit)
cnot q1 q2 = return (q1,q2)

toffoli : Qubit -> Qubit -> Qubit -> InPlace (Qubit,Qubit,Qubit)
toffoli q1 q2 q3 = return (q1,q2,q3)

meas : Qubit -> InPlace Bit
meas q = return (B "placeholder")

measMany : Vect n Qubit -> InPlace (Vect n Bit)
measMany [] = return []
measMany (q::qr) = do
    b <- meas q
    br <- measMany qr
    return (b::br)

-- Some tests

-- In the following, replacing WithAncilla with fewer or more ancillae correctly fails at compile-time
simpleTest : Qubit -> WithAncilla ()
simpleTest q = meas q >>= \c => discard c

-- Same here, but with more complex composition and do-notation (like in Quipper)
slightlyMoreComplexTest : Qubit -> WithAncilla Qubit
slightlyMoreComplexTest q = do
    q <- hadamard q
    q' <- qinit
    (q,q') <- cnot q q'
    c <- meas q'
    discard c
    return q

-- Trying to implement quantum carry-ripple adder from "Vedral, V., Barenco, A., & Ekert, A. (1996).
-- Quantum networks for elementary arithmetic operations. Physical Review A."
-- This algorithm adds a n-qubit register to a (n+1)-qubit register and stores the result
-- in the latter register, thus implementing the unitary |a,b> |-> |a,a+b>.
-- It uses n ancilla qubits in the process.

-- Carry subcircuit
carry : Qubit -> Qubit -> Qubit -> Qubit -> InPlace (Qubit,Qubit,Qubit,Qubit)
carry q1 q2 q3 q4 = do
    (q2,q3,q4) <- toffoli q2 q3 q4
    (q2,q3) <- cnot q2 q3
    (q1,q3,q4) <- toffoli q1 q3 q4
    return (q1,q2,q3,q4)

-- Reverse of carry
uncarry : Qubit -> Qubit -> Qubit -> Qubit -> InPlace (Qubit,Qubit,Qubit,Qubit)
uncarry q1 q2 q3 q4 = do
    (q1,q3,q4) <- toffoli q1 q3 q4
    (q2,q3) <- cnot q2 q3
    (q2,q3,q4) <- toffoli q2 q3 q4
    return (q1,q2,q3,q4)

-- Full-adder subcircuit
sum : Qubit -> Qubit -> Qubit -> InPlace (Qubit,Qubit,Qubit)
sum q1 q2 q3 = do
    (q2,q3) <- cnot q2 q3
    (q1,q3) <- cnot q1 q3
    return (q1,q2,q3)

-- "body" of the actual n-qubit adder circuit.
-- At this phase the ancillae (c) are given as input and returned as output, so we are still InPlace
adder' : Vect n Qubit -> Vect n Qubit -> Vect (n+1) Qubit -> InPlace (Vect n Qubit, Vect n Qubit, Vect (n+1) Qubit)
adder' [c] [a] [b,b'] = do
    (c,a,b,b') <- carry c a b b'
    (a,b) <- cnot a b
    (c,a,b) <- sum c a b
    return ([c], [a], [b,b'])
adder' (c::c'::cr) (a::ar) (b::br) = do
    (c,a,b,c') <- carry c a b c'
    (c'::cr, ar, br) <- adder' (c'::cr) ar br
    (c,a,b,c') <- uncarry c a b c'
    (c,a,b) <- sum c a b
    return (c::c'::cr, a::ar, b::br)

-- Necessary for ancilla arithmetic in the following function
zeroNeutralRight : (n:Nat) -> (n+0 = n)
zeroNeutralRight Z = Refl
zeroNeutralRight (S m) = cong (zeroNeutralRight m) 

-- The actual adder circuit with ancilla initialization and termination.
-- Here is where we actually make use of the monad
adder : (n:Nat) ->
        Vect n Qubit -> Vect (n+1) Qubit -> WithAncillae n (Vect n Qubit, Vect (n+1) Qubit)
--We must inform the type checker that the resulting n+0 ancillae is indeed n ancillae
adder n a b =
    replace {P = \m => WithAncillae m (Vect n Qubit, Vect (n+1) Qubit)} (zeroNeutralRight n) $ do
        c <- qinitMany n
        (c,a,b) <- adder' c a b
        c <- measMany c
        discardMany c
        return (a,b)

-- If we did not annotate the right number of ancillae, the function would fail to type-check, e.g.:
-- wrongAdder : (n:Nat) ->
--     Vect n Qubit -> Vect (n+1) Qubit -> InPlace (Vect n Qubit, Vect (n+1) Qubit)
-- wrongAdder n a b =
--     replace {P = \m => WithAncillae m (Vect n Qubit, Vect (n+1) Qubit)} (zeroNeutralRight n) $ do
--         c <- qinitMany n
--         (c,a,b) <- adder' c a b
--         c <- measMany c
--         discardMany c
--         return (a,b)

--useless
main : IO ()
main = putStrLn "Hello world"