module Main

import Data.Vect

--Datatype for the representation of computations requiring ancillae

data WithAncillae : Nat -> Type -> Type where
    WA : a -> WithAncillae n a

--Useful shorthands:
InPlace : Type -> Type
InPlace t = WithAncillae 0 t --Computazioni senza ancillae
WithAncilla : Type -> Type
WithAncilla t = WithAncillae 1 t --Computazioni con una sola ancilla

-- Ho provato a definire una graded monad come typeclass che accetta un generico Effect come annotazione
-- ma per qualche motivo non riesco a far tornare i tipi, per cui ho commentato via i seguenti blocchi

--interface Effect (t : Type) where
--    none : () -> t
--    join : t -> t -> t

--interface Effect g => GradedMonad g (m : g -> Type -> Type) | m where
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

-- Ho quindi implementato le operazioni return e bind ad-hoc per WithAncillae

return : a -> WithAncillae 0 a
return x = WA x

(>>=) : WithAncillae n a -> (a -> WithAncillae m b) -> WithAncillae (n+m) b
(WA x) >>= f = let (WA y) = f x in WA y

--QUANTUM STUFF

--data types

data Complex = C Double Double

data Qubit = Q Complex Complex
data Bit = B Bool

--operations

init : InPlace Qubit
init = return $ Q (C 1.0 0.0) (C 0.0 0.0)

initMany : (n:Nat) -> InPlace (Vect n Qubit)
initMany Z = return []
initMany (S n) = do
    q <- init
    rq <- initMany n
    return (q::rq)

discard : Bit -> WithAncillae 1 () --Quando faccio discard, tengo traccia nella segnatura della monade
discard b = WA ()

discardMany : Vect n Bit -> WithAncillae n ()
discardMany [] = return ()
discardMany (b::br) = do
    discard b
    discardMany br

-- Le seguenti operazioni sono assolutamente inutili dal punto di vista computazionale (non fanno niente),
-- visto che ci interessa fare dei test a compile-time mi sono preoccupato solo che avessero il tipo corretto.

fakeH : Qubit -> InPlace Qubit
fakeH q = return q

fakeCNOT : Qubit -> Qubit -> InPlace (Qubit,Qubit)
fakeCNOT q1 q2 = return (q1,q2)

fakeToffoli : Qubit -> Qubit -> Qubit -> InPlace (Qubit,Qubit,Qubit)
fakeToffoli q1 q2 q3 = return (q1,q2,q3)

fakeMeas : Qubit -> InPlace Bit
fakeMeas q = return (B True)

fakeMeasMany : Vect n Qubit -> InPlace (Vect n Bit)
fakeMeasMany [] = return []
fakeMeasMany (q::qr) = do
    b <- fakeMeas q
    br <- fakeMeasMany qr
    return (b::br)

--Test vari

simpleTest : Qubit -> WithAncilla () --replacing WithAncilla with fewer or more ancillae correctly fails at compile-time
simpleTest q = fakeMeas q >>= \c => discard c

slightlyMoreComplexTest : Qubit -> WithAncilla Qubit
slightlyMoreComplexTest q = do
    q <- fakeH q
    q' <- init
    (q,q') <- fakeCNOT q q'
    c <- fakeMeas q'
    discard c
    return q

--Trying to implement quantum carry-ripple adder from Vedral, V., Barenco, A., & Ekert, A. (1996).
--Quantum networks for elementary arithmetic operations. Physical Review A.
--This implementation adds two n-qubit registers using n ancillae in the process

carry : Qubit -> Qubit -> Qubit -> Qubit -> InPlace (Qubit,Qubit,Qubit,Qubit)
carry q1 q2 q3 q4 = do
    (q2,q3,q4) <- fakeToffoli q2 q3 q4
    (q2,q3) <- fakeCNOT q2 q3
    (q1,q3,q4) <- fakeToffoli q1 q3 q4
    return (q1,q2,q3,q4)

uncarry : Qubit -> Qubit -> Qubit -> Qubit -> InPlace (Qubit,Qubit,Qubit,Qubit)
uncarry q1 q2 q3 q4 = do
    (q1,q3,q4) <- fakeToffoli q1 q3 q4
    (q2,q3) <- fakeCNOT q2 q3
    (q2,q3,q4) <- fakeToffoli q2 q3 q4
    return (q1,q2,q3,q4)

sum : Qubit -> Qubit -> Qubit -> InPlace (Qubit,Qubit,Qubit)
sum q1 q2 q3 = do
    (q2,q3) <- fakeCNOT q2 q3
    (q1,q3) <- fakeCNOT q1 q3
    return (q1,q2,q3)

--"body" of the adder circuit. Note that ancillae are input and output
adder' : Vect n Qubit -> Vect n Qubit -> Vect (n+1) Qubit -> InPlace (Vect n Qubit, Vect n Qubit, Vect (n+1) Qubit)
adder' [c] [a] [b,b'] = do
    (c,a,b,b') <- carry c a b b'
    (a,b) <- fakeCNOT a b
    (c,a,b) <- sum c a b
    return ([c], [a], [b,b'])
adder' (c::c'::cr) (a::ar) (b::br) = do
    (c,a,b,c') <- carry c a b c'
    (c'::cr, ar, br) <- adder' (c'::cr) ar br
    (c,a,b,c') <- uncarry c a b c'
    (c,a,b) <- sum c a b
    return (c::c'::cr, a::ar, b::br)

--Necessary for ancillae arithmetic
zeroNeutralRight : (n:Nat) -> (n+0 = n)
zeroNeutralRight Z = Refl
zeroNeutralRight (S m) = cong (zeroNeutralRight m) 


--The actual adder circuit with ancillae initialization and termination. Here we make use of the monad
adder : (n:Nat) -> Vect n Qubit -> Vect (n+1) Qubit -> WithAncillae n (Vect n Qubit, Vect (n+1) Qubit)
--We must inform the type checker that n+0 ancillae is the same as n ancillae
adder n a b = replace {P = \m => WithAncillae m (Vect n Qubit, Vect (n+1) Qubit)} (zeroNeutralRight n) $ do
        c <- initMany n
        (c,a,b) <- adder' c a b
        c <- fakeMeasMany c
        discardMany c
        return (a,b)

--useless
main : IO ()
main = putStrLn "Hello world"