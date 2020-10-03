module Left

import Data.Vect
import Data.Fin
import Data.So

%default total

fs : (m : Nat) -> (i : Fin n) -> Fin (m + n)
fs Z i     = i
fs (S k) i = FS (fs k i)

-- View Vects as an array with an index
data Chop : (xs : Vect n a) -> (i : Fin n) -> Type where
    ChopGlue : (ys : Vect m a) -> (x : a) -> (xs : Vect n a) -> Chop (ys ++ x :: xs) (fs m (FZ{k=n}))

-- covering function for that view
chop : (xs : Vect n a) -> (i : Fin n) -> Chop xs i
chop (x :: xs) FZ = ChopGlue [] x xs
chop (x :: xs) (FS i) with (chop xs i)
    chop (x :: (ys ++ (y :: zs))) (FS (fs m FZ)) | (ChopGlue ys y zs) = ChopGlue (x :: ys) y zs


dom : Vect m (Nat, a) -> (n : Nat) -> Bool
dom [] n        = False
dom ((l, x) :: xs) n with (l == n)
    | False = dom xs n
    | True  = True


assoc : (xs : Vect m (Nat, a)) -> (n : Nat) -> So (dom xs n) -> a
assoc [] _ Oh impossible
assoc ((l, x) :: xs) n p with (l == n)
    assoc ((l, x) :: xs) n p | False = assoc xs n p
    assoc ((l, x) :: xs) n p | True  = x
