module Left

import Data.Vect
import Data.Fin

%default total

fs : (m : Nat) -> (i : Fin n) -> Fin (m + n)
fs Z i     = i
fs (S k) i = FS (fs k i)


data Chop : (xs : Vect n a) -> (i : Fin n) -> Type where
    ChopGlue : (ys : Vect m a) -> (x : a) -> (xs : Vect n a) -> Chop (ys ++ x :: xs) (fs m (FZ{k=n}))

chop : (xs : Vect n a) -> (i : Fin n) -> Chop xs i
chop (x :: xs) FZ = ChopGlue [] x xs
chop (x :: xs) (FS i) with (chop xs i)
    chop (x :: (ys ++ (y :: zs))) (FS (fs m FZ)) | (ChopGlue ys y zs) = ChopGlue (x :: ys) y zs
