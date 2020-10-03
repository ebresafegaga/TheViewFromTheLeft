module Predicate

import Data.Vect

removeElem : (value : a) ->
             (xs : Vect (S n) a) ->
             (prf : Elem value xs) ->
             Vect n a
removeElem value (value :: ys) Here                  = ys
removeElem value {n = Z} (y :: []) (There later)     impossible
removeElem value {n = (S k)} (y :: ys) (There later) = y :: removeElem value ys later



data Last : List a -> a -> Type where
    LastOne   : Last [value] value
    LastCons  : (prf : Last xs value) -> Last (x :: xs) value

last123 : Last [1, 2, 3] 3
last123 = LastCons (LastCons LastOne)

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value        = No $ \somethingimpossible => ?dedede
isLast [x] value       =
    case decEq x value of
        Yes p     => rewrite p in Yes LastOne
        No contra => No $ \LastOne => contra Refl
isLast (x :: xs) value with (isLast xs value)
    | (Yes prf)   = Yes (LastCons prf)
    | (No contra) = No $ \(LastCons whatiwant) => contra whatiwant


--data ExistView : (x : a) -> List a - > Type where
--    Yeah : (x : a) -> ExistView
