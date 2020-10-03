module Views

import Data.Vect

data ListLast : List a -> Type where
    Empty : ListLast []
    NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describeHelper : (input : List Int) -> (form : ListLast input) -> String
describeHelper [] Empty                    = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) =
    "Non-empty, the initial portion is: " ++ show xs

total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) =
    case listLast xs of
        Empty         => NonEmpty [] x
        NonEmpty ys y => NonEmpty (x :: ys) y


describeListEnd : List Int -> String
describeListEnd xs with (listLast xs)
    describeListEnd []          | Empty           = "Empty"
    describeListEnd (ys ++ [x]) | (NonEmpty ys x) = "NonEmpty with initial part: " ++ show ys


myReverse : List a -> List a
myReverse xs with (listLast xs)
    myReverse []          | Empty           = []
    myReverse (ys ++ [x]) | (NonEmpty ys x) = x :: myReverse ys

data SplitList : List a -> Type where
    SplitNil : SplitList []
    SplitOne : SplitList [x]
    SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)

total
splitList : (input : List a) -> SplitList input
splitList input = help input input
    where
        help : List a -> (input : List a) -> SplitList input
        help _ [] = SplitNil
        help _ [x] = SplitOne
        help (_ :: _ :: counter) (item :: items) =
            case help counter items of
                SplitNil             => SplitOne
                SplitOne {x}         => SplitPair [item] [x]
                SplitPair left right => SplitPair (item :: left) right
        help _ xs = SplitPair [] xs

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
    mergeSort []                | SplitNil                 = []
    mergeSort [x]               | SplitOne                 = [x]
    mergeSort (lefts ++ rights) | (SplitPair lefts rights) = merge (mergeSort lefts) (mergeSort rights)


data TakeN : List a -> Type where
    Fewer : TakeN xs
    Exact : (xs : List a) -> TakeN (xs ++ rest)

sub : Nat -> Nat -> Nat
sub k Z = k
sub Z (S j) = Z
sub (S k) (S j) = k `sub` j


div : Nat -> Nat -> Nat
div Z j = Z
div k j = S (div (k `sub` j) j)

total
takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN (S Z) [] = Fewer
takeN (S Z) (x :: xs) = Exact [x]
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) =
    case takeN k xs of
        Fewer => Fewer
        Exact xs =>  Exact (x :: xs)
takeN Z [] = Fewer
takeN Z (x :: xs) = Exact []

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n input with (takeN n input)
    groupByN n input        | Fewer      = [input]
    groupByN n (xs ++ rest) | (Exact xs) = xs :: groupByN n rest

halves : List a -> (List a, List a)
halves xs with (takeN (length xs `div` 2) xs)
    halves xs           | Fewer      = (xs, [])
    halves (ys ++ rest) | (Exact ys) = (ys, rest)


-- data SnocList ty = SnocEmpty | Snoc (SnocList ty) ty

data SnocList : List a -> Type where
    SnocEmpty : SnocList []
    Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])

myAppendNilRightNeutral : (l : List a) -> l ++ [] = l
myAppendNilRightNeutral [] = Refl
myAppendNilRightNeutral (x :: xs) =
    let rest = myAppendNilRightNeutral xs in
    cong rest

associative : (input : List a) -> (xs : List a) -> (input ++ [x]) ++ xs = input ++ x :: xs
associative [] xs = Refl
associative (x :: ys) xs =
    let rest = associative ys xs in
    cong rest

snocListHelp : (snoc : SnocList input) -> (rest : List a) -> SnocList (input ++ rest)
snocListHelp {input} snoc [] = rewrite myAppendNilRightNeutral input in snoc
snocListHelp {input} snoc (x :: xs) =
    let rest = snocListHelp (Snoc snoc {x}) xs in
    rewrite sym $ associative input xs {x} in rest -- snocListHelp (Snoc snoc {x}) xs

snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp SnocEmpty xs


--reverseSnoc : SnocList ty -> List ty
--reverseSnoc SnocEmpty = []
--reverseSnoc (Snoc xs x) = x :: reverseSnoc xs


total
myRevHelper : (input : List a) -> SnocList input -> List a
myRevHelper [] SnocEmpty = []
myRevHelper (xs ++ [x]) (Snoc rec) = x :: myRevHelper xs rec


myRev : List a -> List a
myRev xs with (snocList xs)
    myRev []          | SnocEmpty  = []
    myRev (ys ++ [x]) | (Snoc rec) = x :: myRev ys | rec

isSuffix : Eq a => List a -> List a -> Bool
isSuffix xs ys with (snocList xs)
    isSuffix [] ys          | SnocEmpty  = True
    isSuffix (xs ++ [x]) ys | (Snoc xsrec) with (snocList ys)
        isSuffix (xs ++ [x]) []          | (Snoc xsrec) | SnocEmpty    = False
        isSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec) | (Snoc ysrec) =
            if x == y
            then isSuffix xs ys | xsrec | ysrec
            else False

Position : Type
Position = (Double, Double)


AdderType : (numargs : Nat) ->  Type -> Type
AdderType Z numType  = numType
AdderType (S k) numType = (next : numType) -> AdderType  k numType

adder : (numargs : Nat) -> (acc : Nat) -> AdderType numargs Nat
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)

removeElem : DecEq a => (value : a) -> (xs : Vect (S n) a) -> Vect n a
removeElem value (x :: xs) = case decEq value x of
                                Yes prf   => xs

data MyElem : (x : a) -> Vect k a -> Type where
    MyHere : MyElem x (x :: xs)
    MyThere : MyElem x xs -> MyElem x (y :: xs)

-- ctrl alt D
oneInVctor : MyElem 1 [1, 2, 3]
oneInVctor = ?oneInVctor_rhs

twoIsThere : MyElem 3 [1, 2, 3, 4, 5, 6]
twoIsThere = MyThere (MyThere MyHere)

empties : Vect m (Vect 0 ty)
empties {m = Z} = []
empties {m = (S k)} = [] :: empties

trans : (matrix : Vect n (Vect m ty)) -> Vect m (Vect n ty)
trans [] = empties
trans (x :: xs) = ?trans_rhs_2


rev : Vect n a -> Vect n a
rev [] = []
rev {n=S k} (x :: xs) =
    let r = rev xs ++ [x] in
    rewrite plusCommutative 1 k in
    r
