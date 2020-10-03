module Main

curry' : ((a, b) -> c) -> a -> b -> c
curry' f x y = f (x, y)


plus' : Nat -> Nat -> Nat
plus' Z j = j
plus' (S k) j = S (plus' k j)

data Vect : Nat -> Type -> Type where
    Nil : Vect Z a
    (::) : a -> Vect n a -> Vect (S n) a



zipWithVec : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWithVec f [] [] = []
zipWithVec f (x :: z) (y :: w) = f x y :: zipWithVec f z w


repeat : (n : Nat) -> (x : a) -> Vect n a
repeat Z x = []
repeat (S k) x = x :: repeat k x


take : (n : Nat) -> Vect (n+k) a -> Vect n a
take Z x = []
take (S k) (x :: xs) = x :: take k xs


map : List a -> (a -> b) -> List b
map [] f = []
map (x :: xs) f = f x :: map xs f


fourElts : (n : Nat ** Vect n Int)
fourElts = (4 ** [1, 2, 3, 4])

filter : (a -> Bool) -> Vect n a -> (m ** Vect m a)
filter f [] = (_ ** [])
filter f (x :: xs) =
    let (len ** rest) = filter f xs
    in if f x
        then (_ ** x :: rest)
        else (_ ** rest)

namespace HList
    data HList : List Type -> Type where
        Nil : HList []
        (::) : t -> HList ts -> HList (t :: ts)

mixed : HList [String, Nat, Integer]
mixed = ["Hello", 42, 16]


(++) : HList as -> HList bs -> HList (as ++ bs)
(++) [] y = y
(++) (x :: z) y = x :: z ++ y

symmetry : x = y -> y = x
symmetry Refl = Refl

congruence : {f : a -> b} -> x = y -> f x = f y
congruence Refl = Refl


sulp : Nat -> Nat -> Nat
sulp k Z = k
sulp k (S j) = S (sulp k j)

sulpZeroNeutral : (k : Nat) -> k = sulp 0 k
sulpZeroNeutral Z = Refl
sulpZeroNeutral (S k) = cong (sulpZeroNeutral k)

sulpAddOneMIsSuccM : (m : Nat) -> sulp 1 m = S m
sulpAddOneMIsSuccM Z = Refl
sulpAddOneMIsSuccM (S k) = cong (sulpAddOneMIsSuccM k)

sulpSucckIsSuccJ : (k, j : Nat) -> sulp (S k) j = sulp k (S j)
sulpSucckIsSuccJ Z j =
    rewrite sulpAddOneMIsSuccM j in
    rewrite sym $ sulpZeroNeutral j in  Refl
sulpSucckIsSuccJ (S k) j =
    rewrite sulpSucckIsSuccJ k j in
    ?hole

sulpLeftAdd : (n,m : Nat) -> sulp (S n) m = S (sulp n m)
sulpLeftAdd Z m = rewrite sym $ sulpZeroNeutral m in sulpAddOneMIsSuccM m
sulpLeftAdd (S k) j =
    rewrite sulpSucckIsSuccJ (S k) j in Refl

appendHard : Vect n a -> Vect m a -> Vect (sulp n m) a
appendHard {m} [] ys =
    rewrite sym $ sulpZeroNeutral m in ys
appendHard {m} (x :: xs) ys =
    let rest = appendHard xs ys in
    -- rewrite sulpLeftAdd _ m in
    ?goal (x :: rest)

data SnocList : List a -> Type where
    Empty : SnocList []
    Snoc  : (xs : List a) -> (x : a) -> SnocList (xs ++ [x])

snocced : (xs : List a) -> SnocList xs
snocced [] = Empty
snocced (x :: xs) with (snocced xs)
    snocced (x :: [])          | Empty       = Snoc [] x
    snocced (x :: (ys ++ [y])) | (Snoc ys y) = Snoc (x :: ys) y

rot : List a -> List a
rot xs with (snocced xs)
    rot []          | Empty       = []
    rot (ys ++ [x]) | (Snoc ys x) = x :: ys

myUnzip : List (a, b) -> (List a, List b)
myUnzip [] = ([], [])
myUnzip ((a, b) :: xs) with (myUnzip xs)
  | (left, right) = ?verclassy -- (a :: left, b :: right)


data UnZip : List (a, b) -> Type where
    ZipEmpty : UnZip []
    ZipElem : (xs : List a) -> (ys : List b) -> UnZip (zip xs ys)

unZip : (xs : List (a, b)) ->  UnZip xs
unZip [] = ZipEmpty
unZip ((x, y) :: rest) with (unZip rest)
    unZip ((x, y) :: [])          | ZipEmpty        = ZipElem [x] [y]
    unZip ((x, y) :: (zip xs ys)) | (ZipElem xs ys) = ZipElem (x :: xs) (y :: ys)


data Compare : Nat -> Nat -> Type where
    Lt : (x : Nat) -> (y : Nat) -> Compare x (x + S y)
    Eq : (x : Nat) -> Compare x x
    Gt : (x : Nat) -> (y : Nat) -> Compare (y + S x) y

compare' : (x : Nat) -> (y : Nat) -> Compare x y
compare' Z Z     = Eq Z
compare' Z (S n) = Lt Z n
compare' (S m) Z = Gt m Z
compare' (S m) (S n) with (compare' m n)
    compare' (S x) (S (x + (S y))) | (Lt x y) = Lt (S x) y
    compare' (S x) (S x)           | (Eq x)   = Eq (S x)
    compare' (S (y + (S x))) (S y) | (Gt x y) = Gt x (S y)


data Comp : Nat -> Nat -> Type where
    Lthan : (x : Nat) -> (y : Nat) -> Comp x (x + y)
    Equal : (x : Nat) -> Comp x x
    Gthan : (x : Nat) -> (y : Nat) -> Comp (y + x) y


comp : (x : Nat) -> (y : Nat) -> Comp x y
comp Z Z = Equal 0
comp Z (S k) = Lthan Z (S k)
comp (S k) Z = Gthan (S k) 0
comp (S k) (S j) with (comp k j)
    comp (S k) (S (k + y)) | (Lthan k y) = Lthan (S k) y
    comp (S j) (S j)       | (Equal j)   = Equal _
    comp (S (j + x)) (S j) | (Gthan x j) = Gthan x (S j)


plusZeroIdentity' : (x : Nat) -> x `plus` 0 = x
plusZeroIdentity' Z = ?plusZeroIdentity'_rhs_1
plusZeroIdentity' (S k) = ?plusZeroIdentity'_rhs_2


mylength : List a -> Nat
mylength [] = Z
mylength (x :: xs) = S (mylength xs)


myappend : Vect n a -> Vect m a -> Vect (n + m) a
myappend [] ys = ys
myappend (x :: xs) ys = x :: myappend xs ys


data ElemAt : Nat -> Type -> List xs -> Type where
    AtZ : ElemAt Z t (t :: ts)
    AtS : ElemAt k t ts -> ElemAt  (S k) t (u :: ts)


plusAssoc : (l, c, r : Nat) -> (l `plus` c) `plus` r =  l `plus` (c `plus` r)
plusAssoc Z c r = Refl
plusAssoc (S k) c r = rewrite plusAssoc k c r in Refl -- cong (plusAssoc k c r)

data Fin : Nat -> Type where
    FZ : Fin (S k)
    FS : Fin k -> Fin (S k)

index : Fin n -> Vect n a -> a
index FZ (x :: xs) = x
index (FS fin) (x :: xs) = index fin xs

data Elem : a -> Vect n a -> Type where
    Here : {x : a} -> {xs : Vect n a} -> Elem x (x :: xs)
    There : {x,y :a} -> {xs : Vect n a} -> Elem x xs -> Elem x (y :: ys)

data Parity : Nat -> Type where
    Even : Parity (n+n)
    Odd : Parity (S (n+n))

parity : (n : Nat) -> Parity n
parity Z = Even {n=Z}
parity (S Z) = Odd {n=Z}
parity (S (S k)) with (parity k)
    parity _ | Even = ?goal_1
    parity _ | Odd = ?goal_2




natToBin : Nat -> List Bool
natToBin Z = []
natToBin k with (parity k)
    natToBin (n + n)     | Even = False :: natToBin n
    natToBin (S (n + n)) | Odd = True :: natToBin n


oneIsAddOne : (n : Nat) -> (1+n) = S n
oneIsAddOne Z = Refl
oneIsAddOne (S k) = Refl

incr : Nat -> Nat
incr = (+ 1)

addIsIncr : (n : Nat) -> (S n) = incr n
addIsIncr Z = Refl
addIsIncr (S k) =
    let rest = addIsIncr k in
    cong rest

combK : a -> e -> a
combK = \ a, e => a

combS : (e -> s -> v) -> (e -> s) -> e -> v
combS = \ esv, es, e => esv e (es e)

myId : a -> a
myId {a} = combS combK (combK {e=a})

plusProve : (n : Nat) -> (n + Z) = n
plusProve Z = Refl
plusProve (S k) =
    let rest = plusProve k in
    cong rest

-- Lenard Iverson,
-- definitive paper on compiling pattern matching
-- Works at Google

data Zero : Type where

data One : Type where
    One' : One


(>=) : Nat -> Nat -> Type
x >= Z = One
Z >= (S x) = Zero
(S x) >= (S y) = x >= y

self : (n : Nat) -> n >= n
self Z = One'
self (S k) = self k

transG : (x, y, z :Nat) -> x >= y -> y >= z -> x >= z
transG x y Z p1 p2 = One'
transG Z Z (S k) p1 p2  impossible
transG Z (S j) (S k) p1 p2 impossible
transG (S j) Z (S k) p1 p2 impossible
transG (S j) (S i) (S k) p1 p2 = transG j i k p1 p2

pIsS : (n : Nat) -> (plus n 1) = S n
pIsS Z = Refl
pIsS (S k) =
    rewrite pIsS k in Refl

plusS1Eq2 : (n : Nat) ->  plus n (S Z) = S n
plusS1Eq2 Z = Refl
plusS1Eq2 (S k) = rewrite plusS1Eq2 k in Refl

data Sigma : (a : Type) -> (T : a -> Type) -> Type where
    Sg : {T: a -> Type} -> (x : a) -> T x -> Sigma a T

difference : (m, n : Nat) -> m >= n -> Sigma Nat (\d => m = (n+d))
difference m Z p = Sg m Refl
difference Z (S k) p impossible
difference (S j) (S k) p with (difference j k p)
    | (Sg d q) = ?kekkdd --rewrite q in (Sg d Refl) --(cong q)

vTake : (m, n : Nat) -> (m >= n) -> Vect m a -> Vect n a
vTake m Z p xs = []
vTake Z (S k) p xs impossible
vTake (S j) (S k) p (x :: xs) = x :: vTake j k p xs


data Bit = I | O

or : Bit -> Bit -> Bit
or I y = I
or O y = y

orAddoc : (a : Bit) -> (b : Bit) -> (c : Bit) ->
        (a `or` b) `or` c = a `or` (b `or` c)
orAddoc I b c = Refl
orAddoc O b c = Refl

BitString : Type
BitString = List Bit

bsor : BitString -> BitString -> BitString
bsor [] y = ?bsor_rhs_1
bsor (x :: xs) y = ?bsor_rhs_2


notTrue : (S (S a)) = 1 -> Void
notTrue Refl impossible

(>>) : (a -> a') -> (b -> b') -> (a, b) -> (a', b')
(>>) f g (a, b) = (f a, g b)






main : IO ()
main = putStrLn (cast 'c')
