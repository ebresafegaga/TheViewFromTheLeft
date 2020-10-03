module STLC

import Data.Fin
import Data.Vect

%default total

data Sg : (a : Type) -> (f : a -> Type) -> Type where
    Sigma : (x : a) -> f x -> Sg a f

record Sg' (a : Type) (f : a -> Type) where
    constructor MkSigma
    fst : a
    snd : f fst

Evidence : Sg Nat $ \ n => Nat
Evidence = Sigma 0 0

(>>=) : Nat -> Nat -> Type
m     >>= Z     = ()
Z     >>= (S n) = Void
(S m) >>= (S n) = m >>= n

difference : (m, n : Nat) -> m >>= n -> Sg Nat $ \ d => m = (n + d)
difference m Z prf         = Sigma m Refl
difference Z (S n) prf     impossible
difference (S m) (S n) prf with (difference m n prf)
    difference (S (plus n d)) (S n) prf | (Sigma d Refl) = Sigma d Refl

data TExp : Type where
    O : TExp
    (>>) : (s : TExp) -> (t : TExp) -> TExp

data Expr : Nat -> Type where
    EVar : (i : Fin n) -> Expr n
    EApp : (f : Expr n) -> (s : Expr n) -> Expr n
    ELam : (s : TExp) -> (t : Expr (S n)) -> Expr n

data In : (xs : List a) -> (x : a) -> Type where
    RightHere : In (x :: xs) x
    OverThere : (i : In xs y) -> In (x :: xs) y

(\\) : In xs x -> (x : a) -> Fin (length xs)
RightHere \\ x = ?op_rhs_2
input \\ x = ?op_rhs_3


--"Programming with these ‘fake’ dependent types is an entertaining challenge,
--but let’s be clear: these techniques are cleverly dreadful, rather than dreadfully
--clever"

data Tree : (n : Type) -> (l : Type) -> Type where
    Leaf : l -> Tree n l
    Node : n -> Tree n l -> Tree n l -> Tree n l

%name Tree t, tree

mymerge : List Nat -> List Nat -> List Nat
mymerge []        ys        = ys
mymerge xs        []        = xs
mymerge (x :: xs) (y :: ys) with (x < y)
    | False = y :: mymerge (x :: xs) ys
    | True  = x :: mymerge xs (y :: ys)

flatten : Tree n (Maybe Nat) -> List Nat
flatten (Leaf Nothing)      = []
flatten (Leaf (Just x))     = [x]
flatten (Node _ left right) = mymerge (flatten left) (flatten right)

insert : Nat -> Tree Bool (Maybe Nat) -> Tree Bool (Maybe Nat)
insert k (Leaf Nothing)    = Leaf (Just k)
insert k l@(Leaf (Just x)) = Node True l (Leaf (Just k))
insert k (Node False l r)  = Node True l (insert k r)
insert k (Node True l r)   = Node False (insert k l) r

share : List Nat -> Tree Bool (Maybe Nat)
share []        = Leaf Nothing
share (x :: xs) = insert x (share xs)

sort : List Nat -> List Nat
sort = flatten . share



partitionEithers : List (Either a b) -> (List a, List b)
partitionEithers []              = ([], [])
partitionEithers (Left l :: xs)  = ?partitionEithers_rhs_1
partitionEithers (Right r :: xs) = ?partitionEithers_rhs_3


vec : a -> Vect n a
vec {n =Z} x   = []
vec {n =S n} x = x :: vec {n} x

va : Vect n (a -> b) -> Vect n a -> Vect n b
va []        []        = []
va (f :: fs) (x :: xs) = f x :: va fs xs

transpose' : Vect i (Vect j x) -> Vect j (Vect i x)
transpose' []          = vec []
transpose' (xj :: xij) = va (va (vec (::)) xj) (transpose' xij)

vmap : (a -> b) -> Vect n a -> Vect n b
vmap f xs = va (vec f) xs

vZipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
vZipWith f xs ys = va (va (vec f) xs) ys

vdot : Vect n Nat -> Vect n Nat -> Nat
vdot xs ys = sum $ vZipWith (*) xs ys

Matrix : Nat -> Nat -> Type
Matrix k j = Vect k (Vect j Nat)

mProduct : Matrix a n -> Matrix n b -> Matrix a b
mProduct {n} {b} m1 m2 = vmap (\ row => vmap (\ cols => vdot row cols) m2') m1
    where
         m2' : Matrix b n
         m2' = transpose m2

zero : Matrix i j -> Matrix i j
zero mat = vmap (\ row => vec 0) mat

gen : Nat ->  Vect n Nat
gen {n = Z} k     = []
gen {n = (S j)} k = k :: gen (k+1)

identity : Matrix i i -> Matrix i i
identity = help 0 . zero where
    help : Nat -> Matrix i j -> Matrix i j
    help k []          = []
    help k (xs :: xss) =
        let result = vZipWith (\ x, i => if i == k then 1 else x) xs (gen 0) in
        result :: help (k+1) xss

mat : Matrix 3 3
mat =  [ [1, 2, 3], [1, 2, 3], [1, 2, 3] ]

mMatByVec : Matrix m n -> Vect n Nat -> Vect m Nat
mMatByVec mat vec = vmap (\ row => vdot row vec) mat

mMatCompose : Matrix a n -> Matrix n b -> Matrix a b
mMatCompose m1 []        = ?mMatCompose_rhs_1
mMatCompose m1 (x :: xs) = ?mMatCompose_rhs_2

--multOneRightNeutral
--multZeroRightZero
--plusZeroRightNeutral

sextprf : (k, j : Nat) -> (plus k (plus j (mult k j))) = (plus j (mult k (S j)))
sextprf Z j     = Refl
sextprf (S k) Z =
    rewrite multOneRightNeutral k in
    rewrite multZeroRightZero k in
    rewrite plusZeroRightNeutral k in
    Refl
sextprf (S k) (S j) =
    rewrite sym $ sextprf k j in
    ?here

join' : Vect a (Vect b x) -> Vect (a * b) x
join' {a = Z}{b = _} xs = []
join' {a = a}{b = Z} xs = rewrite multZeroRightZero a in []
join' (xs :: xss)       =
    --let therest = join' (xs :: xss) in
    --let tails = vmap tail xss
    --    heads = vmap head xss
    --    result = heads ++ join' tails in
    --rewrite sym $ sextprf k j in result
    xs ++ join' xss

fmax : Fin (S n)
fmax {n = Z}     = FZ
fmax {n = (S k)} = FS fmax

fweak : Fin n -> Fin (S n)
fweak FZ     = FZ
fweak (FS x) = FS (fweak x)

vproj : Vect n x -> Fin n -> x
vproj (y :: xs) FZ     = y
vproj (y :: xs) (FS x) = vproj xs x

vtab : (Fin n -> x) -> Vect n x
vtab {n = Z} f     = []
vtab {n = (S k)} f = f fmax :: (vtab $ \ fin => f (fweak fin))


data OPF : (m : Nat) -> (n : Nat) -> Type where
    OZero : OPF 0 0
    OSame : OPF m n -> OPF (S m) (S n)
    OLeft : OPF m n -> OPF m (S n)


opf : (f : OPF m n) -> (i : Fin m) -> Fin n
opf OZero i          = i
opf (OSame x) FZ     = FZ
opf (OSame x) (FS y) = FS (opf x y)
opf (OLeft x) FZ     = FZ
opf (OLeft x) y      = fweak (opf x y)

a : Vect 5 Nat
a = [1, 2, 3, 4, 5]

seco : Fin 3
seco =  FS FZ


iOPF : OPF n n
iOPF {n =Z}   = OZero
iOPF {n =S k} = OSame iOPF

cOPF :  OPF l m -> OPF m n -> OPF l n
cOPF OZero y             = y
cOPF (OSame x) (OSame y) = OSame (cOPF x y)
cOPF x (OLeft y)         = OLeft (cOPF x y)
cOPF (OLeft x) (OSame y) = OLeft (cOPF x y)

five : OPF 3 5
five = OLeft (OLeft (OSame (OSame (OSame OZero))))

six : OPF 5 8
six = OSame (OSame (OSame (OSame (OSame (OLeft (OLeft (OLeft OZero)))))))

three : OPF 3 8
three = cOPF five six


sss : OPF 3 5
--sss = OSame (OSame (OLeft (OLeft OZero)))

aaa : OPF 1 1


fFin : Fin n -> Nat
fFin FZ     = Z
fFin (FS x) = S (fFin x)


data BoundCheck : Nat -> Nat -> Type where
    InsideBound : (i : Fin n) -> BoundCheck n (fFin i)
    OutsideBound : (m : Nat) -> BoundCheck n (n + m)

boundCheck : (n, m : Nat) -> BoundCheck n m
boundCheck Z m      = OutsideBound m
boundCheck (S k) Z  = InsideBound FZ
boundCheck (S k) (S j) with (boundCheck k j)
    boundCheck (S k) (S (fFin i)) | (InsideBound i)  = InsideBound (FS i)
    boundCheck (S k) (S (k + m))  | (OutsideBound m) = OutsideBound m



data FinView : Fin n -> Type where
    Fmax : FinView fmax
    FWeak : (i : Fin n) -> FinView (fweak i)

finView : (i : Fin n) -> FinView i
finView FZ     = Fmax
finView (FS x) with (finView x)
    finView (FS x)         | Fmax      = ?finView_rhs_2_rhs_1
    finView (FS (fweak i)) | (FWeak i) = ?finView_rhs_2_rhs_2


toInt : Fin n -> Nat
toInt x = ?toInt_rhs


infixl 1 <<=

data (<<=) : Nat -> Nat -> Type where
    OZ : 0 <<= 0
    OS : m <<= n -> S m <<= S n
    O' : m <<= n -> m <<= S n



anum : 5 <<= 10
anum = OS (OS (OS (OS (OS (O' (O' (O' (O' (O' OZ)))))))))


vTake : GTE m n -> Vect m a -> Vect n a
vTake LTEZero _               = []
vTake (LTESucc prf) (x :: xs) = x :: vTake prf xs

transGTE : (n : Nat) -> GTE n n
transGTE Z     = LTEZero
transGTE (S k) = LTESucc (transGTE k)

vTakeIdFact : (xs : Vect n a) -> vTake (transGTE n) xs = xs
vTakeIdFact [] = Refl
vTakeIdFact {n=S len} (x :: xs) with (vTakeIdFact xs)
    vTakeIdFact {n=S len} (x :: xs) | q with (vTake (transGTE len) xs)
        vTakeIdFact {n=S len} (x :: xs) | Refl | xs = Refl

 -- with (vTakeIdFact xs)
    --vTakeIdFact (x :: xs) | q = ?dedede_rhs
--5

 --rewrite vTakeIdFact xs in ?deded
-- "rewrite is just a fancy notation of saying abstract the left hand side of the equation using with
-- , abstract the proof of the equation using with and pattern match on the proof"

data Split : Nat -> Nat -> Nat -> Type where
    ZZZ : Split 0 0 0
    LLL : Split l m r -> Split (S l) (S m) r
    RRR : Split l m r -> Split l (S m) (S r)

slt : Split 4 7 3
slt = LLL (RRR (LLL (LLL (RRR (RRR (LLL ZZZ))))))

pack : Vect l a -> Split l m r -> Vect r a -> Vect m a
pack [] ZZZ []              = []
pack (x :: xl) (LLL nnn) xr = x :: pack xl nnn xr
pack xl (RRR nnn) (x :: xr) = x :: pack xl nnn xr


data FindSplit : (nnn : Split l m r) -> Vect m x -> Type where
    SplitBits : (xl : Vect l x) -> (xr : Vect r x) -> FindSplit nnn (pack xl nnn xr)

findSplit : (nnn : Split l m r) -> (xs : Vect m x) -> FindSplit nnn xs
findSplit ZZZ []              = SplitBits [] []
findSplit (LLL nnn) (x :: xs) with (findSplit nnn xs)
    findSplit (LLL nnn) (x :: (pack xl nnn xr)) | (SplitBits xl xr) = SplitBits (x ::  xl) xr
findSplit (RRR nnn) (x :: xs) with (findSplit nnn xs)
    findSplit (RRR nnn) (x :: (pack xl nnn xr)) | (SplitBits xl xr) = SplitBits xl (x :: xr)


sumV : Vect 11 Nat
sumV = vTake (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc ?dede1)))))) [1, 2, 3, 4, 5, 6]
