module State


import Control.Monad.State

labelWith : Stream l -> List a -> List (l, a)
labelWith xs []                 = []
labelWith (lbl :: xs) (x :: ys) = (lbl, x) :: labelWith xs ys

data Tree a = Empty
            | Node (Tree a) a (Tree a)


flatten : Tree a -> List a
flatten Empty        = []
flatten (Node l x r) = flatten l ++ x :: flatten r


treeLabelWith : Stream ltype -> Tree a ->
                (Stream ltype, Tree (ltype, a))
treeLabelWith labels Empty        = (labels, Empty)
treeLabelWith labels (Node l x r) =
    let (this :: left, ltree) = treeLabelWith labels l
        (right, rtree) = treeLabelWith left r in
    (right, Node ltree (this, x) rtree)

increase : Nat -> State Nat ()
increase k = do current <- get
                put (current + k)


treeLabelWithState : Tree a -> State (Stream ltype) (Tree (ltype, a))
treeLabelWithState Empty = pure Empty
treeLabelWithState (Node l x r)
    = do left_labelled <- treeLabelWithState l
         (this :: rest) <- get
         put rest
         right_labelled <- treeLabelWithState r
         pure (Node left_labelled (this, x) right_labelled)


update : (s -> s) -> State s ()
update f = do value <- get
              let newValue = f value
              put newValue

try : State Nat String
try = do v <- get
         pure ?dede

countEmpty : Tree a -> State Nat ()
countEmpty Empty        = update S
countEmpty (Node l _ r)
    = do v <- get
         let lvalue = execState (countEmpty l) v
         let rvalue = execState (countEmpty r) v
         put (plus lvalue rvalue)

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty        = update (\ (e, n) => (S e, n))
countEmptyNode (Node l x r) = do v <- get
                                 let (_, result) = runState (countEmptyNode l) v
                                 let (_, value) = runState (countEmptyNode r) result
                                 put value
