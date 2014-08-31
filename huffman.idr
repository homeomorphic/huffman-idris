module Main

import Data.List
%default total

data Code : List Char -> Type where
  Leaf   : {c: Char} -> Code (c::Nil)
  Branch : {lcs, rcs: List Char} -> (Code lcs) -> (Code rcs) -> Code (lcs ++ rcs)


data Bit = Zero | One

instance Show Bit where
    show Zero = "0"
    show One = "1"


notInTail : (Elem x (y::ys) -> _|_) -> (Elem x ys -> _|_)
notInTail f pf = f (There pf)

inSecond : (lcs: List Char) -> (rcs: List Char) -> (Elem c (lcs ++ rcs)) -> (Elem c lcs -> _|_) -> Elem c rcs
inSecond []        rcs inBoth notInFirst = inBoth
inSecond (c :: xs) rcs Here notInFirst = FalseElim (notInFirst Here)
inSecond (x :: xs) rcs (There y) notInFirst = inSecond xs rcs y (notInTail notInFirst)

encodeChar : Code cs -> (c: Char) -> Elem c cs -> List Bit
encodeChar Leaf _ pf  = Nil
encodeChar (Branch {lcs} {rcs} l r) c pf 
    with (isElem c lcs)
      | Yes pf2 = Zero :: encodeChar l c pf2
      | No  pf3 =  One :: encodeChar r c (inSecond lcs rcs pf pf3)

decodeChar : Code cs -> List Bit -> Maybe Char
decodeChar (Leaf {c = c}) [] = Just c
decodeChar (Leaf {c = c}) (x :: xs) = Nothing
decodeChar (Branch x y) [] = Nothing
decodeChar (Branch x y) (c::cs) = case c of
                                        Zero => decodeChar x cs
                                        One  => decodeChar y cs


singletonList : Elem c [c'] -> c = c'
singletonList Here = ?singletonList_rhs_1
singletonList (There x) = ?singletonList_rhs_2

decodeWorks : (code: Code cs) -> (c: Char) -> (pf: Elem c cs) -> (Just c = (decodeChar code (encodeChar code c pf)))
decodeWorks Leaf c pf = ?works
decodeWorks (Branch {lcs} {rcs} lc rc) c pf with (isElem c lcs)
    | Yes pf2 = let ih = decodeWorks lc c pf2 in ?works_2
    | No  pf3 = let ih = decodeWorks rc c (inSecond lcs rcs pf pf3) in ?works_3

exampleCode : Code ('a'::'b'::'c'::Nil)
exampleCode = abc where
    a : Code ('a':: Nil)
    b : Code ('b':: Nil)
    c : Code ('c':: Nil)
    ab : Code ('a'::'b'::Nil)
    abc : Code ('a'::'b'::'c'::Nil)
    a = Leaf
    b = Leaf
    c = Leaf
    ab = Branch a b
    abc = Branch ab c

main : IO ()
main = do
    let encoded = (encodeChar exampleCode 'b' (believe_me ())) -- (There (There Here)))
    print encoded
    print $ decodeChar exampleCode encoded

---------- Proofs ----------

Main.works_3 = proof
  intros
  trivial


Main.works_2 = proof
  intros
  trivial


Main.works = proof
  intros
  rewrite (singletonList pf)
  trivial


Main.singletonList_rhs_2 = proof
  intros
  exact FalseElim (uninhabited x)



Main.singletonList_rhs_1 = proof
  intros
  trivial


