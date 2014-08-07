module huffman

import Data.SortedSet

data Code : Type where
  Leaf   : Char -> Code
  Branch : SortedSet Char -> Code -> Code -> Code



data Bit = Zero | One

chars : Code -> SortedSet Char
chars (Leaf x) = insert x empty
chars (Branch x _ _) = x

encodeChar : Code -> Char -> List Bit
encodeChar (Leaf c')      c = Nil
encodeChar (Branch _ l r) c =
    if      contains c (chars l) then Zero :: encodeChar l c
    else if contains c (chars r) then One  :: encodeChar r c
    else error where error = error



exampleCode : Code
exampleCode = Branch (fromList abc) (Branch (fromList ab) (Leaf 'a') (Leaf 'b')) (Leaf 'c') where
  abc : List Char
  abc = 'a'::'b'::'c'::Nil
  ab : List Char
  ab = 'a'::'b'::Nil


