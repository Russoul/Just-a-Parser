module Me.Russoul.Text.Lexer

import Me.Russoul.Text.Position
import Me.Russoul.Text.Range
import Me.Russoul.Text.Lexer.Token


import Text.Bounded

---------------------- Abstract util ---------------------

apply2 : (Int -> Int, Int -> Int) -> Position -> Position
apply2 (f, g) (MkPosition x y) = MkPosition (f x) (g y)

compose2 : (b -> c, b' -> c') -> (a -> b, a' -> b') -> (a -> c, a' -> c')
compose2 (g, g') (f, f') = (g . f, g' . f')

[NLSepList]
(inner : Show a) => Show (List a) where
  show []        = ""
  show (x :: xs) = show x ++ show' xs
   where
    show' : List a -> String
    show' []        = ""
    show' (x :: xs) = "\n" ++ show x ++ show' xs

----------------------------------------------------------

accountFor : Char -> (Bool, Int -> Int, Int -> Int)
accountFor x = (isNL x || isSpace x, ifThenElse (isNL x) ((+ 1), const 0) (id, (+ 1)))

public export
data State = InSinglelineComment | InMultilineComment | AccWhitespace | Normal

||| Recusion principle for State.
state : a -> a -> a -> a -> State -> a
state inSinglelineComment inMultilineComment accWhitespace normal InSinglelineComment = inSinglelineComment
state inSinglelineComment inMultilineComment accWhitespace normal InMultilineComment = inMultilineComment
state inSinglelineComment inMultilineComment accWhitespace normal AccWhitespace = accWhitespace
state inSinglelineComment inMultilineComment accWhitespace normal Normal = normal

||| Populates bounds information.
||| Combines consecutive whitespace symbols into one token.
||| Combines single-line comments into one token.
export
mkWithBounds : (accW : State)
            -> state (Position, (Int -> Int, Int -> Int), SnocList Char)
                     (Position, (Int -> Int, Int -> Int), SnocList Char)
                     (Position, (Int -> Int, Int -> Int))
                     Position
                     accW
            -> List Char
            -> List (Range, Token)
mkWithBounds InSinglelineComment (p, delta, comment) [] =
  let p' = delta `apply2` p in
  [(MkRange p p', Comment comment)]
mkWithBounds InMultilineComment (p, delta, comment) [] =
  let p' = delta `apply2` p in
  [(MkRange p p', Comment comment)]
-- Remove the trailing whitespace
mkWithBounds AccWhitespace (p, delta) [] = []
mkWithBounds Normal _ [] = []
mkWithBounds Normal p ('-' :: '-' :: xs) =
  mkWithBounds InSinglelineComment (p, (id, (+ 2)), [<]) xs
mkWithBounds Normal p ('{' :: '-' :: xs) =
  mkWithBounds InMultilineComment (p, (id, (+ 2)), [<]) xs
mkWithBounds AccWhitespace (p, delta) ('-' :: '-' :: xs) =
  let p' = delta `apply2` p in
  let w = (MkRange p p', Whitespace) in
  w :: mkWithBounds InSinglelineComment (p', (id, (+ 2)), [<]) xs
mkWithBounds AccWhitespace (p, delta) ('{' :: '-' :: xs) =
  let p' = delta `apply2` p in
  let w = (MkRange p p', Whitespace) in
  w :: mkWithBounds InMultilineComment (p', (id, (+ 2)), [<]) xs
mkWithBounds Normal p (x :: xs) =
  let (isW, delta) = accountFor x in
  case isW of
    False =>
      let p' = delta `apply2` p in
      (MkRange p p', Symbol x) :: mkWithBounds Normal p' xs
    True => mkWithBounds AccWhitespace (p, delta) xs
mkWithBounds AccWhitespace (p, delta) (x :: xs) =
  let (isW, delta') = accountFor x in
  case isW of
    False =>
      let p' = delta `apply2` p in
      let p'' = (delta' `compose2` delta) `apply2` p in
      (MkRange p p', Whitespace) :: (MkRange p' p'', Symbol x) :: mkWithBounds Normal p'' xs
    True => mkWithBounds AccWhitespace (p, delta' `compose2` delta) xs
    -- This will fail on windows                  vvvv
mkWithBounds InSinglelineComment (p, delta, str) ('\n' :: xs) =
  let p' = ((+1), const 0) `apply2` (delta `apply2` p) in
  let comment = (MkRange p p', Comment str) in
  comment :: mkWithBounds Normal p' xs
    -- BUG:
    -- This will fail on windows (and not only?) vvvv
mkWithBounds InMultilineComment (p, delta, str) ('\n' :: xs) =
  -- As soon as we hit a new line,
  -- we ship a comment token and continue
  -- we do this to keep us to single-line semantic tokens only.
  let p' = ((+ 1), const 0) `apply2` (delta `apply2` p) in
  let comment = (MkRange p p', Comment str) in
  comment :: mkWithBounds InMultilineComment (p', (id, id), str) xs
mkWithBounds InMultilineComment (p, delta, str) ('-' :: '}' :: xs) =
  let p' = ((id, (+ 2)) `compose2` delta) `apply2` p in
  let comment = (MkRange p p', Comment str) in
  comment :: mkWithBounds Normal p' xs
mkWithBounds InSinglelineComment (p, delta, str) (x :: xs) =
  mkWithBounds InSinglelineComment (p, (id, (+ 1)) `compose2` delta, str :< x) xs
mkWithBounds InMultilineComment (p, delta, str) (x :: xs) =
  mkWithBounds InMultilineComment (p, (id, (+ 1)) `compose2` delta, str :< x) xs

export
filterOutComments : List (Range, Token) -> (SnocList Range, List (Range, Token))
filterOutComments [] = ([<], [])
filterOutComments ((range, Comment _) :: xs) =
  bimap (:< range) ((range, Whitespace) ::) (filterOutComments xs)
filterOutComments (x :: xs) =
  mapSnd (x ::) (filterOutComments xs)

export
mergeWhitespace : List (Range, Token) -> List (Range, Token)
mergeWhitespace [] = []
mergeWhitespace ((p, Whitespace) :: (p', Whitespace) :: xs) =
  mergeWhitespace ((union p p', Whitespace) :: xs)
mergeWhitespace (x :: xs) = x :: mergeWhitespace xs

export
removeLeadingWhitespace : List (Range, Token) -> List (Range, Token)
removeLeadingWhitespace [] = []
removeLeadingWhitespace ((_, Whitespace) :: xs) =
  removeLeadingWhitespace xs
removeLeadingWhitespace (x :: xs) = x :: xs

export
removeTrailingWhitespace : List (Range, Token) -> List (Range, Token)
removeTrailingWhitespace [] = []
removeTrailingWhitespace [(_, Whitespace)] = []
removeTrailingWhitespace (x :: xs) = x :: removeTrailingWhitespace xs

namespace Show.Token
  public export
  [BriefInst] Show Token where
    show (Symbol x) = cast x
    show Whitespace = " "
    show (Comment str) = "/"

  public export
  [WithBoundsBriefInst] Show (WithBounds Token) where
    show (MkBounded tok isIrr (MkBounds l c l' c')) =
      show @{BriefInst} tok ++ "(\{show l}:\{show c}-\{show l'}:\{show c'})"

  public export
  [WithBoundsBriefListInst] Show (List (WithBounds Token)) where
    show xs = show @{NLSepList @{WithBoundsBriefInst}} xs

export
tokenise : List Char -> (SnocList Range, List (Range, Token))
tokenise = mapSnd removeLeadingWhitespace
         . mapSnd removeTrailingWhitespace
         . mapSnd mergeWhitespace
         . filterOutComments  --vvvvvvvvvvvvvv We count starting at 0 for both axes,
         . mkWithBounds Normal (MkPosition 0 0) -- solely because LSP expects this format.
