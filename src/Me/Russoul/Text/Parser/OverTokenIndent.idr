module Me.Russoul.Text.Parser.OverTokenIndent

import Me.Russoul.Data.Location
import Me.Russoul.Text.Lexer.Token
import Me.Russoul.Text.Parser

import Data.String.Extra
import Data.Fin
import Data.SnocList

||| Indentation level
public export
record Indent where
  [noHints]
  constructor MkIndent
  column : Int

||| Indentation level & user state
public export
record State s where
  constructor MkState
  base : Indent
  skip : Bool
  user : s

||| Specialised type of grammars
public export
Rule : Type -> Type -> Type
Rule s a = Grammar (State s) Token a

export
getBaseIndent : Rule s Indent
getBaseIndent = base <$> get

export
getIndent : Rule s Indent
getIndent = MkIndent <$> column

export
setBaseIndent : Indent -> Rule s ()
setBaseIndent x = update {base := x}

||| Check that the indentation of the next token matches the target level
export
aligned : Indent -> Rule s ()
aligned info = do
  col <- column
  guard "Misalignment" (col == info.column)
  update {skip := True}

||| Parse one token with the given condition.
||| The token must be indented strictly more than the base.
export
terminal : String -> (Token -> Maybe a) -> Rule s a
terminal ruleName f = do
  st <- get
  col <- column
  guard ("\{ruleName}: indentation check failed") (st.skip || col > st.base.column)
  result <- Text.Parser.terminal ruleName f
  update {skip := False}
  pure result

%hide Text.Parser.terminal
%hide Text.Parser.is

||| Read the token and succeed if it matches the predicate.
export
is : String -> (Token -> Bool) -> Rule s Token
is msg f = terminal msg (\x => toMaybe (f x) x)

public export
char : Char -> Rule s Token
char x = is ("Expected symbol: " ++ cast x) (isSymbol (== x))

public export
char_ : Char -> Rule s ()
char_ = ignore . char

namespace List1
  public export
  str : List1 Char -> Rule s (List1 Token)
  str (x ::: []) = map singleton (char x)
  str (x ::: a :: as) = map cons (char x) <*> str (a ::: as)

namespace String
  public export
  str : String -> Rule s (List1 Token)
  str s =
    case unpack s of --FIX: RETHINK THIS
      [] => fail "[Internal error] Attempt to parse an empty string"
      (x :: xs) => List1.str (x ::: xs) <|> fail "Expected string: \{s}"

public export
str_ : String -> Rule s ()
str_ = ignore . str

public export
noIndent : Indent
noIndent = MkIndent 0
