module Me.Russoul.Text.Lexer.Token

import Data.SnocList

public export
data Token : Type where
 ||| Can't be whitespace
 Symbol : Char -> Token
 ||| Fusion of consecutive whitespace symbols, including newline (' ', '\n', etc.)
 Whitespace : Token
 ||| Fusion of symbols that are part of a comment. Can't cross line boundary
 Comment : SnocList Char -> Token

public export
Show Token where
  show (Symbol c) = "Symbol \{show c}"
  show Whitespace = "Whitespace"
  show (Comment com) = "Comment \{show com}"

public export
isSymbol : (Char -> Bool) -> Token -> Bool
isSymbol f (Symbol x) = f x
isSymbol f _ = False

public export
isSpace : Token -> Bool
isSpace Whitespace = True
isSpace _ = False

public export
isComment : Token -> Bool
isComment (Comment _) = True
isComment _ = False

public export
isToken : Token -> Bool -> Token -> Maybe Token
