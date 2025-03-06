module Me.Russoul.Text.Parser.OverChar

import public Me.Russoul.Text.Parser
import public Me.Russoul.Data.Location

import Data.Either
import Data.Fin
import Data.List
import Data.List1
import Data.Maybe
import Data.String

import Text.Lexer

------------- Utilities for grammars over Char ----------------

public export
Digit : Type
Digit = Fin 10

public export
Rule : (s : Type) -> (ty : Type) -> Type
Rule s ty = Grammar s Char ty

export
toString : Foldable t
        => Rule s (t Char)
        -> Rule s String
toString p = map (foldr (\char, str => cast char ++ str) "") p

export
lower : Rule s Char
lower = terminal "lower" (\x => toMaybe (isLower x) x)

export
upper : Rule s Char
upper = terminal "upper" (\x => toMaybe (isUpper x) x)

export
alpha : Rule s Char
alpha = terminal "alpha" (\x => toMaybe (isAlpha x) x)

public export
mbDigit : Char -> Maybe Digit
mbDigit '0' = Just 0
mbDigit '1' = Just 1
mbDigit '2' = Just 2
mbDigit '3' = Just 3
mbDigit '4' = Just 4
mbDigit '5' = Just 5
mbDigit '6' = Just 6
mbDigit '7' = Just 7
mbDigit '8' = Just 8
mbDigit '9' = Just 9
mbDigit _   = Nothing

export
digit : Rule s Digit
digit = terminal "digit" mbDigit

export
digits : Rule s (List1 Digit)
digits = some digit

littleEndianBase10ToNat : List Digit -> Nat
littleEndianBase10ToNat [] = 0
littleEndianBase10ToNat (x :: xs) = finToNat x + 10 * littleEndianBase10ToNat xs

||| Big-endian string of base10 digits to Nat
public export
[BigEndianBase10] Cast (List1 Digit) Nat where
  cast = littleEndianBase10ToNat . forget . reverse

public export
nat : Rule s Nat
nat = map (cast @{BigEndianBase10}) digits

||| A two-digit base-10 natural number.
||| Leading zeros are allowed.
export
twoDigitNat : Rule s Nat
twoDigitNat = do
  d0 <- digit
  d1 <- digit
  pure (10 * finToNat d0 + finToNat d1)

export
alphaNum : Rule s Char
alphaNum = terminal "alphanumeric" (\x => toMaybe (isAlphaNum x) x)

export
space : Rule s ()
space = terminal "space" (\x => ignore $ toMaybe (x == ' ') x)

||| Parse an exact char. Case-sensetive.
export
char : Char -> Rule s Char
char c = terminal (cast c) (\x => toMaybe (x == c) x)

||| Parse an exact char. Case-sensetive. Ignore the result.
export
char_ : Char -> Rule s ()
char_ = ignore . char

||| Parse a chacter such that condition holds
export
such : (Char -> Bool) -> Rule s Char
such cond = terminal "notChar" (\x => toMaybe (cond x) x)

||| Parse one char from the list.
||| Prefer ones closer to the head of the list.
||| Fail if the list is empty or none of the chars matches.
export
oneOf : String -> Rule s Char
oneOf str =
  case fastUnpack str of
    [] => fail "oneOf \"\""
    x :: rest => char x <|> go rest
 where
  go : List Char -> Rule s Char
  go [] = fail "oneOf: no match"
  go (x :: xs) = char x <|> go xs

||| Rule an exact char. Case-insensetive.
export
charLike : Char -> Rule s Char
charLike c =
  char (toLower c) <|> char (toUpper c)

||| Non-empty string. Case-sensitive.
export
str : String -> Rule s String
str c =
  case fastUnpack c of
    [] => fail "str \"\""
    x :: xs => toString $
      seqList1 (map char (x ::: xs))

||| Non-empty string. Case-sensitive. Ignore the result.
export
str_ : String -> Rule s ()
str_ = ignore . str

export
newline : Rule s ()
newline =  str_ "\r\n" <|> str_ "\n"

||| Non-empty string. Case-insensitive.
export
strLike : String -> Rule s String
strLike c =
  case fastUnpack c of
    [] => fail "strLike \"\""
    x :: xs => toString $
      seqList1 (map charLike (x ::: xs))

public export
subscriptDigit : Rule s Digit
subscriptDigit =
  is "₀" (== '₀') $> 0
    <|>
  is "₁" (== '₁') $> 1
    <|>
  is "₂" (== '₂') $> 2
    <|>
  is "₃" (== '₃') $> 3
    <|>
  is "₄" (== '₄') $> 4
    <|>
  is "₅" (== '₅') $> 5
    <|>
  is "₆" (== '₆') $> 6
    <|>
  is "₇" (== '₇') $> 7
    <|>
  is "₈" (== '₈') $> 8
    <|>
  is "₉" (== '₉') $> 9

public export
subscriptDigits : Rule s (List1 Digit)
subscriptDigits = some subscriptDigit

public export
subscriptNat : Rule s Nat
subscriptNat = do
  n <- subscriptDigits
  pure (convert ([<] <>< (forget n)) 1)
 where
  -- decimal = {1, 10, 100, ...}
  convert : SnocList Digit -> (decimal : Nat) -> Nat
  convert [<] _ = 0
  convert (left :< x) decimal = convert left (decimal * 10) + finToNat x * decimal

||| ASCII printable characters and newline
asciiTokenMap : TokenMap Char
asciiTokenMap = [(pred (== '\n'), const '\n')] ++ [(pred (== chr i), const (chr i)) | i <- [32..126]]

||| Run the parser on the string,
||| expecting full consumption of the input.
export
parseAll : s
        -> (act : Grammar s Char ty)
        -> (xs : String)
        -> Either (ParsingError Char s) (s, WithBounds ty)
parseAll st act xs =
  let (toks, (l, c, rest)) = lex asciiTokenMap xs in
  case rest of
    "" => Parser.parseAll st act toks
    _ => Left
          $ Error
              "Unrecognised character (only printable ASCII and newline symbols are supported)"
              st
              Nothing
              (MkBounds l c l c)


export
mbParseAll : s
          -> (act : Grammar s Char ty)
          -> (xs : String)
          -> Maybe (s, WithBounds ty)
mbParseAll st act xs = eitherToMaybe $ parseAll st act xs
