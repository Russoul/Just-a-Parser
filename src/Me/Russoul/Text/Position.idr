module Me.Russoul.Text.Position

||| Position in a text file (think of a blinking cursor)
||| Assume: line ≥ 0
||| Assume: column ≥ 0
public export
record Position where
  constructor MkPosition
  line : Int
  column : Int

public export
Eq Position where
  MkPosition x y == MkPosition x' y' = x == x' && y == y'

public export
Ord Position where
  compare (MkPosition l c) (MkPosition l' c') =
    case compare l l' of
      EQ => compare c c'
      r  => r

public export
Show Position where
  show (MkPosition line column) = "MkPosition {line = \{show line}, column = \{show column}}"

export
min : Position -> Position -> Position
min a b =
  if a < b then a else b

export
max : Position -> Position -> Position
max a b =
  if a > b then a else b

export
Cast (Int, Int) Position where
  cast (x, y) = MkPosition x y

export
Cast Position (Int, Int) where
  cast (MkPosition x y) = (x, y)
