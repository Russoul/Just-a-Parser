module Me.Russoul.Text.Range

import Me.Russoul.Text.Position
import Text.Bounded

||| Range of symbols in a text file (think of a visual selection that can span multiple lines but also be degenerate in length)
||| Assume: start < end
public export
record Range where
  constructor MkRange
  start : Position
  end : Position

export
union : Range -> Range -> Range
union (MkRange s e) (MkRange s' e') =
  let s'' = min s s' in
  let e'' = max e e' in
  MkRange s'' e''

(+) = union

public export
Show Range where
  show (MkRange s e) = "MkRange {start = \{show s}, end = \{show e}}"

public export
Eq Range where
  MkRange a b == MkRange a' b' = a == a' && b == b'

public export
Ord Range where
  compare (MkRange l c) (MkRange l' c') =
    case compare l l' of
      EQ => compare c c'
      r  => r

public export
Cast Bounds Range where
  cast (MkBounds l c l' c') = MkRange (MkPosition l c) (MkPosition l' c')

public export
Cast Range Bounds where
  cast (MkRange (MkPosition l c) (MkPosition l' c')) = MkBounds l c l' c'
