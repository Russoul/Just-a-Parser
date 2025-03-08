module Me.Russoul.Text.Bounded.Extra

import Me.Russoul.Text.Range

import Text.Bounded

public export
Int2 : Type
Int2 = (Int, Int)

export
union : Bounds -> Bounds -> Bounds
union (MkBounds sl sc el ec) (MkBounds sl' sc' el' ec') =
  let (minl, minc) = min (sl, sc) (sl', sc') in
  let (maxl, maxc) = max (el, ec) (el', ec') in
  MkBounds minl minc maxl maxc

||| Construct @Bounds from start and end @Point
export
mkBounds : Int2 -> Int2 -> Bounds
mkBounds (startL, startC) (endL, endC) = MkBounds startL startC endL endC

export
degenerate : Int2 -> Bounds
degenerate x = mkBounds x x
