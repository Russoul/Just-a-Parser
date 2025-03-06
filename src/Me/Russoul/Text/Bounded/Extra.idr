module Me.Russoul.Text.Bounded.Extra

import Me.Russoul.Data.Location

import Text.Bounded

||| (s, e) ∪ (s', e') =
||| (min (s, s'), max (e, e'))
export
union : Bounds -> Bounds -> Bounds
union (MkBounds sl sc el ec) (MkBounds sl' sc' el' ec') =
  let (minl, minc) = min2 (sl, sc) (sl', sc') in
  let (maxl, maxc) = max2 (el, ec) (el', ec') in
  MkBounds minl minc maxl maxc

||| Construct @Bounds from start and end @Point
export
mkBounds : Point -> Point -> Bounds
mkBounds (startL, startC) (endL, endC) = MkBounds startL startC endL endC

export
degenerate : Point -> Bounds
degenerate x = mkBounds x x
