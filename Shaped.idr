module Shaped

import Data.Vect
import Data.So

%default total

mkRank : (len: Nat) -> (stride: Nat) -> Fin 3
mkRank len s = case len > s of
  True => the (Fin 3) 2
  False => if (len > 1) then the (Fin 3) 1 else the (Fin 3) 0

data Dim: (rows, stride, len: Nat) -> Type where
  MkDim: (rows, stride: Nat)
    -> {auto NZs : So (stride > 0)}
    -> {auto NZs : So (rows > 0)}
    -> Dim rows stride (rows * stride)

data Shape: (rank: Fin 3) -> Dim rows stride len -> Type where
  SomeScalar:
    Shape
      (mkRank 1 1)
      (MkDim 1 1)
  SomeVect:
    (stride: Nat)
    -> {auto NZs : So (stride > 0)}
    -> Shape
        (mkRank stride stride)
        (MkDim 1 stride)
  SomeMat:
    (rows, stride: Nat)
    -> {auto NZs : So (stride > 0)}
    -> {auto NZs : So (rows > 0)}
    -> Shape
        (mkRank (rows * stride) stride)
        (MkDim rows stride)

data Operation =
  Plus | Minus
  | Slash | Backslash
  | Equal

data Parallelism: Nat -> Nat -> Type where
  mkPar: (x: Nat) -> (y: Nat) -> Parallelism x y

record Phase where
  constructor MkPhase
  operation : Operation
  shape : Shape rank (MkDim (S rows) (S stride))
  par : Parallelism x y

-- shape (Reduce (SomeVect 4))
-- shape (Reduce (SomeMat 3 3))
-- shape (Sum (SomeVect 4) (shape (Reduce (SomeMat 3 3))))
-- shape (Sum SomeScalar (shape (Reduce (SomeVect 4))))
Reduce : Shape q (MkDim (S r) (S n)) -> Phase
Reduce {q=FZ} o = MkPhase Slash o (mkPar 0 0)
Reduce {q=FS(FZ)} {n} o = MkPhase Slash SomeScalar (mkPar (S n) 0)
Reduce {q=FS(FS(FZ))} {r} {n} o = MkPhase Slash (SomeVect (S n)) (mkPar ((S n)*(S r)) 0)

Scan : Shape p (MkDim (S r) (S n)) -> Phase
Scan {r} {n} o = MkPhase Backslash o (mkPar ((S n)*(S r)) 0)

-- scalarToVect (MkScalar 1) (MkVect [1,2,3,4])
-- [Plus, Minus, Slash]
-- shape (Sum SomeScalar SomeScalar)
-- shape (Sum (SomeVect 4) (SomeVect 4))
-- shape (Sum (SomeMat 3 3) (SomeMat 3 3))
Sum : Shape p (MkDim (S r) (S n)) -> Shape p (MkDim (S r) (S n)) -> Phase
Sum {r} {n} a o = MkPhase Plus o (mkPar 0 ((S n)*(S r)))

-- shape (NSum SomeScalar (SomeVect 4))
-- shape (NSum SomeScalar (SomeMat 3 3))
NSum : Shape 0 (MkDim (S r) (S n)) -> Shape p (MkDim (S j) (S m)) -> Phase
NSum {j} {m} a o = MkPhase Plus (SomeMat (S j) (S m)) (mkPar 0 ((S j)*(S m)))
