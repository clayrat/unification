module FO.Unification

import Data.Vect

%access public export
%default total

thin : Fin (S n) -> Fin n -> Fin (S n)
thin  FZ     y     = FS y
thin (FS x)  FZ    = FZ
thin (FS x) (FS y) = FS (thin x y)

thick : Fin (S n) -> Fin (S n) -> Maybe (Fin n)
thick          FZ     FZ    = Nothing
thick          FZ    (FS y) = Just y
thick {n=Z}   (FS x)  _     = absurd x
thick {n=S k} (FS x)  FZ    = Just FZ
thick {n=S k} (FS x) (FS y) = FS <$> (thick x y)

parameters (name : Nat -> Type, decEqName : (i : Nat) -> (x, y : name i) -> Dec (x = y))

  data Term : Nat -> Type where
    Var : Fin n -> Term n
    Con : name k -> Vect k (Term n) -> Term n

  -- replacement function
  mutual
    replace : (Fin n -> Term m) -> Term n -> Term m
    replace f (Var i)    = f i
    replace f (Con s ts) = Con s (replaceChildren f ts)

    replaceChildren : (Fin n -> Term m) -> Vect k (Term n) -> Vect k (Term m)
    replaceChildren f []        = []
    replaceChildren f (x :: xs) = replace f x :: (replaceChildren f xs)

 -- replacement composition

  rComp : (f : Fin m -> Term n) -> (g : Fin l -> Term m) -> Fin l -> Term n
  rComp f g = replace f . g

  -- occurs check
  mutual
    check : Fin (S n) -> Term (S n) -> Maybe (Term n)
    check x1 (Var x2)   = Var <$> thick x1 x2
    check x1 (Con s ts) = Con s <$> checkChildren x1 ts

    checkChildren : Fin (S n) -> Vect k (Term (S n)) -> Maybe (Vect k (Term n))
    checkChildren x1 []      = Just []
    checkChildren x1 (t::ts) = [| (check x1 t) :: (checkChildren x1 ts) |]

  -- substitutions (AList in McBride, 2003)
  data Subst : Nat -> Nat -> Type where
    Nul  : Subst n n
    Snoc : Subst m n -> Term m -> Fin (S m) -> Subst (S m) n

  -- compose two substitutions
  sComp : Subst m n -> Subst l m -> Subst l n
  sComp s1  Nul          = s1
  sComp s1 (Snoc s2 t x) = Snoc (sComp s1 s2) t x

  -- substitute t for x
  for : Term n -> Fin (S n) -> Fin (S n) -> Term n
  for t x y = case thick x y of
    Just y' => Var y'
    Nothing => t

  -- substitution application
  apply : Subst m n -> Fin m -> Term n
  apply  Nul         = Var
  apply (Snoc s t x) = rComp (apply s) (for t x)

  flexRigid : Fin n -> Term n -> Maybe (m ** Subst n m)
  flexRigid {n=Z}   x _ = absurd x
  flexRigid {n=S n} x t = (\t' => (n ** Snoc Nul t' x)) <$> check x t

  flexFlex : Fin n -> Fin n -> (m ** Subst n m)
  flexFlex {n = Z}   x _ = absurd x
  flexFlex {n = S n} x y = case thick x y of
    Nothing => (S n ** Nul)
    Just z => (n ** Snoc Nul (Var z) x)

  mutual
    unifyAcc : Term m -> Term m -> (n ** Subst m n) -> Maybe (n ** Subst m n)
    unifyAcc (Con {k=k1} s1 ts1) (Con {k=k2} s2 ts2) acc with (decEq k1 k2)
      unifyAcc (Con {k=k1} s1 ts1) (Con {k=k2} s2 ts2) acc | No neq = Nothing
      unifyAcc (Con {k=k1} s1 ts1) (Con {k=k1} s2 ts2) acc | Yes Refl with (decEqName k1 s1 s2)
        unifyAcc (Con {k=k1} s1 ts1) (Con {k=k1} s2 ts2) acc | Yes Refl | No neq = Nothing
        unifyAcc (Con {k=k1} s1 ts1) (Con {k=k1} s1 ts2) acc | Yes Refl | Yes Refl = unifyAccChildren ts1 ts2 acc
    unifyAcc (Var x1) (Var x2) (m ** Nul) = Just (flexFlex x1 x2)
    unifyAcc (Var x1)  t2      (m ** Nul) = flexRigid x1 t2
    unifyAcc  t1      (Var x2) (m ** Nul) = flexRigid x2 t1
    unifyAcc  t1       t2      (m ** Snoc s t' x) =
      (\(l ** sub) => (l ** Snoc sub t' x))
        <$> unifyAcc (replace (for t' x) t1) (replace (for t' x) t2) (m ** s)

    unifyAccChildren : Vect k (Term n) -> Vect k (Term n) -> (m ** Subst n m) -> Maybe (m ** Subst n m)
    unifyAccChildren []         []       acc = Just acc
    unifyAccChildren (t1::ts1) (t2::ts2) acc = unifyAcc t1 t2 acc >>= unifyAccChildren ts1 ts2

  unify : Term m -> Term m -> Maybe (n ** Subst m n)
  unify {m} t1 t2 = unifyAcc t1 t2 (m ** Nul)