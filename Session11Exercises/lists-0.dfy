datatype List<T> = Nil | Cons(head:T, tail:List<T>)

function method length<T> (l:List<T>) : nat
{
    match l
       case Nil         => 0
       case Cons(_, xs) => 1 + length(xs)
}

predicate sorted(l:List<int>)
{
    match l 
       case Nil         => true
       case Cons(x, xs) => 
            match xs 
               case Nil         => true
               case Cons(y, ys) => x <= y && sorted(xs)
}

function elems<T> (l:List<T>) : multiset<T>
{
    match l
       case Nil         => multiset{}
       case Cons(x, xs) => multiset{x} + elems(xs)
}

function sum(l:List<int>): (res:int)
{
    match l 
        case Nil         => 0
        case Cons(y, ys) => y + sum(ys)
}

function insert(x: int, l:List<int>): (res:List<int>)
requires sorted(l)
ensures sorted(res)
ensures elems(res) == elems(l) + multiset{x}
{
    match l
        case Nil => Cons(x,Nil)
        case Cons(y, ys) => if x <= y then Cons(x, l)
                            else Cons(y,insert(x, ys))
}

function delete<T> (x: T, l:List<T>): (res:List<T>)
ensures elems(res) == elems(l) - multiset{x}
{
    match l
        case Nil => Nil
        case Cons(y, ys) => if x == y then ys
                            else Cons(y, delete(x, ys))
}

function search<T> (x: T, l:List<T>): (res:bool)
ensures res == (x in elems(l))
{
    match l
        case Nil => false
        case Cons(y, ys) => if x == y then true
                            else search(x,ys)
}

function min(x:nat, y:nat): (res:nat)
{
    if x <=y then x else y
}

function take<T> (n: nat, l:List<T>): (res:List<T>)
ensures length(res) == min (n, length(l))
{
    match l
        case Nil => Nil
        case Cons(x,xs) => if n <= 0 then Nil
                            else Cons(x, take(n-1, xs))
}

function drop<T> (n: nat, l:List<T>): (res:List<T>)
ensures length(res) == if length(l) < n then 0 else length(l) - n
{
    match l
        case Nil => Nil
        case Cons(x,xs) => if n <= 0 then l
                            else drop(n-1, xs)
}

function method splitWhileNE <T(==)> (x: T, l:List<T>): (res:(List<T>, List<T>))
ensures elems(l) == elems(res.0) + elems(res.1)
{
    match l
      case Nil        => (Nil,Nil)
      case Cons(y,ys) => if x == y then (Nil, l)
                         else var (l1,l2) := splitWhileNE (x, ys);
                              (Cons(y,l1), l2)
}

/*
   Exercises
*/

// 1. write the code of this function and verify it (but do not use take and drop)

function method split<T> (n: nat, l:List<T>): (res:(List<T>, List<T>))
ensures length(res.0) == min (n, length(l))
ensures length(res.1) == if length(l) < n then 0 else length(l) - n
ensures elems(l) == elems(res.0) + elems(res.1)
{
    match l
        case Nil => (Nil, Nil)
        case Cons(x, xs) => if length(l) > n then 
                                var (l1,l2):= split(n, xs);
                                (l1, Cons(x, l2)) 
                            else (Cons(x,xs), Nil)
}

// 2. specify, write the code of this function, and verify it

function method reverse(l:List<int>): (res:List<int>)
ensures elems(l) == elems(res)
{
    match l
        case Nil => Nil
        case Cons(x,xs) =>concat(reverse(xs), Cons(x, Nil)) 
        /*
            match reverse(xs)
            case Nil => Cons(x,Nil)
            case Cons(y,xs) => Cons(y, concat(xs, Cons(x, Nil)))*/
}

// 3. specify, write the code of this function, and verify it

function method concat(l1:List<int>,l2:List<int>): (res:List<int>)
ensures elems(res)==elems(l1) + elems(l2)
{
    match l1
        case Nil => l2
        case Cons(x, xs) =>
            Cons(x,concat(xs, l2))
}

// 4. prove it

lemma concatAssoc(l1:List<int>,l2:List<int>,l3:List<int>)
ensures concat(l1,concat(l2,l3))==concat(concat(l1,l2),l3)
{
    
}

// 5. prove it

lemma Lemma_ConcatNil(xs : List<int>)
  ensures concat(xs, Nil) == xs
  ensures concat(Nil, xs) ==xs
{
}

lemma Lemma_RevConcat(xs: List<int>, ys: List<int>)
  ensures reverse(concat(xs, ys)) == concat(reverse(ys), reverse(xs));
{
  match (xs) {
    case Nil => calc == {
         reverse(concat(Nil, ys));
         {Lemma_ConcatNil(ys);}
         reverse(ys);
         {Lemma_ConcatNil(reverse(ys));}
         concat(reverse(ys), Nil);
         concat(reverse(ys), reverse(Nil));
    }
    case Cons(k, ks) => calc =={
        reverse(concat(xs, ys));
        reverse(concat(concat(Cons(k,Nil), ks),ys));
        {concatAssoc(Cons(k,Nil), ks,ys);}
        reverse(concat(Cons(k,Nil), concat(ks,ys)));
        concat(reverse(concat(ks,ys)), Cons(k,Nil));
        concat(concat(reverse(ys), reverse(ks)), Cons(k,Nil));
        {concatAssoc(reverse(ys), reverse(ks),Cons(k,Nil));}
        concat(reverse(ys), concat(reverse(ks), Cons(k, Nil)));
        concat(reverse(ys), reverse(xs));
    }
  }
}


lemma reverseIdemp(l:List<int>)
ensures reverse(reverse(l))==l
{
    match (l) {
    case Nil =>
    case Cons(x, xs) => calc =={
        reverse(reverse(l));
        reverse(concat(reverse(xs), Cons(x, Nil)));
        {Lemma_RevConcat(reverse(xs), Cons(x,Nil));}
        concat(reverse(Cons(x,Nil)), reverse(reverse(xs)));
        {
            reverseIdemp(xs);
            assert reverse(Cons(x, Nil)) == Cons(x,Nil);
        }
        concat(Cons(x,Nil), xs);
        l;
    }
  }
}
