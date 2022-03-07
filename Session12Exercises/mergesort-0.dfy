datatype List<T> = Nil | Cons(head:T, tail:List<T>)

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

method mergesort(l:List<int>) returns (res:List<int>)
ensures sorted(res) 
ensures elems(l) == elems(res)
decreases length(l)
{
  if length(l) < 2 
       { 
         //assert sorted(l);
         sortedSmallList(l);
         res := l;}
  else {
         //splitLengths(l);
         var (left, right) := split(l);
         var resl := mergesort(left);
         var resr := mergesort(right);
         res := merge(resl,resr);
    }
}

function method length<T> (l:List<T>) : nat
{
    match l
       case Nil         => 0
       case Cons(_, xs) => 1 + length(xs)
}

function method split<T> (l:List<T>): (res: (List<T>, List<T>))
ensures elems(l) == elems(res.0) + elems(res.1)
ensures length(l) >= 2 ==>
        (length(split(l).0) < length(l) && length(split(l).1) < length(l))
{
   match l
      case Nil => (Nil, Nil)
      /*case Cons(x, xs) => var (l1,r1):=split(xs);
                           if length(l)-1 % 2 !=0 then
                              (l1, Cons(x,r1))
                           else
                              (Cons(x,l1),r1)*/
      case Cons(x,Nil) => (Cons(x,Nil), Nil)
      case Cons(x,Cons(y,ys)) => assert length(ys)+2 ==length(l);
                                 var (l1,l2):=split(ys);
                                 (Cons(x,l1),Cons(y,l2))
}

function method merge(l1:List<int>, l2:List<int>) : (res:List<int>)
requires sorted(l1) && sorted(l2)
ensures sorted (res)
ensures elems(res) == elems(l1) + elems(l2)
{
   match l1
      case Nil => l2
      case Cons(x,xs) => 
         match l2
            case Nil => l1
            case Cons(y,ys) => if x > y then 
                                 Cons(y, merge(l1,ys))
                              else
                                 Cons(x,merge(xs,l2))
}



lemma splitLengths(l:List<int>)
requires length(l) >= 2 
ensures length(split(l).0) < length(l) && 
        length(split(l).1) < length(l)
{}


lemma sortedSmallList (l:List<int>)
requires length(l) < 2
ensures  sorted(l)
{}


function partition (l:List<int>, x:int)  : (res: (List<int>,List<int>))
ensures forall z | z in elems(res.0) :: z <= x
ensures forall z | z in elems(res.1) :: z > x
ensures elems(l) == elems(res.0) + elems(res.1)
ensures length(res.0) <= length(l)
ensures length(res.1) <= length(l)


function quicksort (l:List<int>): (res:List<int>)
ensures sorted(res) 
ensures elems(l) == elems(res)
decreases length(l)
{
   match l
      case Nil        => Nil
      case Cons(x,xs) => var (l1,l2) := partition(xs,x);
                         var left    := quicksort(l1);
                         var right   := quicksort(l2);
                         concatPreserveSorted(Cons(x,Nil), right);
                         assert sorted(Cons(x,right));
                         concatPreserveSorted(left,Cons(x,right));
                         concat(left,Cons(x,right))                         

}


function method concat(l1:List<int>,l2:List<int>): (res:List<int>)
ensures elems(res) == elems(l1) + elems(l2)
{
      match l1
        case Nil => l2
        case Cons(x, xs) =>
            Cons(x,concat(xs, l2))
}

lemma sortedIsSorted(l:List<int>)
requires sorted(l);
ensures l.Cons? ==> forall x | x in elems(l.tail) :: x >= l.head
{
   match l
      case Nil => assert sorted(Nil);
      case Cons(x,xs) => 
         
         assert forall xx | xx in elems(xs) :: xx>= x; 

         assert sorted(xs);
}

lemma concatPreserveSorted(l1:List<int>,l2:List<int>)
requires sorted(l1) && sorted(l2)
requires forall x,y | x in elems(l1) && y in elems(l2) :: x <= y
ensures sorted(concat(l1,l2))
{
   match l1
      case Nil => assert sorted(Nil);
      case Cons(x,Nil) =>  assert x in elems(l1);
                           assert forall k | k in elems(l2) :: x <= k;
                           concatPreserveSorted(Nil,l2);
                           assert sorted(concat(Cons(x,Nil),l2));
      case Cons(x,xs) => 
            assert sorted(xs);
            assert concat(Cons(x,Nil), xs)==l1;
            assert sorted(concat(Cons(x,Nil), xs));
            assert forall k | k in elems(xs) :: k in elems(l1);
            concatPreserveSorted(xs, l2);
            assert x in elems(l1);
            assert Cons(x,xs)==l1;
            sortedIsSorted(l1);
            assert forall k | k in elems(xs) :: x <= k;
            assert sorted(concat(Cons(x,Nil), concat(xs,l2))) ;
            assert concat(Cons(x,Nil), concat(xs,l2)) == concat(l1,l2);
}


/*
   Exercises
*/

// 1. Modify and verify mergesort using function splitAt n/2 instead of split

// 2. Complete the verification of quicksort

// 3. Prove the following Lemma

lemma firstEqual(l1:List<int>,l2:List<int>)
requires sorted(l1) && sorted(l2) && elems(l1)==elems(l2)
ensures l1.Cons? ==> l1.head == l2.head
{
   match l1
      case Nil => assert l2==Nil;
      case Cons(x,xs) =>
                  sortedIsSorted(l1);
                  sortedIsSorted(l2);
                  assert forall k | k in elems(l1) :: x<=k;
                  assert forall k | k in elems(l2) :: x<=k;
                  assert x in elems(l2);
                  assert l2.head in elems(l1);
                  assert forall k | k in elems(l2) ::l2.head<=k;
                  assert forall k | k in elems(l1) :: l2.head<=k;
                  assert elems(xs) + multiset{x} == elems(l2); 
                  assert l2.head == x;
}

lemma uniqueSortedList(l1:List<int>,l2:List<int>)
requires sorted(l1) && sorted(l2) && elems(l1)==elems(l2)
ensures l1 == l2
{
   match l1
      case Nil =>
      case Cons(x,xs) =>
            match l2 
               case Nil => assert false;
               case Cons(y,ys) => 
                  assert sorted(xs);
                  assert sorted(ys);
                  sortedIsSorted(l1);
                  sortedIsSorted(l2);
                  firstEqual(l1,l2);
                  assert y==x;
                  assert elems(xs) == elems(l2) - multiset{y};
                  assert elems(xs) == elems(ys);
                  uniqueSortedList(xs, ys);
}
