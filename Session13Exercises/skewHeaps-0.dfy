/*

Skew Heaps
Copyright: Specified and verified by Ricardo Peña, February 2019

*/

// Skew Heaps are just binary trees holding the so-called heap property 
datatype Skew = Empty  |  Node (left: Skew, key: int, right: Skew)

// This is the Skew Heap invariant
predicate isSkew (t: Skew)
{
   match t
      case Empty       => true
      case Node(l,x,r) => isSkew(l) && isSkew(r) &&  heap(l, x, r) 
}				

// This is the heap property at the root level
predicate heap(l:Skew, x:int, r:Skew) 
{
   forall z | z in mset(l) + mset(r) :: x <= z
}		
			
// this is the mathematical model implemented by a Skew Heap
function mset(t:Skew): multiset<int>
{
   match t
      case Empty       => multiset{}		
      case Node(l,x,r) => mset(l) + multiset{x} + mset(r)	
}				

// This funtion joins two Skew heaps in amortized logarithmic time
function method join(t1:Skew, t2:Skew): (res:Skew)
requires isSkew(t1) && isSkew(t2)
ensures isSkew(res)
ensures mset(res) == mset(t1) + mset(t2)
{
    match t1
      case Empty          => t2
      case Node(l1,x1,r1) => 
         match t2
            case Empty          => t1
            case Node(l2,x2,r2) => 
               assert mset(l2) + mset(r2) + multiset{x2} == mset(t2);
               assert mset(l1) + mset(r1) + multiset{x1} == mset(t1);
               assert mset(r1) == mset(t1) - mset(l1) - multiset{x1};
               assert mset(r2) == mset(t2) - mset(l2) - multiset{x2};
               if x1 <= x2 then 
                  //assert mset(join(r1, t2)) + mset(l1) + multiset{x1} == mset(t1) + mset(t2);
                  assert forall z | z in mset(r1) :: x1 <= z;
                  //assert mset(join(r1,t2)) == mset(r1) + mset(t2);
                  //assert forall k | k in mset(join(r1,t2)) :: k>=x1; 
                  assert isSkew(Node(join(r1,t2),x1,l1));
                  Node(join(r1,t2),x1,l1)

               else 
                  //assert mset(join(t1, r2)) + mset(l2) + multiset{x2} == mset(t1) + mset(t2);
                  assert forall z | z in mset(r2) :: x2 <= z;
                  //assert mset(join(t1,r2)) == mset(t1) + mset(r2);
                  //assert forall k | k in mset(join(t1,r2)) :: k>=x2; 
                  assert isSkew(Node(join(t1,r2),x2,l2));
                  Node(join(t1,r2),x2,l2)
}
/*
   Exercises
*/
// 1. Provide the specification and verification of the above function method join

// 2. Provide the specification, code and verification of the following function method
//    It inserts an element in a Skew Heap in amortized logarithmic time
//    Hint: use join
function method insert(x:int, t:Skew): (res:Skew)
requires isSkew(t)
ensures isSkew(res)
ensures mset(t) + multiset{x} == mset(res)
{
   match t 
      case Empty => Node(Empty, x, Empty)
      case Node(l, y, r) => 
         assert mset(Node(Empty, x,Empty)) == multiset{x};
         join(t, Node(Empty, x,Empty)) 
}

//use join

// 3. Provide the specification, code and verification of the following function method
//    It gets the minimum of a Skew Heap in constant time
function method min(t:Skew): int
requires isSkew(t)
requires t != Empty
ensures forall k | k in mset(t) :: k>=min(t)
{
   match t 
      case Node(l,x,r) => 
         assert mset(t)==mset(l) + mset(r) + multiset{x};
         assert  forall k | k in mset(t) :: k>=x;
         x
}

// 4. Provide the specification, code and verification of the following function method
//    It deletes the minimum of a Skew Heap in amortized logarithmic time
//    Hint: use join
function method deleteMin(t:Skew): (res:Skew)
requires isSkew(t) && t != Empty
ensures mset(res) == mset(t) - multiset{min(t)}
ensures isSkew(res)
{
   match t 
      case Node(l,x,r) => join(l,r)
}
