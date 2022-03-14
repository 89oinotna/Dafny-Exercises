/*

Binary Search Trees (BST)
Copyright: Specified and verified by Ricardo Peña, February 2019

*/

// BSTs are binary trees having unique keys and sorted inorder traversal
datatype BST = Empty  |  Node (left: BST, key: int, right: BST)

// This is the BST invariant
predicate isBST (t: BST)
{
   match t
      case Empty       => true
      case Node(l,x,r) => promising(l,x,r) && isBST(l) && isBST(r)
}				

// This is the BST property at the root level
predicate promising(l:BST, x:int, r:BST) 
{
   (forall z :: z in tset(l) ==> z < x) && 
   (forall z :: z in tset(r) ==> x < z)
}	

function tset(t:BST): set<int>
{
   match t
      case Empty       => {}		
      case Node(l,x,r) => tset(l)+{x}+tset(r)	
}				

function inorder(t: BST): seq<int>
{
   match t
      case Empty       => []
      case Node(l,x,r) => inorder(l) + [x] + inorder(r)
}			

// It searchs whether an element is present in a BST
function method search(x:int, t:BST): (res:bool)
requires isBST(t)
ensures res == (x in tset(t))
{
   match t 
      case Empty => false
      case Node(l, xx, r) => if x==xx then true
                              else if x < xx then search(x, l)
                              else search(x, r)
}

// It inserts an element in a BST 
function method insert(x:int, t:BST): (res:BST)
requires isBST(t)
ensures  isBST(res)
ensures  tset(res) == tset(t) + {x}
{
   match t 
      case Empty => Node(Empty, x, Empty)
      case Node(l,xx,r) => if x == xx then t 
                           else if x < xx then Node(insert(x, l), xx, r)
                           else Node(l, xx, insert(x,r))
}

// It deletes an element from a BST 
function method delete(x:int, t:BST): (res:BST)
requires isBST(t)
ensures  isBST(res)
ensures  tset(res) == tset(t) - {x}
{
   match t 
      case Empty => t
      case Node(l, y, r) => if  x < y then Node(delete(x,l), y,r)
                              else if x > y then Node(l,y,delete(x,r))
                              else match r
                                    case Empty => l
                                    case Node(_,_,_) => var (m,t') := deleteMin(r);
                                                         Node(l, m, t')

}

// It deletes the minimum element of a non empty BST
function method deleteMin (t: BST): (res: (int, BST))
requires isBST(t) && t != Empty
ensures res.0 in tset(t) 
ensures forall x | x in tset(t)-{res.0} :: res.0 < x
ensures isBST(res.1) 
ensures tset(res.1) == tset(t) - {res.0}
{
   match t 
      case Node(Empty,y,r) => (y, r)
      case Node(l,y,r) => var (m,l') := deleteMin(l);
                           //assert y>m;
                           //assert forall x | x in tset(r) :: m < x;
                           //assert forall x | x in tset(l') :: m < x;
                           assert tset(Node(l',y,r)) == tset(t) - {m};
                           (m, Node(l',y,r))
}


predicate sorted(s: seq<int>)
{
    forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}

lemma sortedInorder(t: BST)
requires isBST(t)
ensures  sorted(inorder(t))
{
   match t 
      case Empty       =>
      case Node(l,x,r) => 
            assert promising(l,x,r);
            inorderPreserveSet(l);
            //assert forall z | z in inorder(l) :: z in tset(l);
            assert forall z | z in inorder(l) :: z < x;
            inorderPreserveSet(r);
            assert forall z | z in inorder(r) :: z > x;
            //assert inorder(t)[|inorder(l)|]==x;
            assert forall j | 0<= j < |inorder(l)| :: inorder(t)[j] in tset(l);
            assert forall j | |inorder(l)| < j < |inorder(t)| :: inorder(t)[j] in tset(r);
}

lemma inorderPreserveSet (t:BST)
ensures forall z | z in inorder(t) :: z in tset(t)
{}
/*
     Exercises
*/


// 1. Program a function mirror which gets the symmetric image of a tree along
//    a vertical axis passing through the root and prove the postcondition shown

function mirror(t:BST):(res:BST)
ensures tset(res)==tset(t)
{
   match t
      case Empty => Empty
      case Node(l, x, r) => Node(mirror(r),x, mirror(l))
}

// 2. We give you this function returning the reverse of a sequence

function rev <T> (s:seq<T>): (res:seq<T>)
{
   if s==[] then []
            else rev(s[1..]) + [s[0]]
}

lemma revList<T>(s1:T,s2:seq<T>)
ensures [s1] + rev(s2) == rev(s2 + [s1])
ensures rev(s2) + [s1] == rev([s1] + s2)
{
   if(|s2| == 0){
      assert [s1] == rev([s1]);
   }
   else{
      calc ==  {
         [s1] + rev(s2);
         [s1] + rev(s2[1..]) + [s2[0]];
         {
            revList(s1, s2[1..]);  
         }
         rev(s2[1..] + [s1]) + [s2[0]];
         rev([s2[0]] + (s2[1..] + [s1]));
         {
            assert [s2[0]] + (s2[1..] + [s1]) == s2 + [s1];
         }
         rev(s2 + [s1]);
      }
   }
}

lemma revSum <T>(s1:seq<T>,s2:seq<T>)
ensures rev(s1) + rev(s2) == rev(s2 + s1)
{
   if (|s1| == 0){
      assert rev(s1) + rev(s2) == rev(s2);
      assert s2 + s1 == s2;
   }
   else{
      calc == {
         rev(s1[1..]) + [s1[0]] + rev(s2);
         {
            revList(s1[0], s2);
         }
         rev(s1[1..]) + rev(s2+[s1[0]]);
         {revSum(s1[1..], rev(s2+[s1[0]]));}
         rev(s2+[s1[0]] + s1[1..]);
         {
            assert s2+[s1[0]] + s1[1..] == s2 + s1;
         }
         rev(s2+s1);
      }
   }
}


// then, prove the following lemma by using the 'calc' facility

lemma reverseInorder (t:BST)
ensures inorder(mirror(t)) == rev(inorder(t))
{
   match t 
      case Empty =>
      case Node(l,x,r) =>
         calc == {
            inorder(mirror(t));
            inorder(Node(mirror(r), x, mirror(l)));
            inorder(mirror(r)) + [x] + inorder(mirror(l));
            rev(inorder(r)) + [x] + rev(inorder(l));
            {
               revSum(inorder(r),[x]);
               revSum([x]+inorder(r), inorder(l));
            }
            rev(inorder(l) + ([x] + inorder(r)));
            {
               assert inorder(l) + ([x] + inorder(r)) ==inorder(l) + [x] + inorder(r);
            }
            rev(inorder(t));
         }
}

