/*

AVL trees
specified and verified by Ricardo Peña, November 2017

*/

/* AVLs are just binary trees having an additional height field in the nodes */
datatype AVL = Empty  |  Node (left: AVL, height: nat, key: int, right: AVL)

/* This is the AVL invariant */
predicate isAVL (t: AVL)
{
   match t
      case Empty         => true
      case Node(l,h,k,r) => h == height(t)  && isAVL(l) && isAVL(r) && 
                            promising(l, k, r) && -1 <= height(l) - height(r) <= 1
}				

/* This is the binary search tree property at the root level */
predicate promising(l:AVL, x:int, r:AVL) 
{
   (forall z :: z in tset(l) ==> z < x) && 
   (forall z :: z in tset(r) ==> x < z)
}		

function inorder(t: AVL): seq<int>
{
   match t
      case Empty         => []
      case Node(l,_,x,r) => inorder(l)+[x]+inorder(r)
}				

/* this is the mathematical model implemented by an AVL */
function tset(t:AVL): set<int>
{
   match t
      case Empty          => {}		
      case Node(l,_,x,r) => tset(l)+{x}+tset(r)	
}				

/* these are both specification and implementation methods */
function method max (x:int, y:int): int
{
  if x >= y then x else y
}				

function method abs (x: int): nat
{
  if x >= 0 then x else -x
}				

/* these are specification-oriented ghost functions */
function height(t: AVL) : nat
{
  match t 
     case Empty         => 0 
     case Node(l,_,_,r) => 1 + max (height(l), height(r)) 
}				

/* This is used in the implementation with a cost in O(1) */
function method myHeight(t: AVL): nat
{
  match t 
     case Empty         => 0 
     case Node(_,h,_,_) => h
}				

// It is automatically proven by structural induction
lemma heights (t: AVL)
requires isAVL(t)				
ensures height(t) == myHeight(t)
{
}				

/* These are the smart constructors, the first one visible from outside */
function method empty (): (res:AVL) // cost in O(1)
ensures isAVL(res)
ensures tset(res) == {}
{ 
  Empty
}

function method node(l: AVL, x: int, r: AVL): (res:AVL) // cost in O(1)
requires promising(l, x, r) && -1 <= height(l) - height(r) <= 1
requires isAVL(l) && isAVL(r)
ensures isAVL(res)
ensures tset(res) == tset(l) + {x} + tset(r)
{
    Node(l, 1 + max (myHeight(l), myHeight(r)), x, r)
}			

/* Visible look up function */
function method search(x:int, t: AVL): (res:bool)
requires isAVL(t)
ensures res == (x in tset(t))
{
   match t
      case Empty          =>  false
      case Node (l,_,y,r) =>  if x < y then  search (x, l)
                              else if x > y  then search (x, r)
                                             else /* x == y*/ true
}

/* Visible insertion function */
function method insert(x: int, t: AVL): (res:AVL)
requires isAVL(t)
ensures isAVL(res)
ensures 0 <=  height(res) - height(t) <= 1     // and some internal properties                  
ensures tset (res) == tset(t) + {x}
{
   match t 
      case Empty             =>  // assert(isAVL(node(Empty, x, Empty)));
                                 // assert(tset(node(Empty, x, Empty))=={x});
                                 node(Empty, x, Empty)
      case Node (l, _, y, r) =>     
              if x < y  then  equil(insert(x, l), y, r)
                        else  if x > y then equil(l, y, insert(x, r))
                                       else  t
}															 				
/* Visible delete function */
function method delete(x: int, t: AVL): AVL
requires isAVL(t)                                     // it assumes the datatype invariant
ensures isAVL(delete(x, t))                           // it ensures the datatype invariant
ensures 0 <= height(t) - height(delete(x,t)) <= 1     // and some internal properties                  
ensures tset(delete(x,t)) == tset(t) - {x}		      // this is the model-based postcondition					 
{
   match t
      case Empty            => t
      case Node (l, _,y, r) =>
            if x < y then equil(delete(x,l), y, r)
                     else if x > y then equil(l, y, delete(x, r))
                          else match r
                                 case Empty         => l 
                                 case Node(_,_,_,_) =>
                                      var (m,r') := deleteMin(r);
                                      equil(l, m, r')
}

/* Auxiliary internal methods */
function method deleteMin (t: AVL): (res: (int, AVL))
requires isAVL(t) && t != Empty
ensures res.0 in tset(t)
ensures forall x | x in tset(t) :: res.0 <= x
ensures isAVL(res.1) 
ensures tset(res.1) == tset(t) - {res.0}
ensures 0 <= height(t) - height(res.1) <= 1           
{
   match t
      case Node(l, _,x, r) =>
         match l 
            case Empty => (x, r)
            case Node(_,_,_,_) => 
               var (m,l') := deleteMin(l);
               (m, equil(l', x, r))
}

/* O(1) method that balances the tree, if needed */
function method equil(l: AVL, x: int, r: AVL): AVL // cost in O(1)
requires promising(l, x, r)
requires isAVL(l) && isAVL(r)
requires abs(height(l)-height(r)) <= 2
ensures  isAVL(equil(l,x,r))
ensures  tset(equil(l, x, r)) == tset(l) + {x} + tset (r)
ensures  max(height(l), height(r)) <= height(equil(l, x, r)) <= max(height(l), height(r))+1		
{    
   if abs(myHeight(l)-myHeight(r)) <= 1 
      then node(l, x, r)
      else  if myHeight(l) == myHeight(r) + 2 
              then leftUnbalance(l, x, r)
              else rightUnbalance(l, x, r)
}				

// it implements the LL and LR rotations
function method leftUnbalance(l: AVL, x: int, r: AVL): (res: AVL) // cost in O(1)
requires height(l) == height(r) + 2
requires promising(l, x, r)
requires isAVL(l) && isAVL(r)
ensures isAVL(res)
ensures tset(res) == tset(l) + {x} + tset (r)
ensures max(height(l), height(r)) <= height(res) <= max(height(l), height(r)) + 1		
{
  if myHeight(l.left)  >= myHeight(l.right) 
     then // this is the LL rotation
          //assert l.Node? && promising(l.left, l.key, l.right) && -1 <= height(l.left)-height(l.right) <= 1;
          assert isAVL(l.left) && isAVL(l.right);
          assert forall z :: z in tset(l) ==> z < x;
          assert forall z :: z in tset(node (l.right, x, r)) ==> l.key < z; 
          node(l.left, l.key, node (l.right, x, r))
     else // this the LR rotation
          //assert l.Node? && promising(l.left, l.key, l.right);  
          //assert l.right.Node? ;
          assert isAVL(l.right);
          assert isAVL(l.left);  
          //assert tset(l.right.left) < tset(l.right);
          //assert promising(l.left, l.key, l.right.left);
          assert forall z :: z in tset(l) ==> z < x;
          assert forall z :: z in tset(l.right) ==> z < x;
          node(node(l.left, l.key, l.right.left), l.right.key, node(l.right.right, x, r))
}				

/*
    Exercises
*/

// 1. Specify and verify the following function method

// it implements the RR and RL rotations
function method rightUnbalance(l: AVL, x: int, r: AVL): (res: AVL)
requires height(l)+2 == height(r)
requires promising(l, x, r)
requires isAVL(l) && isAVL(r)
ensures isAVL(res)
ensures tset(res) == tset(l) + {x} + tset (r)
ensures max(height(l), height(r)) <= height(res) <= max(height(l), height(r)) + 1
{
  if myHeight(r.right)  >= myHeight(r.left)    
     then // this is the RR rotation
         assert isAVL(r.left) && isAVL(r.right);
         assert forall z :: z in tset(r) ==> z > x;
         assert forall z :: z in tset(node (l, x, r.left)) ==> r.key > z; 
         node(node(l, x, r.left), r.key, r.right)
     else // this the RL rotation
         assert isAVL(r.right);
         assert isAVL(r.left);  
         assert forall z :: z in tset(r) ==> z > x;
         assert forall z :: z in tset(r.left) ==> z > x;
         node(node(l, x, r.left.left), r.left.key, node(r.left.right, r.key, r.right))
}				

