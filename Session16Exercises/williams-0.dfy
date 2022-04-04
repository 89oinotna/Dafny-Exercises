/*

    This is Williams minimum heap implemented as a class
    Specified and verified by Ricardo Peña, January 2019

*/
class Williams_heap {
    var v: array<int>;
    var next: nat;
    ghost var repr: set<object>;
    ghost var model: multiset<int>;

    // It replaces the usual Valid() predicate. It specifies that v[j..next) is a minHeap
    
    predicate isHeap (j:nat) 
    requires 0 <= j <= v.Length
    reads this, v
    {
        this in repr && v in repr &&
        0 <= next <= v.Length && 
        (forall i | 2*j+1 <= i < next :: v[(i-1)/2] <= v[i]) &&
        model == multiset(v[..next])
    }
    

    constructor (size: nat) 
    ensures isHeap(0) && v.Length == size && next == 0
    ensures fresh (repr)
    ensures model == multiset{}
    {
        v := new int [size];
        next := 0;
        repr := {this, v};
        model := multiset{};
    }

    function method min(): int
    reads this, v
    //reads repr
    requires isHeap(0)
    requires next > 0
    //ensures min() in model
    ensures forall i | 0<=i<next :: v[i] >= min() 
    {
        assert forall i | 0<=i <next :: isHeap(i);
        firstIsMin();
        
        //assert forall i | 0<i<next :: v[i] >= v[0];
        v[0]
    }

    lemma firstIsMin()
    requires isHeap(0)
    requires next > 0
    ensures forall i | 0<i< next :: v[i] >= v[0]
    {
        forall i | 0<i< next ensures v[i] >= v[0]{
            firstIsLessEqual(i);
        }
    }

    lemma firstIsLessEqual(j:nat)
    requires isHeap(0)
    requires 0 < j < next
    ensures v[j] >= v[0]
    //ensures forall i | 0<=i< next :: v[i] >= v[0]
    {
        if (0 == (j-1)/2){}
        else{
            firstIsLessEqual((j-1)/2);
        }
    }

    method insert (val: int)
    modifies this, v
    requires isHeap(0)
    requires next < v.Length
    modifies repr
    ensures isHeap(0) 
    ensures next == old(next) + 1
    ensures repr == old(repr) 
    //ensures v == old(v)
    ensures v.Length == old(v.Length)
    ensures model == old(model) + multiset{val}
    //ensures forall i | 0<=i<next :: v[i] >= min() 
    {
        v[next] := val; next := next + 1;
        model := model + multiset{val};
        assert model==multiset(v[..next]);
        float ();
    }

    method float()
    requires 0 < next <= v.Length
    requires this in repr && v in repr; // isHeap(0) does not hold here
    requires model==multiset(v[..next])
    requires forall i | 0 < i < next-1 :: v[(i-1)/2] <= v[i]
    modifies v //this, v (modifying this dafny doesnt know if im creating a new object for v)
    //ensures repr == old(repr)
    ensures isHeap(0)
    ensures model == old(model) == multiset(v[..next])
    {
        var j := next-1;
        while j > 0 && v[(j-1)/2] > v[j] 
            invariant model == old(model) == multiset(v[..next])
            invariant 0 <= j <= next-1 < v.Length
            invariant forall i | 0 < i < next :: i != j ==> v[(i-1)/2] <= v[i]
            invariant j > 0 && 2*j+1< next ==> v[(j-1)/2] <= v[2*j+1] 
            invariant j > 0 && 2*j+2< next ==> v[(j-1)/2] <= v[2*j+2]
        {
            v[(j-1)/2], v[j] := v[j], v[(j-1)/2];
            j := (j-1)/2;
        }
    }

    method deleteMin ()
    requires isHeap(0)
    requires 0 < next
    modifies repr
    //modifies this, v
    ensures isHeap(0) 
    ensures next == old(next) - 1
    ensures repr == old(repr)
    ensures model == old(model) - multiset{old(v[0])}
    {
        ghost var pre := v[0];
        assert pre in model;

        
        v[0] := v[next-1]; 
        next := next - 1;
        model := model - multiset{pre};
        assert model == multiset(v[..next]);
        sink (0, next);
    }

    // It sinks v[s] in a heap ending in v[l-1]
    method sink(s:nat, l:nat)
    requires 0 <= s <= l == next <= v.Length
    requires this in repr && v in repr    // isHeap(0) does not hold here
    //requires next == 0 <==> model == multiset{}
    //requires forall i | 0 <= i < next :: v[i] in model
    requires model == multiset(v[..next])
    requires forall i | 0 < i < next :: (i-1)/2 != s ==> v[(i-1)/2] <= v[i]
    modifies v
    ensures repr == old(repr)
    ensures isHeap(s)
    ensures model == old(model) == multiset(v[..next])
    {
        //assert next == 0 ==> model == multiset([]);
        var j := s;
        while 2*j+1 < l 
            //invariant forall i | 0 <= i < next :: v[i] in model
            invariant model == old(model) == multiset(v[..next])
            //invariant model == old(model)
            invariant forall k | 2*s+1 <= k < l :: (k-1)/2 != j ==> v[(k-1)/2] <= v[k]
            invariant j >= 2*s+1 && 2*j+1< l ==> v[(j-1)/2] <= v[2*j+1] 
            invariant j >= 2*s+1 && 2*j+2< l ==> v[(j-1)/2] <= v[2*j+2]
        {
            var m: nat;
            if 2*j+2 < l && v[2*j+2] <= v[2*j+1] {
                m := 2*j+2;         // right son is smaller
            } else {
                m := 2*j+1;     // left son is smaller
            }				 		
            if v[j] > v[m] {
                v[j], v[m] := v[m], v[j];
                j  := m; 
            } else {   
                break;
            }								
        }
    }
}

predicate sorted_seg(a:array<int>, i:int, j:int) //j not included
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}


method heapsort_with_extra_space (a: array<int>)
modifies a
ensures sorted_seg(a, 0, a.Length)
{
    var queue := new Williams_heap(a.Length);
    var i := 0;
    while i < a.Length 
        invariant queue.isHeap(0) 
        invariant a.Length == queue.v.Length
        invariant i == queue.next <= queue.v.Length 
        invariant fresh(queue.repr)
    {
        queue.insert(a[i]);
        i := i + 1;
    }
    i := 0;
    while i < a.Length 
        invariant 0<=i<=a.Length
        invariant sorted_seg(a, 0, i)
        invariant forall j, k | 0<=j<i && k in queue.model :: a[j] <= k
        invariant queue.isHeap(0) 
        invariant queue.next == a.Length - i
        invariant fresh(queue.repr)
    {
        assert queue.isHeap(0); 
        assert queue.next > 0;
        queue.firstIsMin();
        assert forall j | 0<j<queue.next ::queue.min()<=queue.v[j];
        assert forall j, k | 0<=j<i && k in queue.model :: a[j] <= k;
        a[i] := queue.min(); 
        assert a[i] in queue.model;
        assert forall j | 0<=j<i :: a[j] <= a[i];
        queue.deleteMin();
        i := i + 1;
    }

/*

   Exercise: add an observable  model function or model ghost field to the class, 
   write suitable postconditions in terms of the observable model, and prove 
   that array 'a' becomes sorted at the end of the second while loop
   
*/
}
