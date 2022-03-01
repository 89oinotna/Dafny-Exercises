predicate sorted_seg(a:seq<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= |a|
//reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}



method mpartition2(v:array<int>, c:int, f:int, e:int) returns (p:int,q:int)
 modifies v
 requires 0<=c<=f<=v.Length-1 //There is at least one element
 requires e in v[c..f+1] 
 ensures c<=p<=q<=f 
 ensures (forall u::c<=u<p ==> v[u]<e)   && 
         (forall u::p<=u<=q ==> v[u]==e) &&
         (forall w::q+1<=w<=f ==> v[w]>e)
 ensures multiset(v[c..f+1])==multiset(old(v[c..f+1]))
 ensures v[..c]==old(v[..c])
 ensures v[f+1..]==old(v[f+1..])
 //Implement and verify



//Verify quicksort
method {:timeLimitMultiplier 2} quicksort (a:array<int>, c:int, f:int)//c and f included
modifies a 
requires 0 <= c <= f+1 <= a.Length //when c==f+1 empty sequence
ensures sorted_seg(a[..],c,f) 
ensures multiset(a[c..f+1]) == old(multiset(a[c..f+1]))
ensures a[..c]==old(a[..c])
ensures a[f+1..]==old(a[f+1..])
decreases f-c
{
    if (c < f) {
       var p,q := mpartition2(a,c,f,a[c]);
              ghost var a1 := a[..] ; 
            
       quicksort(a,c,p-1);
 
             ghost var a2 := a[..] ; 
            
       quicksort(a,q+1,f);
    }
}

 

